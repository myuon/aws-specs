theory MultiWorkerWithQueue
  imports Main "../spec/SQS"
begin

datatype Node
  = Worker nat
  | Queue
  | Acceptor

datatype 'val Message
  = SQSRequest "'val SQSRequest"
  | SQSResponse "'val SQSResponse"
  | Accept 'val

record 'val WorkerState =
  alive :: bool
  process :: "(MessageId \<times> 'val) list"

record 'val State =
  workers :: "nat \<rightharpoonup> 'val WorkerState"
  accepted :: "'val set"
  queue :: "(Node, 'val) SQSState"

datatype ('proc,'msg) Send = Send (msg_recipient: 'proc) (send_payload: 'msg)

datatype 'msg Event
  = Received (msg_sender: Node) (received_message: 'msg)
  | WorkerStep
  | QueueStep

fun valid_event :: "(Node, 'val Message) Send Event \<Rightarrow> Node \<Rightarrow> (Node \<times> (Node, 'val Message) Send) set \<Rightarrow> bool" where
  "valid_event (Received sender (Send recp msg)) (Worker w) msgs = ((recp = Worker w) \<and> ((sender, (Send recp msg)) \<in> msgs))"
| "valid_event WorkerStep _ _ = True"
| "valid_event _ _ _ = False"

type_synonym ('st, 'val) StepStateFunction = "'st \<Rightarrow> (Node, 'val Message) Send Event \<Rightarrow> ('st \<times> (Node, 'val Message) Send set)" 
type_synonym 'val StepFunction = "Node \<Rightarrow> ('val State, 'val) StepStateFunction"

fun worker_step :: "('val WorkerState, 'val) StepStateFunction" where
  "worker_step st WorkerStep = (st \<lparr> process := tl (process st) \<rparr>, {Send Acceptor (Accept (snd (hd (process st)))), Send Queue (SQSRequest (Delete (fst (hd (process st)))))})"
| "worker_step st (Received _ (Send _ (SQSResponse (Returned xs)))) = (st \<lparr> process := xs \<rparr>, {})"
| "worker_step st _ = (st, {})"

fun queue_step :: "((Node, 'val) SQSState, 'val) StepStateFunction" where
  "queue_step st (Received proc (Send _ (SQSRequest req))) = (st \<lparr> request := Some (proc,req) \<rparr>, {})"
| "queue_step st QueueStep = (let st' = SQS_step st in (st', case response st' of None \<Rightarrow> {} | Some (proc,resp) \<Rightarrow> {Send proc (SQSResponse resp)}))"
| "queue_step st _ = (st, {})"

fun step :: "'val StepFunction" where
  "step (Worker proc) st (Received target msg) =
    (if Worker proc = target then (let (w, ms) = worker_step (the (workers st proc)) (Received target msg) in (st \<lparr> workers := workers st (proc \<mapsto> w) \<rparr>, ms)) else (st, {}))
  "
| "step Acceptor st (Received _ (Send _ (Accept val))) = (st \<lparr> accepted := accepted st \<union> {val} \<rparr>, {})"
| "step _ st _ = (st, {})"

type_synonym 'val world = "'val State \<times> (Node \<times> (Node, 'val Message) Send Event) list \<times> (Node \<times> (Node, 'val Message) Send) set"

inductive execute_step :: "'val StepFunction \<Rightarrow> 'val world \<Rightarrow> 'val world \<Rightarrow> bool" where
  exec_step: "\<lbrakk> valid_event event proc msgs;
    step' proc st event = (st', ns);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> (\<lambda>msg. (proc,msg)) ` ns
  \<rbrakk> \<Longrightarrow> execute_step step' (st,events,msgs) (st',events',msgs')"

definition execute where
  "execute step' \<equiv> rtranclp (execute_step step')"

inductive execute_traced :: "'val StepFunction \<Rightarrow> 'val world \<Rightarrow> 'val world \<Rightarrow> 'val world list \<Rightarrow> bool" where
  execute_traced_empty: "execute_traced step' w w []"
| execute_traced_cons: "\<lbrakk> execute_traced step' w1 w2 path; execute_step step' w2 w3 \<rbrakk> \<Longrightarrow> execute_traced step' w1 w3 (path @ [w2])"

lemma execute_induct: "execute step' w w' \<Longrightarrow> (\<And>w. P w w) \<Longrightarrow> (\<And>w1 w2 w3. execute step' w1 w2 \<Longrightarrow> P w1 w2 \<Longrightarrow> execute_step step' w2 w3 \<Longrightarrow> P w1 w3) \<Longrightarrow> P w w'"
  apply (simp add: execute_def)
  apply (erule rtranclp_induct)
   apply auto
  done

lemma execute_imps_trace:
  assumes "execute step' w w'"
  obtains path where "execute_traced step' w w' path"
  apply (induct rule: execute_induct)
  apply (rule assms)
  using execute_traced_empty apply blast
  using execute_traced_cons by blast

lemma trace_imps_execute:
  assumes "execute_traced step' w w' path"
  shows "execute step' w w'"
  apply (rule execute_traced.induct)
  apply (rule assms)
  apply (simp add: execute_def)
  by (simp add: execute_def)

lemma execute_traced_coherence_0: "\<lbrakk> execute_traced step w w' path; length path = 0 \<rbrakk> \<Longrightarrow> w = w'"
  apply (induct rule: execute_traced.induct)
  apply simp
  apply simp
  done

lemma execute_traced_coherence_Suc:
  assumes "execute_traced step w w' path" "length path = Suc n"
  obtains w0 path' where "path = path' @ [w0]" "execute_traced step w w0 path'" "execute_step step w0 w'" "length path' = n"
  using assms
  apply (induct arbitrary: rule: execute_traced.induct)
  apply simp
  apply simp
  done

lemma step_accepted_monotonic: "step proc st event = (st',ns) \<Longrightarrow> accepted st \<subseteq> accepted st'"
  apply (cases proc)
  apply auto
proof-
  fix x1 x
  assume hyp: "step (Worker x1) st event = (st', ns)" "proc = Worker x1" "x \<in> accepted st"
  have "step (Worker x1) st event = (st',ns) \<Longrightarrow> accepted st \<subseteq> accepted st'"
    apply (cases event)
    apply auto
  proof-
    fix x11 x12 x
    assume "(if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Received x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) = (st', ns)"
      and "event = Received x11 x12" "x \<in> accepted st"

    have "
       (if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Received x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) =
       (st', ns) \<Longrightarrow>
       event = Received x11 x12 \<Longrightarrow> x \<in> accepted st \<Longrightarrow> x \<in> accepted st'"
      apply (cases x11)
      apply auto
    proof-
      fix x1a
      show "(if x1 = x1a then let (w, y) = worker_step (the (workers st x1)) (Received (Worker x1a) x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) =
           (st', ns) \<Longrightarrow>
           event = Received (Worker x1a) x12 \<Longrightarrow> x \<in> accepted st \<Longrightarrow> x11 = Worker x1a \<Longrightarrow> x \<in> accepted st'"
        apply (cases "x1 = x1a")
        apply auto
        apply (cases "worker_step (the (workers st x1a)) (Received (Worker x1a) x12)")
        apply auto
        done
    qed

    show "x \<in> accepted st'"
      by (simp add: \<open>(if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Received x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) = (st', ns)\<close> \<open>\<lbrakk>(if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Received x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) = (st', ns); event = Received x11 x12; x \<in> accepted st\<rbrakk> \<Longrightarrow> x \<in> accepted st'\<close> \<open>event = Received x11 x12\<close> \<open>x \<in> accepted st\<close>)
  qed

  show "x \<in> accepted st'"
    using \<open>step (Worker x1) st event = (st', ns) \<Longrightarrow> accepted st \<subseteq> accepted st'\<close> hyp(1) hyp(3) by blast
next
  fix x
  show "step Acceptor st event = (st', ns) \<Longrightarrow> proc = Acceptor \<Longrightarrow> x \<in> accepted st \<Longrightarrow> x \<in> accepted st'"
    apply (cases event)
    apply auto
  proof-
    fix x11 x12
    show "step Acceptor st (Received x11 x12) = (st', ns) \<Longrightarrow> proc = Acceptor \<Longrightarrow> x \<in> accepted st \<Longrightarrow> event = Received x11 x12 \<Longrightarrow> x \<in> accepted st'"
      apply (cases x12)
      apply (cases "send_payload x12")
      apply auto
      done
  qed
qed

lemma accepted_step_monotonic: "execute_step step (st,events,msgs) (st',events',msgs') \<Longrightarrow> accepted st \<subseteq> accepted st'"
proof-
  assume hyp: "execute_step step (st,events,msgs) (st',events',msgs')"
  obtain proc event ns where
    "valid_event event proc msgs"
    "step proc st event = (st',ns)"
    "events' = events @ [(proc,event)]"
    "msgs' = msgs \<union> (\<lambda>msg. (proc,msg)) ` ns"
    apply (rule execute_step.cases [OF hyp])
    by blast
  show ?thesis
    using \<open>step proc st event = (st', ns)\<close> step_accepted_monotonic by blast
qed

lemma accepted_monotonic: "execute step (st :: 'val State,events,msgs) (st',events',msgs') \<Longrightarrow> accepted st \<subseteq> accepted st'"
proof-
  assume "execute step (st,events,msgs) (st',events',msgs')"
  obtain path :: "'val world list" where "execute_traced step (st,events,msgs) (st',events',msgs') path"
    using \<open>execute step (st, events, msgs) (st', events', msgs')\<close> execute_imps_trace by blast
  {
    fix n :: nat
    have "\<lbrakk> length (path :: 'val world list) = n; execute_traced step (st :: 'val State,events,msgs) (st',events',msgs') path \<rbrakk> \<Longrightarrow> accepted st \<subseteq> accepted st'"
      apply (induct n arbitrary: path st events msgs st' events' msgs')
      using execute_traced_coherence_0 apply blast
    proof-
      fix n :: nat and path :: "'val world list" and st :: "'val State" and events msgs st' events' msgs'
      assume hyp: "(\<And>(path :: 'val world list) st events msgs st' events' msgs'. length path = n \<Longrightarrow> execute_traced step (st, events, msgs) (st', events', msgs') path \<Longrightarrow> accepted st \<subseteq> accepted st')"
        and "length path = Suc n" "execute_traced step (st, events, msgs) (st', events', msgs') path"
      obtain w0 and path' :: "'val world list" where "path = path' @ [w0]" "execute_traced step (st,events,msgs) w0 path'" "execute_step step w0 (st',events',msgs')" "length path' = n"
        using \<open>execute_traced step (st, events, msgs) (st', events', msgs') path\<close> \<open>length path = Suc n\<close> execute_traced_coherence_Suc by blast
      obtain st'' events'' msgs'' where "w0 = (st'',events'',msgs'')"
        using prod_cases3 by blast
      have "accepted st \<subseteq> accepted st''"
        using \<open>execute_traced step (st, events, msgs) w0 path'\<close> \<open>length path' = n\<close> \<open>w0 = (st'', events'', msgs'')\<close> hyp by auto
      moreover have "accepted st'' \<subseteq> accepted st'"
        using \<open>execute_step step w0 (st', events', msgs')\<close> \<open>w0 = (st'', events'', msgs'')\<close> accepted_step_monotonic by blast
      ultimately show "accepted st \<subseteq> accepted st'"
        by simp
    qed
  }
  thus ?thesis
    using \<open>execute_traced step (st, events, msgs) (st', events', msgs') path\<close> by blast
qed

definition initialState :: "nat \<Rightarrow> 'val State" where
  "initialState W \<equiv> \<lparr> workers = map_of (map (\<lambda>i. (i, \<lparr> alive = True, process = [] \<rparr>)) (map nat [0..int W])), accepted = {}, queue = initialSQSState \<rparr>"

definition initialWorld :: "nat \<Rightarrow> 'val world" where
  "initialWorld W \<equiv> (initialState W, [], {})"

lemma worker_step_wont_change_accepted:
  "step (Worker w) st event = (st',ns) \<Longrightarrow> accepted st' = accepted st"
  apply (cases event)
  apply simp_all
proof-
  fix x11 x12
  show "(if Worker w = x11 then let (wa, y) = worker_step (the (workers st w)) (Received x11 x12) in (st\<lparr>workers := workers st(w \<mapsto> wa)\<rparr>, y) else (st, {})) =
       (st', ns) \<Longrightarrow>
       event = Received x11 x12 \<Longrightarrow> accepted st' = accepted st"
    apply (cases "Worker w = x11")
    apply simp_all
    apply (cases "worker_step (the (workers st w)) (Received x11 x12)")
    apply simp
    apply (cases st, cases st')
    apply simp
    done
qed

lemma step_accepted_change_onlyif:
  assumes "step proc st event = (st', ns)" "val \<in> accepted st' - accepted st"
  obtains r s val where "event = Received r (Send s (Accept val))"
  using assms
  apply (cases event)
  apply simp_all
  apply (cases proc)
  apply simp_all
  using assms(1) worker_step_wont_change_accepted apply blast
  by (metis Message.exhaust Send.exhaust prod.inject step.simps(4) step.simps(5))

lemma execute_step_accepted_change_onlyif:
  assumes "execute_step step (st,events,msgs) (st',events',msgs')" "val \<in> accepted st' - accepted st"
  obtains p r s where "events' = event @ [(p, Received r (Send s (Accept val)))]"
  using assms
  apply (cases rule: execute_step.cases)
  by (metis DiffD1 DiffD2 Event.simps(3) step_accepted_change_onlyif valid_event.elims(2) worker_step_wont_change_accepted)

lemma execute_step_backward_Accept:
  assumes "execute step (initialWorld W) (st',events',msgs')" "val \<in> accepted st'"
  obtains p r s where "(p, Received r (Send s (Accept val))) \<in> set events'"
proof-
  obtain path where "execute_traced step (initialWorld W) (st',events',msgs') path"
    using assms(1) execute_imps_trace by blast
  { fix n
    have "\<lbrakk> length path = n; execute_traced step (initialWorld W) (st',events',msgs') path; val \<in> accepted st' \<rbrakk> \<Longrightarrow> \<exists>p r s. (p, Received r (Send s (Accept val))) \<in> set events'"
      apply (induct n arbitrary: path st' events' msgs')
    proof-
      fix path st' events' msgs'
      assume "length path = 0"
        and "execute_traced step (initialWorld W) (st',events',msgs') path"
        and "val \<in> accepted st'"
      have "(st',events',msgs') = initialWorld W"
        using \<open>execute_traced step (initialWorld W) (st', events', msgs') path\<close> \<open>length path = 0\<close> execute_traced_coherence_0 by fastforce
      hence "accepted st' = {}"
        by (simp add: initialWorld_def initialState_def)
      show "\<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set events'"
        using \<open>accepted st' = {}\<close> \<open>val \<in> accepted st'\<close> by blast
    next
      fix n path st' events' msgs'
      assume "(\<And>path st' events' msgs'.
           length path = n \<Longrightarrow>
           execute_traced step (initialWorld W) (st', events', msgs') path \<Longrightarrow>
           val \<in> accepted st' \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set events')"
        and "length path = Suc n" "execute_traced step (initialWorld W) (st', events', msgs') path" "val \<in> accepted st'"
      obtain w' path' where "path = path' @ [w']" "length path' = n" "execute_traced step (initialWorld W) w' path'" "execute_step step w' (st',events',msgs')"
        using \<open>execute_traced step (initialWorld W) (st', events', msgs') path\<close> \<open>length path = Suc n\<close> execute_traced_coherence_Suc by blast
      obtain st events msgs where "w' = (st,events,msgs)"
        using prod_cases3 by blast
      have "accepted st \<subseteq> accepted st'"
        using \<open>execute_step step w' (st', events', msgs')\<close> \<open>w' = (st, events, msgs)\<close> accepted_step_monotonic by blast
      have "val \<in> accepted st \<or> val \<in> accepted st' - accepted st"
        using \<open>val \<in> accepted st'\<close> by blast
      moreover have "val \<in> accepted st \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set events'"
        using \<open>\<And>st' path msgs' events'. \<lbrakk>length path = n; execute_traced step (initialWorld W) (st', events', msgs') path; val \<in> accepted st'\<rbrakk> \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set events'\<close> \<open>execute_traced step (initialWorld W) w' path'\<close> \<open>length path' = n\<close> \<open>w' = (st, events, msgs)\<close> by blast
      moreover have "val \<in> accepted st' - accepted st \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set events'"
      proof-
        assume "val \<in> accepted st' - accepted st"
        have "execute_step step (st,events,msgs) (st',events',msgs')"
          using \<open>execute_step step w' (st', events', msgs')\<close> \<open>w' = (st, events, msgs)\<close> by blast
        obtain p r s where "events' = events @ [(p, Received r (Send s (Accept val)))]"
          by (meson \<open>execute_step step (st, events, msgs) (st', events', msgs')\<close> \<open>val \<in> accepted st' - accepted st\<close> execute_step_accepted_change_onlyif)
        show ?thesis
          using \<open>events' = events @ [(p, Received r (Send.Send s (Accept val)))]\<close> by auto
      qed
      ultimately show "\<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set events'"
        by blast
    qed
  }
  thus ?thesis
    using \<open>execute_traced step (initialWorld W) (st', events', msgs') path\<close> assms(2) that by auto
qed

theorem liveness:
  assumes "execute step (initialWorld W) w"
  obtains w' where "execute step w w'" "ran (messages (SQS.queue (queue ((\<lambda>(a,b,c). a) w')))) = {}" "accepted ((\<lambda>(a,b,c). a) w') = {0..W}"
  sorry

end
