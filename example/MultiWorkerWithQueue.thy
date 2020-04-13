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
  "valid_event (Received sender msg) _ msgs = ((sender, msg) \<in> msgs)"
| "valid_event WorkerStep _ _ = True"
| "valid_event _ _ _ = False"

type_synonym ('st, 'val) StepStateFunction = "'st \<Rightarrow> (Node, 'val Message) Send Event \<Rightarrow> ('st \<times> (Node, 'val Message) Send set)" 
type_synonym 'val StepFunction = "Node \<Rightarrow> ('val State, 'val) StepStateFunction"

fun worker_step :: "('val WorkerState, 'val) StepStateFunction" where
  "worker_step st WorkerStep = (if List.null (process st)
    then (st, {Send Queue (SQSRequest (Receive 10))})
    else (st \<lparr> process := tl (process st) \<rparr>, {Send Acceptor (Accept (snd (hd (process st)))), Send Queue (SQSRequest (Delete (fst (hd (process st)))))}))"
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

record 'val world =
  world_state :: "'val State"
  world_events :: "(Node \<times> (Node, 'val Message) Send Event) list"
  world_messages :: "(Node \<times> (Node, 'val Message) Send) set"

inductive execute_step :: "'val StepFunction \<Rightarrow> 'val world \<Rightarrow> 'val world \<Rightarrow> bool" where
  exec_step: "\<lbrakk> valid_event event proc msgs;
    step' proc st event = (st', ns);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> (\<lambda>msg. (proc,msg)) ` ns
  \<rbrakk> \<Longrightarrow> execute_step step' \<lparr> world_state = st, world_events = events, world_messages = msgs \<rparr> \<lparr> world_state = st', world_events = events', world_messages = msgs' \<rparr>"

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

lemma accepted_step_monotonic: "execute_step step w w' \<Longrightarrow> accepted (world_state w) \<subseteq> accepted (world_state w')"
  apply (erule execute_step.cases)
  apply simp
  using step_accepted_monotonic by blast

lemma accepted_monotonic:
  fixes w :: "'val world"
  shows "execute step w w' \<Longrightarrow> accepted (world_state w) \<subseteq> accepted (world_state w')"
proof-
  assume "execute step w w'"
  obtain path where "execute_traced step w w' path"
    using \<open>execute step w w'\<close> execute_imps_trace by blast
  {
    fix n :: nat
    have "\<lbrakk> length path = n; execute_traced step w w' path \<rbrakk> \<Longrightarrow> accepted (world_state w) \<subseteq> accepted (world_state w')"
      apply (induct n arbitrary: path w w')
      using execute_traced_coherence_0 apply blast
    proof-
      fix n :: nat and path :: "'val world list" and w w'
      assume hyp: "(\<And>(path :: 'val world list) w w'. length path = n \<Longrightarrow> execute_traced step w w' path \<Longrightarrow> accepted (world_state w) \<subseteq> accepted (world_state w'))"
        and "length path = Suc n" "execute_traced step w w' path"
      obtain w0 :: "'val world" and path' where "path = path' @ [w0]" "execute_traced step w w0 path'" "execute_step step w0 w'" "length path' = n"
        using \<open>execute_traced step w w' path\<close> \<open>length path = Suc n\<close> execute_traced_coherence_Suc by blast
      have "accepted (world_state w) \<subseteq> accepted (world_state w0)"
        using \<open>execute_traced step w w0 path'\<close> \<open>length path' = n\<close> hyp by auto
      moreover have "accepted (world_state w0) \<subseteq> accepted (world_state w')"
        by (simp add: \<open>execute_step step w0 w'\<close> accepted_step_monotonic)
      ultimately show "accepted (world_state w) \<subseteq> accepted (world_state w')"
        by simp
    qed
  }
  thus ?thesis
    using \<open>execute_traced step w w' path\<close> by blast
qed

definition initialState :: "nat \<Rightarrow> 'val State" where
  "initialState W \<equiv> \<lparr> workers = map_of (map (\<lambda>i. (i, \<lparr> alive = True, process = [] \<rparr>)) (map nat [0..int W])), accepted = {}, queue = initialSQSState \<rparr>"

definition initialWorld :: "nat \<Rightarrow> 'val world" where
  "initialWorld W \<equiv> \<lparr> world_state = initialState W, world_events = [], world_messages = {} \<rparr>"

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
  obtains r s where "event = Received r (Send s (Accept val))"
  using assms
  apply (cases event)
  apply simp_all
  apply (cases proc)
  apply simp_all
  using assms(1) worker_step_wont_change_accepted apply blast
proof-
  fix x11 x12
  show "(\<And>r s. x11 = r \<and> x12 = Send.Send s (Accept val) \<Longrightarrow> thesis) \<Longrightarrow>
       step Acceptor st (Received x11 x12) = (st', ns) \<Longrightarrow> val \<in> accepted st' \<and> val \<notin> accepted st \<Longrightarrow> event = Received x11 x12 \<Longrightarrow> proc = Acceptor \<Longrightarrow> thesis"
    apply (cases x12)
    apply (cases "send_payload x12")
    apply auto
    done
qed

lemma execute_step_accepted_change_onlyif:
  assumes "execute_step step w w'" "val \<in> accepted (world_state w') - accepted (world_state w)"
  obtains p r s where "world_events w' = world_events w @ [(p, Received r (Send s (Accept val)))]"
  using assms
  apply (cases rule: execute_step.cases)
  apply simp
  by (meson Diff_iff step_accepted_change_onlyif)

lemma execute_step_events_increasing_as_set:
  assumes "execute_step step w w'"
  shows "set (world_events w) \<subseteq> set (world_events w')"
  using assms
  apply (cases rule: execute_step.cases)
  apply auto
  done

lemma execute_step_backward_Accept:
  assumes "execute step (initialWorld W) w'" "val \<in> accepted (world_state w')"
  obtains p r s where "(p, Received r (Send s (Accept val))) \<in> set (world_events w')"
proof-
  obtain path where "execute_traced step (initialWorld W) w' path"
    using assms(1) execute_imps_trace by blast
  { fix n
    have "\<lbrakk> length path = n; execute_traced step (initialWorld W) w' path; val \<in> accepted (world_state w') \<rbrakk> \<Longrightarrow> \<exists>p r s. (p, Received r (Send s (Accept val))) \<in> set (world_events w')"
      apply (induct n arbitrary: path w')
    proof-
      fix path w'
      assume "length path = 0"
        and "execute_traced step (initialWorld W) w' path"
        and "val \<in> accepted (world_state w')"
      have "w' = initialWorld W"
        using \<open>execute_traced step (initialWorld W) w' path\<close> \<open>length path = 0\<close> execute_traced_coherence_0 by fastforce
      hence "accepted (world_state w') = {}"
        by (simp add: initialWorld_def initialState_def)
      show "\<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w')"
        using \<open>accepted (world_state w') = {}\<close> \<open>val \<in> accepted (world_state w')\<close> by blast
    next
      fix n path w'
      assume "(\<And>path w'.
           length path = n \<Longrightarrow>
           execute_traced step (initialWorld W) w' path \<Longrightarrow>
           val \<in> accepted (world_state w') \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w'))"
        and "length path = Suc n" "execute_traced step (initialWorld W) w' path" "val \<in> accepted (world_state w')"
      obtain w'' path' where "path = path' @ [w'']" "length path' = n" "execute_traced step (initialWorld W) w'' path'" "execute_step step w'' w'"
        using \<open>execute_traced step (initialWorld W) w' path\<close> \<open>length path = Suc n\<close> execute_traced_coherence_Suc by blast
      have "accepted (world_state w'') \<subseteq> accepted (world_state w')"
        using \<open>execute_step step w'' w'\<close> accepted_step_monotonic by blast
      have "val \<in> accepted (world_state w'') \<or> val \<in> accepted (world_state w') - accepted (world_state w'')"
        by (simp add: \<open>val \<in> accepted (world_state w')\<close>)
      moreover have "val \<in> accepted (world_state w'') \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w')"
      proof-
        have "val \<in> accepted (world_state w'') \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w'')"
          using \<open>\<And>w' path. \<lbrakk>length path = n; execute_traced step (initialWorld W) w' path; val \<in> accepted (world_state w')\<rbrakk> \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w')\<close> \<open>execute_traced step (initialWorld W) w'' path'\<close> \<open>length path' = n\<close> by blast
        moreover have "set (world_events w'') \<subseteq> set (world_events w')"
          using \<open>execute_step step w'' w'\<close> execute_step_events_increasing_as_set by blast
        ultimately show "val \<in> accepted (world_state w'') \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w')"
          by blast
      qed
      moreover have "val \<in> accepted (world_state w') - accepted (world_state w'') \<Longrightarrow> \<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w')"
      proof-
        assume "val \<in> accepted (world_state w') - accepted (world_state w'')"
        have "execute_step step w'' w'"
          by (simp add: \<open>execute_step step w'' w'\<close>)
        obtain p r s where "world_events w' = world_events w'' @ [(p, Received r (Send s (Accept val)))]"
          by (meson \<open>execute_step step w'' w'\<close> \<open>val \<in> accepted (world_state w') - accepted (world_state w'')\<close> execute_step_accepted_change_onlyif)
        show ?thesis
          using \<open>world_events w' = world_events w'' @ [(p, Received r (Send.Send s (Accept val)))]\<close> by auto
      qed
      ultimately show "\<exists>p r s. (p, Received r (Send.Send s (Accept val))) \<in> set (world_events w')"
        by blast
    qed
  }
  thus ?thesis
    using \<open>execute_traced step (initialWorld W) w' path\<close> assms(2) that by blast
qed

(*
lemma exists_consume_queue_tasks_execution:
  obtains w' df xs where
    "execute step w w'"
    "world_events w' = world_events w @ df"
    "map snd df = Received (Worker 0) (SQSRequest (Receive 1)) # Received Queue (Send (Worker 0) (SQSResponse (Returned xs))) # []"
*)

theorem liveness:
  assumes "execute step (initialWorld W) w"
  obtains w' where "execute step w w'" "ran (messages (SQS.queue (queue (world_state w')))) = {}" "accepted (world_state w') = {0..W}"
  sorry

end
