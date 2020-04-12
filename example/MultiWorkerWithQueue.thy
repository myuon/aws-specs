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
  process :: "'val list"

record 'val State =
  workers :: "nat \<rightharpoonup> 'val WorkerState"
  accepted :: "'val set"

datatype ('proc, 'msg) Event
  = Sent 'proc 'msg
  | WorkerStep

fun valid_event :: "(Node, 'val Message) Event \<Rightarrow> Node \<Rightarrow> (Node \<times> 'val Message) set \<Rightarrow> bool" where
  "valid_event (Sent sender msg) (Worker _) msgs = ((sender, msg) \<in> msgs)"
| "valid_event WorkerStep _ _ = True"
| "valid_event _ _ _ = False"

type_synonym 'val StepFunction = "Node \<Rightarrow> 'val State \<Rightarrow> (Node, 'val Message) Event \<Rightarrow> ('val State \<times> 'val Message set)" 

fun worker_step :: "'val WorkerState \<Rightarrow> (Node, 'val Message) Event \<Rightarrow> ('val WorkerState \<times> 'val Message set)" where
  "worker_step st WorkerStep = (st \<lparr> process := tl (process st) \<rparr>, {Accept (hd (process st))})"
| "worker_step st (Sent _ (SQSResponse (Returned xs))) = (st \<lparr> process := map snd xs \<rparr>, {})"
| "worker_step st _ = (st, {})"

fun step :: "'val StepFunction" where
  "step (Worker proc) st (Sent target msg) =
    (if Worker proc = target then (let (w, ms) = worker_step (the (workers st proc)) (Sent target msg) in (st \<lparr> workers := workers st (proc \<mapsto> w) \<rparr>, ms)) else (st, {}))
  "
| "step Acceptor st (Sent _ (Accept val)) = (st \<lparr> accepted := accepted st \<union> {val} \<rparr>, {})"
| "step _ st _ = (st, {})"

inductive execute_step where
  exec_step: "\<lbrakk> valid_event event proc msgs;
    step' proc st event = (st', ns);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> (\<lambda>msg. (proc,msg)) ` ns
  \<rbrakk> \<Longrightarrow> execute_step step' (st,events,msgs) (st',events',msgs')"

definition execute where
  "execute step' \<equiv> rtranclp (execute_step step')"

type_synonym 'val world = "'val State \<times> (Node \<times> (Node, 'val Message) Event) list \<times> (Node \<times> 'val Message) set"

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
    assume "(if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Sent x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) = (st', ns)"
      and "event = Sent x11 x12" "x \<in> accepted st"

    have "
       (if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Sent x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) =
       (st', ns) \<Longrightarrow>
       event = Sent x11 x12 \<Longrightarrow> x \<in> accepted st \<Longrightarrow> x \<in> accepted st'"
      apply (cases x11)
      apply auto
    proof-
      fix x1a
      show "(if x1 = x1a then let (w, y) = worker_step (the (workers st x1)) (Sent (Worker x1a) x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) =
           (st', ns) \<Longrightarrow>
           event = Sent (Worker x1a) x12 \<Longrightarrow> x \<in> accepted st \<Longrightarrow> x11 = Worker x1a \<Longrightarrow> x \<in> accepted st'"
        apply (cases "x1 = x1a")
        apply auto
        apply (cases "worker_step (the (workers st x1a)) (Sent (Worker x1a) x12)")
        apply auto
        done
    qed

    show "x \<in> accepted st'"
      by (simp add: \<open>(if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Sent x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) = (st', ns)\<close> \<open>\<lbrakk>(if Worker x1 = x11 then let (w, y) = worker_step (the (workers st x1)) (Sent x11 x12) in (st\<lparr>workers := workers st(x1 \<mapsto> w)\<rparr>, y) else (st, {})) = (st', ns); event = Sent x11 x12; x \<in> accepted st\<rbrakk> \<Longrightarrow> x \<in> accepted st'\<close> \<open>event = Sent x11 x12\<close> \<open>x \<in> accepted st\<close>)
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
    show "step Acceptor st (Sent x11 x12) = (st', ns) \<Longrightarrow> proc = Acceptor \<Longrightarrow> x \<in> accepted st \<Longrightarrow> event = Sent x11 x12 \<Longrightarrow> x \<in> accepted st'"
      apply (cases x12)
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

end
