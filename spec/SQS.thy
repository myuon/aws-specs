theory SQS
  imports Main
begin

datatype MessageId = MessageId nat
datatype ClientId = ClientId nat

record 'a SQSState =
  messages :: "(MessageId \<times> 'a) list"
  messageIdCounter :: nat

(* A queue in SQS is supposed to be used from multiple clients.

  - Send: a new data will be sent from a client to the queue
  - Receive: a client requests the queue to receive data, specifying the number of messages it expects
  - ReceiveResponse: the queue returns requested data to the client
  - Delete: a client requests the queue to delete the specified message
*)
datatype 'a SQSRequestPayload
  = Send 'a
  | Receive nat
  | Delete MessageId

datatype 'a SQSRequest = SQSRequest ClientId "'a SQSRequestPayload"

fun getRequestPayload where
  "getRequestPayload (SQSRequest _ p) = p"

datatype 'a SQSResponsePayload
  = Returned "(MessageId \<times> 'a) list"

datatype 'a SQSResponse = SQSResponse ClientId "'a SQSResponsePayload"

definition initialSQSState :: "'a SQSState" where
  "initialSQSState = \<lparr> messages = [], messageIdCounter = 0 \<rparr>"

fun SQS_step :: "'a SQSState \<Rightarrow> 'a SQSRequest \<Rightarrow> 'a SQSState \<times> ('a SQSResponse) option" where
  "SQS_step st (SQSRequest c (Send v)) = (st \<lparr> messages := messages st @ [(MessageId (messageIdCounter st), v)], messageIdCounter := Suc (messageIdCounter st) \<rparr>, None)"
| "SQS_step st (SQSRequest c (Receive n)) = (st, Some (SQSResponse c (Returned (take n (messages st)))))"
| "SQS_step st (SQSRequest c (Delete mid)) = (st \<lparr> messages := filter (\<lambda>(m,_). m \<noteq> mid) (messages st) \<rparr>, None)"

fun steps :: "('s \<Rightarrow> 'q \<Rightarrow> 's \<times> 'p option) \<Rightarrow> 's \<Rightarrow> 'q list \<Rightarrow> 's \<times> 'p list" where
  "steps f s0 [] = (s0, [])"
| "steps f s (q#qs) = (let (s',p') = f s q in let (s'',ps) = steps f s' qs in (s'', case p' of None \<Rightarrow> ps | Some(p) \<Rightarrow> p # ps))"

lemma steps_cons_destruct[elim]:
  fixes s :: "'a SQSState"
  assumes "steps f s (q#qs) = (s',ps)"
  obtains s'' p' ps' where "(s'',p') = f s q" "(s',ps') = steps f s'' qs" "ps = (case p' of None \<Rightarrow> ps' | Some(p) \<Rightarrow> p # ps')"
  using assms
  apply (cases "f s q")
  apply simp
proof-
  fix a :: "'a SQSState" and b
  assume hyp: "(\<And>s'' p' ps'. s'' = a \<and> p' = b \<Longrightarrow> (s', ps') = steps f a qs \<Longrightarrow> ps = (case b of None \<Rightarrow> ps' | Some p \<Rightarrow> p # ps') \<Longrightarrow> thesis)"
    and t: "(case steps f a qs of (s'', ps) \<Rightarrow> (s'', case b of None \<Rightarrow> ps | Some p \<Rightarrow> p # ps)) = (s', ps)"
    and s: "f s q = (a, b)"

  have "fst (steps f a qs) = s'"
    by (metis (no_types, lifting) case_prod_beta fst_conv t)
  have "ps = (case b of None \<Rightarrow> snd (steps f a qs) | Some p \<Rightarrow> p # snd (steps f a qs))"
    using t
    apply (cases "steps f a qs")
    using sndI by fastforce

  show thesis
    apply (rule hyp [of a b "snd (steps f a qs)"])
    apply simp
    using \<open>fst (steps f a qs) = s'\<close> apply auto[1]
    by (simp add: \<open>ps = (case b of None \<Rightarrow> snd (steps f a qs) | Some p \<Rightarrow> p # snd (steps f a qs))\<close>)
qed

lemma "steps SQS_step initialSQSState [] = (initialSQSState, [])"
  by simp

lemma "steps SQS_step (initialSQSState :: nat SQSState) [
  SQSRequest (ClientId 0) (Send 10),
  SQSRequest (ClientId 0) (Send 5),
  SQSRequest (ClientId 0) (Send 1),
  SQSRequest (ClientId 0) (Receive 3),
  SQSRequest (ClientId 0) (Delete (MessageId 0))] =
  (\<lparr> messages = [(MessageId 1, 5), (MessageId 2, 1)], messageIdCounter = 3 \<rparr> :: nat SQSState,
  [SQSResponse (ClientId 0) (Returned [(MessageId 0, 10), (MessageId 1, 5), (MessageId 2, 1)])])"
  by (simp add: initialSQSState_def)

inductive SQS_execute where
  SQS_execute_empty: "SQS_execute st [] st []"
| SQS_execute_step: "\<lbrakk> SQS_step st q = (st', p); SQS_execute st' qs st'' ps \<rbrakk> \<Longrightarrow> SQS_execute st (q#qs) st'' (case p of None \<Rightarrow> ps | Some(p) \<Rightarrow> p # ps)"

lemma SQS_steps_to_execute:
  fixes st :: "'a SQSState"
  shows "(st',ps) = steps SQS_step st qs \<Longrightarrow> SQS_execute st qs st' ps"
  apply (induct qs arbitrary: st st' ps)
  apply (simp, rule)
proof-
  fix a qs and st :: "'a SQSState" and st' ps
  assume "(\<And>st st' ps. (st', ps) = steps SQS_step st qs \<Longrightarrow> SQS_execute st qs st' ps)"
    and "(st', ps) = steps SQS_step st (a # qs)"
  obtain s'' p' ps' where q: "(s'',p') = SQS_step st a" "(st',ps') = steps SQS_step s'' qs" "ps = (case p' of None \<Rightarrow> ps' | Some(p) \<Rightarrow> p # ps')"
    by (metis \<open>(st', ps) = steps SQS_step st (a # qs)\<close> steps_cons_destruct)

  show "SQS_execute st (a # qs) st' ps"
    apply (simp add: q(3))
    apply rule
    apply (simp add: q(1) [symmetric])
    by (simp add: \<open>\<And>st' st ps. (st', ps) = steps SQS_step st qs \<Longrightarrow> SQS_execute st qs st' ps\<close> q(2))
qed

lemma SQS_execute_to_steps:
  fixes st :: "'a SQSState"
  shows "SQS_execute st qs st' ps \<Longrightarrow> steps SQS_step st qs = (st',ps)"
  apply (induct rule: SQS_execute.induct)
  apply simp
  apply simp
  done

theorem SQS_execute_iff_steps:
  fixes st :: "'a SQSState"
  shows "SQS_execute st qs st' ps = (steps SQS_step st qs = (st',ps))"
  using SQS_execute_to_steps SQS_steps_to_execute by force

lemma
  assumes "SQS_execute st [m] st' ps" and "getRequestPayload m = Send v"
  obtains mid where "messages st' = messages st @ [(mid, v)]" "mid = MessageId (messageIdCounter st)"
proof-
  have "steps SQS_step st [m] = (st',ps)"
    using assms
    using SQS_execute_to_steps by blast
  hence "messages st' = messages st @ [(MessageId (messageIdCounter st), v)]"
    apply (simp)
    apply (cases "SQS_step st m")
    apply simp
    using assms(2)
    apply (cases m)
    apply auto
    done

  assume "(\<And>mid. messages st' = messages st @ [(mid, v)] \<Longrightarrow> mid = MessageId (messageIdCounter st) \<Longrightarrow> thesis)"
  show thesis
    using \<open>messages st' = messages st @ [(MessageId (messageIdCounter st), v)]\<close> that by blast
qed

end
