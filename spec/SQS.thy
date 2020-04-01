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

end
