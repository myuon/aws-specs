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

end
