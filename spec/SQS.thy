theory SQS
  imports Main "./Queue"
begin

datatype ClientId = ClientId nat

datatype 'a SQSRequest
  = Send 'a
  | Receive nat
  | Delete MessageId

datatype 'a SQSResponse
  = Returned "(MessageId \<times> 'a) list"

record 'a SQSState =
  queue :: "'a Queue"
  request :: "('a SQSRequest) option"
  response :: "('a SQSResponse) option"

definition initialSQSState :: "'a SQSState" where
  "initialSQSState = \<lparr> queue = Queue.empty, request = None, response = None \<rparr>"

fun SQS_step :: "'a SQSState \<Rightarrow> 'a SQSState" where
  "SQS_step st = (case request st of
    Some (Send v) \<Rightarrow> st \<lparr> queue := insert (queue st) v, response := None \<rparr>
  | Some (Receive n) \<Rightarrow> st \<lparr> response := Some (Returned (pick (queue st) n)) \<rparr>
  | Some (Delete m) \<Rightarrow> st \<lparr> queue := delete (queue st) m, response := None \<rparr>
  ) \<lparr> request := None \<rparr>"

end
