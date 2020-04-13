theory SQS
  imports Main "./Queue"
begin

datatype 'a SQSRequest
  = Send 'a
  | Receive nat
  | Delete MessageId

datatype 'a SQSResponse
  = Returned "(MessageId \<times> 'a) list"

record ('proc, 'a) SQSState =
  queue :: "'a Queue"
  request :: "('proc \<times> 'a SQSRequest) option"
  response :: "('proc \<times> 'a SQSResponse) option"

definition initialSQSState :: "('proc, 'a) SQSState" where
  "initialSQSState = \<lparr> queue = Queue.empty, request = None, response = None \<rparr>"

fun SQS_step :: "('proc, 'a) SQSState \<Rightarrow> ('proc, 'a) SQSState" where
  "SQS_step st = (case request st of
    Some ((_, Send v)) \<Rightarrow> st \<lparr> queue := insert (queue st) v, response := None \<rparr>
  | Some ((proc, Receive n)) \<Rightarrow> st \<lparr> response := Some ((proc, Returned (pick (queue st) n))) \<rparr>
  | Some ((_, Delete m)) \<Rightarrow> st \<lparr> queue := delete (queue st) m, response := None \<rparr>
  | _ \<Rightarrow> st
  ) \<lparr> request := None \<rparr>"

end
