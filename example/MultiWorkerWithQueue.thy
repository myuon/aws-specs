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

inductive execute :: "'val StepFunction \<Rightarrow> 'val State \<Rightarrow> (Node \<times> (Node, 'val Message) Event) list \<Rightarrow> (Node \<times> 'val Message) set \<Rightarrow> bool" where
  exec_empty: "execute step st [] {}"
| exec_step: "\<lbrakk> execute step st events msgs;
    valid_event event proc msgs;
    step proc st event = (st', ns);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> (\<lambda>msg. (proc, msg)) ` ns
  \<rbrakk> \<Longrightarrow> execute step st' events' msgs'"

end
