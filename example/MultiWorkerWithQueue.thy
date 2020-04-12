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
  exec_empty: "execute step' st [] {}"
| exec_step: "\<lbrakk> execute step' st events msgs;
    valid_event event proc msgs;
    step' proc st event = (st', ns);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> (\<lambda>msg. (proc, msg)) ` ns
  \<rbrakk> \<Longrightarrow> execute step' st' events' msgs'"

inductive execute_step where
  exec_step: "\<lbrakk> valid_event event proc msgs;
    step' proc st event = (st', ns);
    events' = events @ [(proc, event)];
    msgs' = msgs \<union> (\<lambda>msg. (proc,msg)) ` ns
  \<rbrakk> \<Longrightarrow> execute_step step' (st,events,msgs) (st',events',msgs')"

definition execute_steps where
  "execute_steps step' \<equiv> rtranclp (execute_step step')"

type_synonym 'val world = "'val State \<times> (Node \<times> (Node, 'val Message) Event) list \<times> (Node \<times> 'val Message) set"

type_synonym 'val Predicate = "'val world \<Rightarrow> bool"
datatype 'val Prop
  = Atom "'val Predicate"
  | Not "'val Prop"
  | Or "'val Prop" "'val Prop"  (infix "[\<or>]" 40)
  | Next "'val Prop"  ("\<circle> _" [100] 80)
  | Until "'val Prop" "'val Prop"  (infix "[U]" 40)

definition And (infix "[\<and>]" 45) where
  "And p q = Not (Not p [\<or>] Not q)"

definition true where
  "true \<equiv> Atom (\<lambda>_. True)"

definition false where
  "false \<equiv> Atom (\<lambda>_. False)"

definition Release :: "'val Prop \<Rightarrow> 'val Prop \<Rightarrow> 'val Prop" (infix "[R]" 50) where
  "\<phi> [R] \<psi> \<equiv> Not (Not \<phi> [U] Not \<psi>)"

definition Finally :: "'val Prop \<Rightarrow> 'val Prop" ("\<diamondsuit> _" [100] 80) where
  "\<diamondsuit>\<phi> \<equiv> true [U] \<phi>"

definition Globally :: "'val Prop \<Rightarrow> 'val Prop" ("\<box> _" [100] 80) where
  "\<box>\<phi> \<equiv> false [R] \<phi>"

definition Paths :: "'val world \<Rightarrow> (nat \<Rightarrow> 'val world) set" where
  "Paths w = {\<pi>. \<pi> 0 = w \<and> (\<forall>i. execute_step step (\<pi> i) (\<pi> (i+1)))}"

definition suffix where
  "suffix k \<pi> \<equiv> \<lambda>i. \<pi> (k+i)"

primrec semantical_path :: "(nat \<Rightarrow> 'val world) \<Rightarrow> 'val Prop \<Rightarrow> bool" (infix "\<Turnstile>p" 60) where
  "(\<pi> \<Turnstile>p Atom p) = p (\<pi> 0)"
| "(\<pi> \<Turnstile>p Not p) = (\<not> (\<pi> \<Turnstile>p p))"
| "(\<pi> \<Turnstile>p Or p q) = (\<pi> \<Turnstile>p p \<or> \<pi> \<Turnstile>p q)"
| "(\<pi> \<Turnstile>p Next p) = (suffix 1 \<pi> \<Turnstile>p p)"
| "(\<pi> \<Turnstile>p Until p q) = (\<exists>i. suffix i \<pi> \<Turnstile>p q \<and> (\<forall>j. i < j \<longrightarrow> suffix j \<pi> \<Turnstile>p p))"

definition semantical :: "'val world \<Rightarrow> 'val Prop \<Rightarrow> bool" (infix "\<Turnstile>" 60) where
  "w \<Turnstile> p = (\<forall>\<pi>. \<pi> 0 = w \<and> \<pi> \<Turnstile>p p)"

lemma not_true_iff_false [simp]:
  "w \<Turnstile> Not true = w \<Turnstile> false"
  by (simp add: semantical_def true_def false_def)

lemma next_not_compat [simp]:
  "w \<Turnstile> \<circle> (Not \<phi>) = w \<Turnstile> Not (\<circle> \<phi>)"
  by (simp add: semantical_def)

lemma path_until_release_iff:
  "\<pi> \<Turnstile>p (p [R] q) = (\<not> \<pi> \<Turnstile>p (Not p [U] Not q))"
  "\<pi> \<Turnstile>p (p [U] q) = (\<not> \<pi> \<Turnstile>p (Not p [R] Not q))"
  apply (simp add: Release_def)
  apply (simp add: Release_def)
  done

lemma Globally_and_Finally:
  "\<pi> \<Turnstile>p \<box>\<phi> = \<pi> \<Turnstile>p Not (\<diamondsuit> (Not \<phi>))"
  unfolding Globally_def Finally_def
proof-
  have "\<pi> \<Turnstile>p Not (true [U] Not \<phi>) = (\<not> \<pi> \<Turnstile>p (true [U] Not \<phi>))"
    by simp
  also have "\<dots> = (\<pi> \<Turnstile>p (Not true [R] Not (Not \<phi>)))"
    using path_until_release_iff(2) by blast
  also have "\<dots> = (\<pi> \<Turnstile>p (false [R] \<phi>))"
    by (simp add: false_def path_until_release_iff(1) true_def)
  finally show "\<pi> \<Turnstile>p (false [R] \<phi>) = \<pi> \<Turnstile>p Prop.Not (true [U] Prop.Not \<phi>)" by simp
qed

end
