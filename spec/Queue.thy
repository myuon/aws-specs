theory Queue
  imports Main
begin

datatype MessageId = MessageId nat

fun getMessageId where
  "getMessageId (MessageId n) = n"

record 'a Queue =
  messages :: "nat \<rightharpoonup> 'a"

definition finiteQueue where
  "finiteQueue st = Finite_Set.finite (dom (messages st))"

definition empty where
  "empty = \<lparr> messages = Map.empty \<rparr>"

definition insert where
  "insert st v \<equiv> st \<lparr> messages := (messages st) ((SOME x. x \<notin> dom (messages st)) \<mapsto> v) \<rparr>"

definition get :: "'a Queue \<Rightarrow> MessageId \<Rightarrow> 'a option" where
  "get st m = messages st (getMessageId m)"

definition delete :: "'a Queue \<Rightarrow> MessageId \<Rightarrow> 'a Queue" where
  "delete st m = st \<lparr> messages := (messages st) (getMessageId m := None) \<rparr>"

lemma insert_existence: "finiteQueue st \<Longrightarrow> \<exists>x. x \<notin> dom (messages st)"
  apply (simp add: finiteQueue_def)
  by (simp add: ex_new_if_finite)

lemma insert_new_point_exists:
  "finiteQueue st \<Longrightarrow> \<exists>m \<in> dom (messages (insert st v)). get (insert st v) (MessageId m) = Some v"
  apply (simp add: finiteQueue_def)
  by (simp add: Queue.insert_def get_def)

lemma insert_get: "get st m = Some v \<Longrightarrow> get (insert st v) m = Some v"
  by (simp add: get_def insert_def)

definition pick :: "'a Queue \<Rightarrow> nat \<Rightarrow> (MessageId \<times> 'a) list" where
  "pick st n = map (\<lambda>x. (MessageId x, the (get st (MessageId x)))) (SOME xs. set xs \<subseteq> dom (messages st) \<and> length xs = min n (card (dom (messages st))))"

lemma pick_existence: "finite X \<Longrightarrow> \<exists>(xs :: nat list). set xs \<subseteq> X \<and> length xs = min n (card X)"
  apply (cases "card X < n")
proof-
  assume "finite X" "card X < n"
  have "\<exists>xs. set xs \<subseteq> X \<and> length xs = card X"
    by (metis \<open>finite X\<close> equalityD2 finite_list length_remdups_card_conv set_remdups)
  have "min n (card X) = card X"
    by (simp add: \<open>card X < n\<close> less_or_eq_imp_le min_absorb2)
  show ?thesis
    by (simp add: \<open>\<exists>xs. set xs \<subseteq> X \<and> length xs = card X\<close> \<open>min n (card X) = card X\<close>)
next
  assume "finite X" "\<not> card X < n"
  have "n \<le> card X"
    using \<open>\<not> card X < n\<close> not_less by blast
  have "n \<le> card (X :: nat set) \<Longrightarrow> \<exists>Y. Y \<subseteq> X \<and> card Y = n"
    apply (induct n arbitrary: X)
    using card_empty apply blast
  proof-
    fix n :: nat and X :: "nat set"
    assume hyp: "\<And>(X :: nat set). n \<le> card X \<Longrightarrow> \<exists>Y\<subseteq>X. card Y = n" "Suc n \<le> card X"
    obtain x xs where "X = {x} \<union> xs" "n \<le> card xs" "x \<notin> xs"
      by (metis \<open>Suc n \<le> card X\<close> card_le_Suc_iff insert_is_Un)
    obtain Y where "Y \<subseteq> xs" "card Y = n"
      using \<open>n \<le> card xs\<close> hyp(1) by auto
    have "x \<notin> Y"
      using \<open>Y \<subseteq> xs\<close> \<open>x \<notin> xs\<close> by blast
    have "card (Y \<union> {x}) = Suc n"
      by (metis Suc_le_lessD Un_insert_right \<open>X = {x} \<union> xs\<close> \<open>Y \<subseteq> xs\<close> \<open>card Y = n\<close> \<open>x \<notin> Y\<close> card_gt_0_iff card_infinite card_insert_disjoint finite_Un finite_subset hyp(2) sup_bot.right_neutral)
    show "\<exists>Y\<subseteq>X. card Y = Suc n"
      by (metis Un_insert_right \<open>X = {x} \<union> xs\<close> \<open>Y \<subseteq> xs\<close> \<open>card (Y \<union> {x}) = Suc n\<close> insert_is_Un insert_subset order_refl order_trans sup_bot.right_neutral)
  qed
  have "\<exists>xs. set xs \<subseteq> X \<and> length xs = n"
    by (metis \<open>\<not> card X < n\<close> \<open>finite X\<close> \<open>n \<le> card X \<Longrightarrow> \<exists>Y\<subseteq>X. card Y = n\<close> finite_list le_less_linear length_remdups_card_conv rev_finite_subset set_remdups)
  show ?thesis
    by (simp add: \<open>\<exists>xs. set xs \<subseteq> X \<and> length xs = n\<close> \<open>n \<le> card X\<close> min_def)
qed

lemma pick_internal_set_some: "\<lbrakk> finiteQueue st; V = (SOME xs. set xs \<subseteq> dom (messages st) \<and> length xs = min n (card (dom (messages st)))) \<rbrakk>
  \<Longrightarrow> set V \<subseteq> dom (messages st) \<and> length V = min n (card (dom (messages st)))"
  apply (simp add: finiteQueue_def)
  by (smt pick_existence tfl_some)

lemma pick_fst_in_domain: "\<lbrakk> finiteQueue st; (m,v) \<in> set (pick st n) \<rbrakk> \<Longrightarrow> getMessageId m \<in> dom (messages st)"
proof-
  assume "finiteQueue st" "(m,v) \<in> set (pick st n)"
  have "getMessageId m \<in> set (SOME xs. set xs \<subseteq> dom (messages st) \<and> length xs = min n (card (dom (messages st))))"
    using \<open>(m,v) \<in> set (pick st n)\<close>
    by (auto simp add: pick_def)
  show "getMessageId m \<in> dom (messages st)"
    by (meson \<open>finiteQueue st\<close> \<open>getMessageId m \<in> set (SOME xs. set xs \<subseteq> dom (messages st) \<and> length xs = min n (card (dom (messages st))))\<close> in_mono pick_internal_set_some)
qed

lemma pick_get: "\<lbrakk> finiteQueue st; (m,v) \<in> set (pick st n) \<rbrakk> \<Longrightarrow> get st m = Some v"
proof-
  assume "finiteQueue st" "(m,v) \<in> set (pick st n)"
  show "get st m = Some v"
    using \<open>(m,v) \<in> set (pick st n)\<close>
    apply (auto simp add: pick_def)
    by (metis \<open>(m, v) \<in> set (pick st n)\<close> \<open>finiteQueue st\<close> domIff get_def option.exhaust_sel pick_fst_in_domain)
qed

end
