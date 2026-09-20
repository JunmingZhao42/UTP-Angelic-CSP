section \<open>Basic Parallel Merge Examples\<close>

theory utp_rad_parallel_examples
  imports utp_rad_parallel_generic utp_rad_ops
begin

subsection \<open>A singleton lifting of the basic reactive merge\<close>

text \<open>
  The trace policy follows the state-free instance of BasicMerge in
  UTP-Reactive-Designs.utp_rdes_parallel. Our alphabet has no separate ordinary
  state to frame. We additionally choose a disjunction for the waiting flags:
  both branch traces and the resulting trace agree, and the result waits when
  either branch waits.  Refusals are unconstrained.  These clauses are an
  explicit choice of merge policy, rather than part of the generic operator.

  The successful seed below requires singleton branch observations.  Merely
  selecting an element from each branch choice set would allow upward-closed
  operands to add arbitrary states and circumvent the trace policy.  This
  singleton lifting does not specify general multi-state angelic merging.
  The seed tests only branch and output observations with ok = True; waiting
  is handled separately. Healthiness supplies startup and waiting-prior
  behaviour. This example does not define general divergence propagation.
\<close>

definition basic_merge_state ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow>
   ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> bool"
where
  "basic_merge_state s0 l r z \<longleftrightarrow>
    rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
    rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v l \<and>
    rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v r \<and>
    rad_state.wait\<^sub>v z = (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r)"

definition basic_merge_seed :: "('t::trace, 'e) rad_merge_rel"
where
  "basic_merge_seed = (\<lambda>(m,out).
    des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
    des_vars.ok\<^sub>v (mrg_right\<^sub>v m) \<and> des_vars.ok\<^sub>v out \<and>
    (\<exists>l r z.
      achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)) = {l} \<and>
      achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m)) = {r} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      basic_merge_state (astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m))) l r z))"

lemma basic_merge_seed_eval:
  "ades_merge_eval basic_merge_seed x p q out \<longleftrightarrow>
    des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q \<and> des_vars.ok\<^sub>v out \<and>
    (\<exists>l r z. achoices.ac\<^sub>v (des_vars.more p) = {l} \<and>
      achoices.ac\<^sub>v (des_vars.more q) = {r} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      basic_merge_state (astate.s\<^sub>v (des_vars.more x)) l r z)"
  by (simp add: basic_merge_seed_def)

lemma basic_merge_seed_obs:
  "merge_slice basic_merge_seed p q (ades_obs b s0 c X) \<longleftrightarrow>
    des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q \<and> c \<and>
    (\<exists>l r z. achoices.ac\<^sub>v (des_vars.more p) = {l} \<and>
      achoices.ac\<^sub>v (des_vars.more q) = {r} \<and>
      z \<in> X \<and> basic_merge_state s0 l r z)"
  by (simp add: basic_merge_seed_eval)

lemma basic_merge_seed_MergeSym: "MergeSym basic_merge_seed"
  by (auto simp add: MergeSym_def basic_merge_seed_eval basic_merge_state_def;
      blast)

lemma basic_merge_seed_H2M [closure]: "basic_merge_seed is H2M"
  by (rule Healthy_intro, rule merge_slice_ext, rule ades_obs_ext;
      simp add: H2M_def H2_obs basic_merge_seed_obs basic_merge_seed_eval; blast)

lemma basic_merge_seed_A0M [closure]: "basic_merge_seed is A0M"
  by (rule Healthy_intro, rule merge_slice_ext, rule ades_obs_ext;
      simp add: A0M_def A0_obs basic_merge_seed_obs basic_merge_seed_eval; blast)

lemma basic_merge_seed_A2M [closure]: "basic_merge_seed is A2M"
  by (rule Healthy_intro, rule merge_slice_ext, rule ades_obs_ext;
      simp add: A2M_def A2_obs basic_merge_seed_obs basic_merge_seed_eval; blast)

lemma basic_merge_seed_PBMHM [closure]: "basic_merge_seed is PBMHM"
  by (rule Healthy_intro, rule merge_slice_ext, rule ades_obs_ext;
      simp add: PBMHM_def PBMH_ades_obs basic_merge_seed_eval; blast)

lemma basic_merge_seed_RA1M [closure]: "basic_merge_seed is RA1M"
  by (rule Healthy_intro, rule merge_slice_ext, rule ades_obs_ext;
      auto simp add: RA1M_def RA1_obs basic_merge_seed_obs basic_merge_seed_eval
        basic_merge_state_def rad_trace_extensions_def; blast)

lemma basic_merge_seed_H1M_ADM [closure]: "H1M basic_merge_seed is ADM"
proof -
  have h1: "H1M basic_merge_seed is H1M" by (rule H1M_healthy)
  have h2: "H1M basic_merge_seed is H2M"
    by (rule Healthy_intro, rule merge_slice_ext, rule ades_obs_ext;
        simp add: H2M_def H1M_def H2_obs H1_obs basic_merge_seed_eval; blast)
  have pb: "H1M basic_merge_seed is PBMHM"
    using basic_merge_seed_PBMHM
    by (simp only: PBMHM_healthy_iff H1M_def merge_health_slice;
        blast intro: H1_PBMH_ades_closure)
  have a0: "H1M basic_merge_seed is A0M"
    by (rule Healthy_intro, rule merge_slice_ext, rule ades_obs_ext;
        simp add: A0M_def H1M_def A0_obs H1_obs basic_merge_seed_obs basic_merge_seed_eval; blast)
  show ?thesis by (rule ADM_intro[OF h1 h2 pb a0])
qed

lemma basic_merge_seed_ADM_eq_H1M:
  "ADM (basic_merge_seed :: ('t::trace, 'e) rad_merge_rel) = H1M basic_merge_seed"
proof -
  let ?M = "basic_merge_seed :: ('t, 'e) rad_merge_rel"
  have absorb_slice: "A (H1 P) = A P" for P :: "('t, 'e) reactive_angelic_design"
    using A_H1_commute[of P] A_is_H1[of P]
    by (simp only: comp_apply Healthy_def')
  have absorb: "ADM (H1M ?M) = ADM ?M"
    by (rule merge_slice_ext;
        simp only: ADM_def H1M_def merge_health_slice absorb_slice)
  have healthy: "ADM (H1M ?M) = H1M ?M"
    by (rule Healthy_if[OF basic_merge_seed_H1M_ADM])
  show ?thesis using absorb healthy by simp
qed

definition BasicMerge_RAD :: "('t::trace, 'e) rad_merge_rel"
where "BasicMerge_RAD = RADM_full basic_merge_seed"

lemma OkM_basic_merge_seed [simp]: "OkM basic_merge_seed = basic_merge_seed"
  by (auto simp: OkM_def basic_merge_seed_def fun_eq_iff)

lemma RADOKM_basic_merge_seed:
  "RADOKM basic_merge_seed = BasicMerge_RAD"
  by (simp add: RADOKM_def BasicMerge_RAD_def)

lemma BasicMerge_RAD_healthy [closure]: "BasicMerge_RAD is RADM_full"
  by (simp add: BasicMerge_RAD_def RADM_full_healthy)

lemma BasicMerge_RAD_MergeSym: "MergeSym BasicMerge_RAD"
  unfolding BasicMerge_RAD_def
  by (rule RADM_full_MergeSym[OF basic_merge_seed_MergeSym])

lemma rad_par_full_basic_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "rad_par_full P basic_merge_seed Q is RAD"
  by (rule rad_par_full_RAD_closure[OF assms])

lemma rad_par_full_basic_comm:
  "rad_par_full P basic_merge_seed Q = rad_par_full Q basic_merge_seed P"
  by (rule rad_par_full_comm[OF basic_merge_seed_MergeSym])

lemma BasicMerge_RAD_def':
  "BasicMerge_RAD = RA3M (RA2M (CSPA1M basic_merge_seed))"
proof -
  have commute: "RA1M (CSPA1M M) = CSPA1M (RA1M M)" for M
    by (rule merge_slice_ext;
        simp add: RA1M_def CSPA1M_def
          RA1_CSPA1_commute[simplified comp_apply])
  show ?thesis
    by (simp only: BasicMerge_RAD_def RADM_full_def comp_apply
        Healthy_if[OF basic_merge_seed_PBMHM]
        Healthy_if[OF basic_merge_seed_H2M] commute
        Healthy_if[OF basic_merge_seed_RA1M])
qed

lemma BasicMerge_RAD_started_zero:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
  shows "merge_slice BasicMerge_RAD p q (ades_obs True s0 c X) =
    merge_slice basic_merge_seed p q (ades_obs True s0 c X)"
  by (simp add: BasicMerge_RAD_def' RA3M_def RA3_obs RA2M_zero
      CSPA1M_def merge_health_eval CSPA1_obs assms)

lemma BasicMerge_RAD_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
  shows "merge_slice BasicMerge_RAD
      \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
      \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
      (ades_obs True s0 c {z}) \<longleftrightarrow>
    (c \<and> basic_merge_state s0 l r z)"
  by (simp only: BasicMerge_RAD_started_zero[OF assms] basic_merge_seed_obs; simp)

lemma BasicMerge_RAD_matching_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
    "rad_state.tr\<^sub>v l = rad_state.tr\<^sub>v r"
    "rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v l"
    "rad_state.wait\<^sub>v z = (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r)"
  shows "merge_slice BasicMerge_RAD
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    (ades_obs True s0 True {z})"
  by (simp only: BasicMerge_RAD_singletons[OF assms(1,2)];
      simp add: basic_merge_state_def assms)

lemma BasicMerge_RAD_mismatching_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
    "rad_state.tr\<^sub>v l \<noteq> rad_state.tr\<^sub>v r"
  shows "\<not> merge_slice BasicMerge_RAD
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    (ades_obs True s0 c {z})"
  using assms(3)
  by (simp only: BasicMerge_RAD_singletons[OF assms(1,2)];
      auto simp: basic_merge_state_def)

lemma rad_par_full_basic_started_zero:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and s0 :: "('t, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
  shows "rad_par_full P basic_merge_seed Q (ades_obs True s0 c X) \<longleftrightarrow>
    (c \<and> (\<exists>l r z.
      P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and>
      z \<in> X \<and> basic_merge_state s0 l r z))"
proof -
  have eval: "rad_par_full P basic_merge_seed Q (ades_obs True s0 c X) =
    (\<exists>p q. P (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,p) \<and>
      Q (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,q) \<and>
      merge_slice basic_merge_seed p q (ades_obs True s0 c X))"
    by (subst rad_par_full_eval; simp only: RADOKM_basic_merge_seed
        BasicMerge_RAD_started_zero[OF assms, simplified merge_slice_eval] merge_slice_eval)
  have obs: "p = \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>"
    if "des_vars.ok\<^sub>v p" "achoices.ac\<^sub>v (des_vars.more p) = {l}" for p l
    using that by (cases p; pred_auto)
  show ?thesis
  proof
    assume h: "rad_par_full P basic_merge_seed Q (ades_obs True s0 c X)"
    obtain p q l r z where h:
      "P (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,p)"
      "Q (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,q)"
      "des_vars.ok\<^sub>v p" "des_vars.ok\<^sub>v q" "c"
      "achoices.ac\<^sub>v (des_vars.more p) = {l}"
      "achoices.ac\<^sub>v (des_vars.more q) = {r}"
      "z \<in> X" "basic_merge_state s0 l r z"
      using h by (auto simp: eval basic_merge_seed_eval)
    show "c \<and> (\<exists>l r z. P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and> z \<in> X \<and> basic_merge_state s0 l r z)"
      using h(1,2,5,8,9) by (simp only: obs[OF h(3,6)] obs[OF h(4,7)]; blast)
  next
    assume "c \<and> (\<exists>l r z. P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and> z \<in> X \<and> basic_merge_state s0 l r z)"
    then obtain l r z where h: "c" "P (ades_obs True s0 True {l})"
      "Q (ades_obs True s0 True {r})" "z \<in> X" "basic_merge_state s0 l r z" by blast
    show "rad_par_full P basic_merge_seed Q (ades_obs True s0 c X)"
      unfolding eval
      apply (rule exI[of _ "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>"])
      apply (rule exI[of _ "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>"])
      using h by (auto simp: basic_merge_seed_eval)
  qed
qed

subsection \<open>Associativity and Worked Prefixes\<close>

lemma trace_difference_eq_iff:
  fixes t0 a b :: "'t::trace"
  assumes "t0 \<le> a" "t0 \<le> b"
  shows "a - t0 = b - t0 \<longleftrightarrow> a = b"
proof
  assume eq: "a - t0 = b - t0"
  have "a = t0 + (a - t0)"
    using assms(1) by (simp add: diff_add_cancel_left')
  also have "... = t0 + (b - t0)" by (simp only: eq)
  also have "... = b" by (rule diff_add_cancel_left'[OF assms(2)])
  finally show "a = b" .
next
  assume "a = b"
  then show "a - t0 = b - t0" by simp
qed

(* Simultaneous normalization preserves associativity: the intermediate
   choice observation can be renamed through its surjective output map. *)
lemma RA2M_MergeAssoc:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "MergeAssoc M"
  shows "MergeAssoc (RA2M M)"
proof (unfold MergeAssoc_def, intro allI)
  fix x :: "('t, 'e) rad_state astate des_vars_ext"
    and p q r out :: "('t, 'e) rad_state achoices des_vars_ext"
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  let ?N = "rad_merge_output ?s0"
  let ?x = "rad_merge_input x"
  have assoc:
    "(\<exists>y. ades_merge_eval M ?x (?N p) (?N q) y \<and>
          ades_merge_eval M ?x y (?N r) (?N out)) =
     (\<exists>y. ades_merge_eval M ?x (?N q) (?N r) y \<and>
          ades_merge_eval M ?x (?N p) y (?N out))"
    using assms by (auto simp: MergeAssoc_def)
  show "(\<exists>y. ades_merge_eval (RA2M M) x p q y \<and>
          ades_merge_eval (RA2M M) x y r out) =
     (\<exists>y. ades_merge_eval (RA2M M) x q r y \<and>
          ades_merge_eval (RA2M M) x p y out)"
  proof
    assume left: "\<exists>y. ades_merge_eval (RA2M M) x p q y \<and>
      ades_merge_eval (RA2M M) x y r out"
    then obtain y where
      "ades_merge_eval M ?x (?N p) (?N q) (?N y)"
      "ades_merge_eval M ?x (?N y) (?N r) (?N out)"
      by (auto simp only: RA2M_eval)
    with assoc obtain z where z:
      "ades_merge_eval M ?x (?N q) (?N r) z"
      "ades_merge_eval M ?x (?N p) z (?N out)" by blast
    obtain target where target: "?N target = z"
      by (rule rad_merge_output_surj)
    show "\<exists>y. ades_merge_eval (RA2M M) x q r y \<and>
      ades_merge_eval (RA2M M) x p y out"
      using z target by (auto simp only: RA2M_eval)
  next
    assume right: "\<exists>y. ades_merge_eval (RA2M M) x q r y \<and>
      ades_merge_eval (RA2M M) x p y out"
    then obtain y where
      "ades_merge_eval M ?x (?N q) (?N r) (?N y)"
      "ades_merge_eval M ?x (?N p) (?N y) (?N out)"
      by (auto simp only: RA2M_eval)
    with assoc obtain z where z:
      "ades_merge_eval M ?x (?N p) (?N q) z"
      "ades_merge_eval M ?x z (?N r) (?N out)" by blast
    obtain target where target: "?N target = z"
      by (rule rad_merge_output_surj)
    show "\<exists>y. ades_merge_eval (RA2M M) x p q y \<and>
      ades_merge_eval (RA2M M) x y r out"
      using z target by (auto simp only: RA2M_eval)
  qed
qed

(* The raw state relation is associative. The intermediate refusal is free;
   reuse the final state's refusal and replace only its waiting flag. *)
lemma basic_merge_state_assoc:
  "(\<exists>v. basic_merge_state s0 a b v \<and> basic_merge_state s0 v c z) =
   (\<exists>v. basic_merge_state s0 b c v \<and> basic_merge_state s0 a v z)"
proof -
  have left:
    "(\<exists>v. basic_merge_state s0 a b v \<and> basic_merge_state s0 v c z) =
     (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v a \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v b \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v c \<and>
      rad_state.wait\<^sub>v z =
        ((rad_state.wait\<^sub>v a \<or> rad_state.wait\<^sub>v b) \<or> rad_state.wait\<^sub>v c))"
    by (auto simp add: basic_merge_state_def
        intro!: exI[where x="rad_state.wait\<^sub>v_update
          (\<lambda>_. rad_state.wait\<^sub>v a \<or> rad_state.wait\<^sub>v b) z"])
  have right:
    "(\<exists>v. basic_merge_state s0 b c v \<and> basic_merge_state s0 a v z) =
     (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v a \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v b \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v c \<and>
      rad_state.wait\<^sub>v z =
        (rad_state.wait\<^sub>v a \<or> (rad_state.wait\<^sub>v b \<or> rad_state.wait\<^sub>v c)))"
    by (auto simp add: basic_merge_state_def
        intro!: exI[where x="rad_state.wait\<^sub>v_update
          (\<lambda>_. rad_state.wait\<^sub>v b \<or> rad_state.wait\<^sub>v c) z"])
  show ?thesis by (simp only: left right disj_assoc)
qed

(* Generic exact-singleton lifting: only the final choice is upward closed.
   This is deliberately different from selecting arbitrary members of both
   branch choice sets, which does NOT preserve associativity. *)
lemma singleton_merge_MergeAssoc:
  fixes M :: "'s ades_merge_rel"
    and B :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  assumes eval: "\<And>x p q out.
    ades_merge_eval M x p q out \<longleftrightarrow>
    (des_vars.ok\<^sub>v out \<and> (\<exists>a b z.
      p = ades_normal_output True {a} \<and>
      q = ades_normal_output True {b} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      B (astate.s\<^sub>v (des_vars.more x)) a b z))"
    and state_assoc: "\<And>s0 a b c z.
      (\<exists>v. B s0 a b v \<and> B s0 v c z) =
      (\<exists>v. B s0 b c v \<and> B s0 a v z)"
  shows "MergeAssoc M"
proof (unfold MergeAssoc_def, intro allI)
  fix x :: "'s astate des_vars_ext"
    and p q r out :: "'s achoices des_vars_ext"
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  show "(\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
    (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x p y out)"
  proof
    assume "\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out"
    then obtain a b c v z where
      p: "p = ades_normal_output True {a}" and
      q: "q = ades_normal_output True {b}" and
      r: "r = ades_normal_output True {c}" and
      out: "des_vars.ok\<^sub>v out" "z \<in> achoices.ac\<^sub>v (des_vars.more out)" and
      steps: "B ?s0 a b v" "B ?s0 v c z"
      by (auto simp add: eval)
    from steps state_assoc[of ?s0 a b c z]
    obtain w where w: "B ?s0 b c w" "B ?s0 a w z" by blast
    have "ades_merge_eval M x q r (ades_normal_output True {w})"
      using q r w by (auto simp add: eval)
    moreover have "ades_merge_eval M x p (ades_normal_output True {w}) out"
      using p out w by (auto simp add: eval)
    ultimately show "\<exists>y. ades_merge_eval M x q r y \<and>
      ades_merge_eval M x p y out" by blast
  next
    assume "\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x p y out"
    then obtain a b c w z where
      p: "p = ades_normal_output True {a}" and
      q: "q = ades_normal_output True {b}" and
      r: "r = ades_normal_output True {c}" and
      out: "des_vars.ok\<^sub>v out" "z \<in> achoices.ac\<^sub>v (des_vars.more out)" and
      steps: "B ?s0 b c w" "B ?s0 a w z"
      by (auto simp add: eval)
    from steps state_assoc[of ?s0 a b c z]
    obtain v where v: "B ?s0 a b v" "B ?s0 v c z" by blast
    have "ades_merge_eval M x p q (ades_normal_output True {v})"
      using p q v by (auto simp add: eval)
    moreover have "ades_merge_eval M x (ades_normal_output True {v}) r out"
      using r out v by (auto simp add: eval)
    ultimately show "\<exists>y. ades_merge_eval M x p q y \<and>
      ades_merge_eval M x y r out" by blast
  qed
qed

lemma BasicMerge_RAD_prefix_singleton:
  assumes "\<not> rad_state.wait\<^sub>v s0"
  shows "PrefixSkip_RAD a (ades_obs True s0 True {z}) \<longleftrightarrow>
    (if rad_state.wait\<^sub>v z
     then rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v s0 \<and> a \<notin> rad_state.ref\<^sub>v z
     else rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v s0 @ [a])"
  using assms
  by (simp add: PrefixSkip_RAD_design RA1_def Let_def prefix_post_p2ac
      p2ac_def ades_state_choice_def rad_trace_extensions_def;
      pred_auto)

lemma basic_merge_seed_eval':
  "ades_merge_eval basic_merge_seed x p q out \<longleftrightarrow>
    (des_vars.ok\<^sub>v out \<and> (\<exists>l r z.
      p = ades_normal_output True {l} \<and> q = ades_normal_output True {r} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      basic_merge_state (astate.s\<^sub>v (des_vars.more x)) l r z))"
proof -
  have obs: "p = ades_normal_output True {l} \<longleftrightarrow>
      (des_vars.ok\<^sub>v p \<and> achoices.ac\<^sub>v (des_vars.more p) = {l})" for p l
    by (cases p; pred_auto)
  show ?thesis by (simp only: basic_merge_seed_eval obs; blast)
qed

lemma basic_merge_seed_MergeAssoc: "MergeAssoc basic_merge_seed"
  by (rule singleton_merge_MergeAssoc[OF basic_merge_seed_eval' basic_merge_state_assoc])

lemma H1M_MergeAssoc:
  assumes "MergeAssoc M"
  shows "MergeAssoc (H1M M)"
proof -
  have eval: "ades_merge_eval (H1M M) x p q out =
    (\<not> des_vars.ok\<^sub>v x \<or> ades_merge_eval M x p q out)" for x p q out
    by (simp add: H1M_def merge_health_eval H1_def; pred_auto)
  show ?thesis using assms
    by (auto simp only: MergeAssoc_def eval; blast)
qed

lemma RA3M_MergeAssoc:
  assumes "MergeAssoc M"
  shows "MergeAssoc (RA3M M)"
proof -
  have eval: "ades_merge_eval (RA3M M) x p q out =
    (if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
     then II_Rac (x,out) else ades_merge_eval M x p q out)" for x p q out
    by (simp add: RA3M_def merge_health_eval RA3_eval)
  show ?thesis using assms
    by (auto simp only: MergeAssoc_def eval split: if_splits; blast)
qed

lemma basic_merge_CSPA1M_MergeAssoc:
  "MergeAssoc (CSPA1M (basic_merge_seed :: ('t::trace, 'e) rad_merge_rel))"
proof -
  have obs: "merge_slice (CSPA1M (basic_merge_seed :: ('t, 'e) rad_merge_rel)) p q (ades_obs b s0 c X) =
      (if b then merge_slice basic_merge_seed p q (ades_obs b s0 c X)
       else rad_trace_extensions s0 \<inter> X \<noteq> {})"
    for p q b s0 c X
    by (simp only: CSPA1M_def merge_health_slice CSPA1_obs basic_merge_seed_obs;
        auto simp: basic_merge_state_def rad_trace_extensions_def; blast)
  have eval: "ades_merge_eval (CSPA1M (basic_merge_seed :: ('t, 'e) rad_merge_rel)) x p q out =
    (if des_vars.ok\<^sub>v x then ades_merge_eval basic_merge_seed x p q out
     else rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
       achoices.ac\<^sub>v (des_vars.more out) \<noteq> {})" for x p q out
  proof -
    obtain b s0 c X where obs_pair: "(x,out) = ades_obs b s0 c X"
      by (cases x; cases out; pred_auto)
    note result = obs[of p q b s0 c X]
    show ?thesis using result obs_pair
      by (simp only: merge_slice_eval; cases x; cases out; auto)
  qed
  show ?thesis using basic_merge_seed_MergeAssoc
    by (auto simp only: MergeAssoc_def eval split: if_splits; blast)
qed

lemma BasicMerge_RAD_MergeAssoc: "MergeAssoc BasicMerge_RAD"
  by (simp only: BasicMerge_RAD_def';
      intro RA3M_MergeAssoc RA2M_MergeAssoc basic_merge_CSPA1M_MergeAssoc)

lemma rad_par_full_basic_assoc:
  "rad_par_full (rad_par_full P basic_merge_seed Q) basic_merge_seed R =
    rad_par_full P basic_merge_seed (rad_par_full Q basic_merge_seed R)"
  by (rule rad_par_full_assoc; simp only: RADOKM_basic_merge_seed BasicMerge_RAD_MergeAssoc)

lemma rad_par_full_basic_prefixes_complete:
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
    "\<not> rad_state.wait\<^sub>v z"
  shows "rad_par_full (PrefixSkip_RAD a) basic_merge_seed (PrefixSkip_RAD b)
    (ades_obs True s0 c {z}) \<longleftrightarrow>
    (c \<and> a = b \<and> rad_state.tr\<^sub>v z = [a])"
  by (simp only: rad_par_full_basic_started_zero[OF assms(1,2)]
      BasicMerge_RAD_prefix_singleton[OF assms(1)];
      auto simp: basic_merge_state_def assms zero_list_def intro!: exI[where x=z])

lemma BasicMerge_RAD_wait:
  assumes "rad_state.wait\<^sub>v s0"
  shows "merge_slice BasicMerge_RAD p q (ades_obs b s0 c X) =
    ((\<not> b \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}) \<or> (c \<and> s0 \<in> X))"
  by (simp add: BasicMerge_RAD_def' RA3M_def merge_health_eval RA3_eval
      II_Rac_eval assms)

lemma basic_merge_seed_not_RADM_full:
  "\<not> ((basic_merge_seed :: ('t::trace, 'e) rad_merge_rel) is RADM_full)"
proof
  let ?M = "basic_merge_seed :: ('t, 'e) rad_merge_rel"
  let ?s0 = "\<lparr>tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = True, \<dots> = ()\<rparr>
    :: ('t, 'e) rad_state"
  let ?p = "ades_normal_output False {}"
  assume h: "?M is RADM_full"
  have fixed: "RADM_full ?M = ?M" by (rule Healthy_if[OF h])
  have eq: "merge_slice BasicMerge_RAD ?p ?p (ades_obs True ?s0 True {?s0}) =
    merge_slice ?M ?p ?p (ades_obs True ?s0 True {?s0})"
    by (simp only: BasicMerge_RAD_def fixed)
  show False using eq
    by (simp add: BasicMerge_RAD_def' RA3M_def merge_health_eval RA3_eval
        II_Rac_eval basic_merge_seed_eval)
qed

lemma basic_merge_state_increments:
  assumes "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v l"
    "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v r"
  shows "basic_merge_state s0 l r z =
    (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
     rad_state.tr\<^sub>v z - rad_state.tr\<^sub>v s0 =
       rad_state.tr\<^sub>v l - rad_state.tr\<^sub>v s0 \<and>
     rad_state.tr\<^sub>v z - rad_state.tr\<^sub>v s0 =
       rad_state.tr\<^sub>v r - rad_state.tr\<^sub>v s0 \<and>
     rad_state.wait\<^sub>v z = (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r))"
  using assms
  by (cases "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z";
      simp add: basic_merge_state_def trace_difference_eq_iff)

end
