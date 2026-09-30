section \<open>Basic Parallel Merge Examples\<close>

theory utp_ap_parallel_examples
  imports utp_ap_parallel "UTP-Reactive-Angelic-Designs.utp_rad_parallel_examples"
begin

subsection \<open>A Basic Merge for Singleton Branch Observations\<close>

text \<open>
  This example repairs the shared singleton-branch seed with APOKM. The seed
  explicitly requires matching branch traces and combines waiting flags by
  disjunction; these are choices of merge policy. The example does not specify
  how a merge should combine arbitrary multistate angelic choice sets.

  At a started, nonwaiting prior with zero trace, the repaired merge agrees
  with the seed. At an unstarted or waiting prior, AP healthiness supplies
  its corresponding boundary behaviour instead.
\<close>

definition BasicMerge_AP :: "('t::trace, 'e) rad_state ades_merge_rel" where
  "BasicMerge_AP = APOKM basic_merge_seed"

lemma BasicMerge_AP_form:
  "BasicMerge_AP = RA3APM (RA2M (A0m (A1m basic_merge_seed)))"
proof -
  have seed: "(\<lambda>(m,out).
      des_vars.ok\<^sub>v out =
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
      basic_merge_seed (m,out)) = basic_merge_seed"
    by (auto simp: basic_merge_seed_def fun_eq_iff)
  show ?thesis by (simp only: BasicMerge_AP_def APOKM_def seed)
qed

lemma APOKM_basic_merge_seed:
  "APOKM basic_merge_seed = BasicMerge_AP"
  by (simp add: APOKM_def BasicMerge_AP_def)

lemma BasicMerge_AP_healthy [closure]: "BasicMerge_AP is APOKM"
  by (simp add: BasicMerge_AP_def APOKM_healthy)

lemma ap_par_basic_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is AP" "Q is AP"
  shows "ap_par P basic_merge_seed Q is AP"
  by (rule ap_par_AP_closure[OF assms])

lemma BasicMerge_AP_SymMerge: "BasicMerge_AP is SymMerge"
  unfolding BasicMerge_AP_def
  by (rule APOKM_SymMerge, rule basic_merge_seed_SymMerge)

lemma ap_par_basic_comm:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  shows "ap_par P basic_merge_seed Q = ap_par Q basic_merge_seed P"
  by (rule ap_par_comm[OF basic_merge_seed_SymMerge])

lemma BasicMerge_AP_started_zero:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x p q out) (ades_obs True s0 c X) =
    (\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs True s0 c X)"
  by (simp add: BasicMerge_AP_form RA3APM_eval RA2M_zero
      assms A_basic_merge_seed_eval)

lemma ap_par_basic_started_zero:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and s0 :: "('t, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "ap_par P basic_merge_seed Q (ades_obs True s0 c X) \<longleftrightarrow>
    (c \<and> (\<exists>l r z.
      P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and>
      z \<in> X \<and> basic_merge_state s0 l r z))"
proof -
  have eval: "ap_par P basic_merge_seed Q (ades_obs True s0 c X) =
    (\<exists>p q. P (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,p) \<and>
      Q (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,q) \<and>
      (\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs True s0 c X))"
    by (subst ap_par_eval; simp only: APOKM_basic_merge_seed
        BasicMerge_AP_started_zero[OF assms, simplified case_prod_conv] case_prod_conv)
  have obs: "p = \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>"
    if "des_vars.ok\<^sub>v p" "achoices.ac\<^sub>v (des_vars.more p) = {l}" for p l
    using that by (cases p; pred_auto)
  show ?thesis
  proof
    assume h: "ap_par P basic_merge_seed Q (ades_obs True s0 c X)"
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
    show "ap_par P basic_merge_seed Q (ades_obs True s0 c X)"
      unfolding eval
      apply (rule exI[of _ "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>"])
      apply (rule exI[of _ "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>"])
      using h by (auto simp: basic_merge_seed_eval)
  qed
qed

lemma BasicMerge_AP_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 True {z}) \<longleftrightarrow> basic_merge_state s0 l r z"
  by (simp only: BasicMerge_AP_started_zero[OF assms] basic_merge_seed_obs;
      auto)

lemma BasicMerge_AP_trace_mismatch:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
    "rad_state.tr\<^sub>v l \<noteq> rad_state.tr\<^sub>v r"
  shows "\<not> (\<lambda>(x,out). ades_merge_eval BasicMerge_AP x \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 True {z})"
  by (simp only: BasicMerge_AP_singletons[OF assms(1,2)];
      use assms(3) in \<open>auto simp: basic_merge_state_def\<close>)

lemma BasicMerge_AP_nonskip_example:
  fixes s0 l r z :: "(unit list, unit) rad_state"
  defines prior_def:
    "s0 \<equiv> \<lparr>tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = False, \<dots> = ()\<rparr>"
    and left_def:
    "l \<equiv> \<lparr>tr\<^sub>v = [()], ref\<^sub>v = {}, wait\<^sub>v = True, \<dots> = ()\<rparr>"
    and right_def:
    "r \<equiv> \<lparr>tr\<^sub>v = [()], ref\<^sub>v = {}, wait\<^sub>v = False, \<dots> = ()\<rparr>"
    and output_def:
    "z \<equiv> \<lparr>tr\<^sub>v = [()], ref\<^sub>v = {()}, wait\<^sub>v = True, \<dots> = ()\<rparr>"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 True {z})"
    and "z \<noteq> s0"
proof -
  have zero: "rad_state.tr\<^sub>v s0 = 0" and active: "\<not> rad_state.wait\<^sub>v s0"
    by (simp_all add: prior_def)
  show "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 True {z})"
    by (simp only: BasicMerge_AP_singletons[OF zero active];
        simp add: basic_merge_state_def prior_def left_def right_def output_def)
  show "z \<noteq> s0" by (simp add: prior_def output_def)
qed

lemma BasicMerge_AP_unstarted:
  fixes s0 :: "('t::trace, 'e) rad_state"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x p q out) (ades_obs False s0 c X)"
  by (simp add: BasicMerge_AP_def APOKM_eval II_AP_eval)

lemma BasicMerge_AP_wait:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "rad_state.wait\<^sub>v s0"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x p q out) (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not> b \<or> (c \<and> s0 \<in> X))"
  by (simp add: BasicMerge_AP_def APOKM_def RA3APM_eval II_AP_eval assms)

lemma BasicMerge_AP_wait_repairs_failed_branches:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "rad_state.wait\<^sub>v s0"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 True {s0})"
    and "\<not> (\<lambda>(x,out). ades_merge_eval basic_merge_seed x \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 True {s0})"
  by (simp_all add: BasicMerge_AP_def APOKM_def RA3APM_eval
      II_AP_eval assms basic_merge_seed_eval)

subsection \<open>Associativity and Worked Prefixes\<close>

lemma RA3APM_AssocMerge:
  assumes "AssocMerge M"
  shows "AssocMerge (RA3APM M)"
  using assms
  by (auto simp only: AssocMerge_ades RA3APM_eval split: if_splits; blast)

lemma BasicMerge_AP_AssocMerge: "AssocMerge BasicMerge_AP"
  by (simp only: BasicMerge_AP_form;
      intro RA3APM_AssocMerge RA2M_AssocMerge A_basic_merge_seed_AssocMerge)

lemma ap_par_basic_assoc:
  "ap_par (ap_par P basic_merge_seed Q) basic_merge_seed R =
    ap_par P basic_merge_seed (ap_par Q basic_merge_seed R)"
  by (rule ap_par_assoc; simp only: APOKM_basic_merge_seed BasicMerge_AP_SymMerge BasicMerge_AP_AssocMerge)

lemma BasicMerge_AP_prefix_singleton:
  "PrefixSkip_AP a (ades_obs True s0 True {z}) =
    PrefixSkip_RAD a (ades_obs True s0 True {z})"
  using fun_cong[OF H1_PrefixSkip_RAD[of a], of "ades_obs True s0 True {z}"]
  by (simp add: H1_obs)

lemma ap_par_basic_prefixes_complete:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
    "\<not> rad_state.wait\<^sub>v z"
  shows "ap_par (PrefixSkip_AP a) basic_merge_seed (PrefixSkip_AP b)
    (ades_obs True s0 c {z}) \<longleftrightarrow>
    (c \<and> a = b \<and> rad_state.tr\<^sub>v z = [a])"
  by (simp only: ap_par_basic_started_zero[OF assms(1,2)]
      BasicMerge_AP_prefix_singleton BasicMerge_RAD_prefix_singleton[OF assms(2)];
      auto simp: basic_merge_state_def assms zero_list_def intro!: exI[where x=z])

lemma basic_merge_seed_not_APM:
  "\<not> ((basic_merge_seed :: ('t::trace, 'e) rad_merge_rel) is APOKM)"
proof
  let ?M = "basic_merge_seed :: ('t, 'e) rad_merge_rel"
  let ?s0 = "\<lparr>tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = True, \<dots> = ()\<rparr>
    :: ('t, 'e) rad_state"
  let ?p = "ades_output False {}"
  assume h: "?M is APOKM"
  have fixed: "APOKM ?M = ?M" by (rule Healthy_if[OF h])
  have eq: "(\<lambda>(x,out). ades_merge_eval BasicMerge_AP x ?p ?p out) (ades_obs True ?s0 True {?s0}) =
    (\<lambda>(x,out). ades_merge_eval ?M x ?p ?p out) (ades_obs True ?s0 True {?s0})"
    by (simp only: BasicMerge_AP_def fixed)
  show False using eq
    by (simp add: BasicMerge_AP_def APOKM_def RA3APM_eval II_AP_eval basic_merge_seed_eval)
qed

end
