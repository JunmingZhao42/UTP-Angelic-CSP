section \<open>Basic Parallel Merge Examples\<close>

theory utp_ap_parallel_examples
  imports utp_ap_parallel_generic "UTP-Reactive-Angelic-Designs.utp_rad_parallel_examples"
begin

subsection \<open>A Basic Merge for Singleton Branch Observations\<close>

text \<open>
  This example repairs the shared singleton-branch seed with APM. The seed
  explicitly requires matching branch traces and combines waiting flags by
  disjunction; these are choices of merge policy. The example does not specify
  how a merge should combine arbitrary multistate angelic choice sets.

  At a started, nonwaiting prior with zero trace, the repaired merge agrees
  with the seed. At an unstarted or waiting prior, AP healthiness supplies
  its corresponding boundary behaviour instead.
\<close>

definition BasicMerge_AP :: "('t::trace, 'e) rad_state ades_merge_rel" where
  "BasicMerge_AP = APM basic_merge_seed"

lemma BasicMerge_AP_healthy [closure]: "BasicMerge_AP is APM"
  by (simp add: BasicMerge_AP_def APM_healthy)

lemma BasicMerge_AP_parallel_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is AP" "Q is AP"
  shows "ap_par_full P BasicMerge_AP Q is AP"
  by (rule ap_par_full_AP_closure[OF assms BasicMerge_AP_healthy])

lemma BasicMerge_AP_MergeSym: "MergeSym BasicMerge_AP"
  unfolding BasicMerge_AP_def
  by (rule APM_MergeSym, rule basic_merge_seed_MergeSym)

lemma BasicMerge_AP_parallel_comm:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  shows "ap_par_full P BasicMerge_AP Q = ap_par_full Q BasicMerge_AP P"
  by (rule ap_par_full_comm[OF BasicMerge_AP_MergeSym])

lemma BasicMerge_AP_started_zero:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "merge_slice BasicMerge_AP p q (ades_obs True s0 c X) =
    merge_slice basic_merge_seed p q (ades_obs True s0 c X)"
  by (simp add: BasicMerge_AP_def APM_def RA3APM_eval RA2M_zero
      assms basic_merge_seed_ADM_eq_H1M H1M_def merge_health_eval H1_obs)

lemma BasicMerge_AP_parallel_started_zero:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and s0 :: "('t, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "ap_par_full P BasicMerge_AP Q (ades_obs True s0 c X) \<longleftrightarrow>
    (c \<and> (\<exists>l r z.
      P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and>
      z \<in> X \<and> basic_merge_state s0 l r z))"
proof -
  have eq: "ap_par_full P BasicMerge_AP Q (ades_obs True s0 c X) =
      ades_par_full P basic_merge_seed Q (ades_obs True s0 c X)"
    by (simp only: ades_par_full_eval
        BasicMerge_AP_started_zero[OF assms, simplified merge_slice_eval])
  show ?thesis by (simp only: eq basic_merge_seed_parallel_eval)
qed

lemma BasicMerge_AP_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "merge_slice BasicMerge_AP
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    (ades_obs True s0 True {z}) \<longleftrightarrow> basic_merge_state s0 l r z"
  by (simp only: BasicMerge_AP_started_zero[OF assms] basic_merge_seed_obs;
      auto)

lemma BasicMerge_AP_trace_mismatch:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
    "rad_state.tr\<^sub>v l \<noteq> rad_state.tr\<^sub>v r"
  shows "\<not> merge_slice BasicMerge_AP
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
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
  shows "merge_slice BasicMerge_AP
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    (ades_obs True s0 True {z})"
    and "z \<noteq> s0"
proof -
  have zero: "rad_state.tr\<^sub>v s0 = 0" and active: "\<not> rad_state.wait\<^sub>v s0"
    by (simp_all add: prior_def)
  show "merge_slice BasicMerge_AP
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    (ades_obs True s0 True {z})"
    by (simp only: BasicMerge_AP_singletons[OF zero active];
        simp add: basic_merge_state_def prior_def left_def right_def output_def)
  show "z \<noteq> s0" by (simp add: prior_def output_def)
qed

lemma BasicMerge_AP_unstarted:
  fixes s0 :: "('t::trace, 'e) rad_state"
  shows "merge_slice BasicMerge_AP p q (ades_obs False s0 c X)"
proof -
  have healthy: "(BasicMerge_AP :: ('t, 'e) rad_state ades_merge_rel) is ADM"
    by (simp add: BasicMerge_AP_def APM_preserves_ADM)
  have slice: "merge_slice BasicMerge_AP p q is H1"
    using healthy by (auto simp only: ADM_components_iff H1M_healthy_iff)
  show ?thesis using slice by (simp add: H1_healthy_obs_iff)
qed

lemma BasicMerge_AP_wait:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "rad_state.wait\<^sub>v s0"
  shows "merge_slice BasicMerge_AP p q (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not> b \<or> (c \<and> s0 \<in> X))"
proof -
  have healthy: "(BasicMerge_AP :: ('t, 'e) rad_state ades_merge_rel) is RA3APM"
    by (simp add: BasicMerge_AP_def APM_preserves_RA3APM)
  show ?thesis
    using assms
    by (simp add: RA3APM_healthy_wait[OF healthy] II_AP_eval)
qed

lemma BasicMerge_AP_wait_repairs_failed_branches:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "rad_state.wait\<^sub>v s0"
  shows "merge_slice BasicMerge_AP
    \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr>
    (ades_obs True s0 True {s0})"
    and "\<not> merge_slice basic_merge_seed
    \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = False, ac\<^sub>v = {}, \<dots> = ()\<rparr>
    (ades_obs True s0 True {s0})"
  by (simp_all add: BasicMerge_AP_def APM_def RA3APM_eval
      II_AP_eval assms basic_merge_seed_eval)


subsection \<open>Associativity and Worked Prefixes\<close>

lemma RA3APM_MergeAssoc:
  assumes "MergeAssoc M"
  shows "MergeAssoc (RA3APM M)"
  using assms
  by (auto simp only: MergeAssoc_def RA3APM_eval split: if_splits; blast)

lemma BasicMerge_AP_MergeAssoc: "MergeAssoc BasicMerge_AP"
  by (simp only: BasicMerge_AP_def APM_def comp_apply basic_merge_seed_ADM_eq_H1M;
      intro RA3APM_MergeAssoc RA2M_MergeAssoc H1M_MergeAssoc basic_merge_seed_MergeAssoc)

lemma BasicMerge_AP_parallel_assoc:
  "ap_par_full (ap_par_full P BasicMerge_AP Q) BasicMerge_AP R =
    ap_par_full P BasicMerge_AP (ap_par_full Q BasicMerge_AP R)"
  by (rule ap_par_full_assoc[OF BasicMerge_AP_MergeAssoc])

lemma BasicMerge_AP_prefix_singleton:
  "PrefixSkip_AP a (ades_obs True s0 True {z}) =
    PrefixSkip_RAD a (ades_obs True s0 True {z})"
  using fun_cong[OF H1_PrefixSkip_RAD[of a], of "ades_obs True s0 True {z}"]
  by (simp add: H1_obs)

lemma BasicMerge_AP_prefixes_complete:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
    "\<not> rad_state.wait\<^sub>v z"
  shows "ap_par_full (PrefixSkip_AP a) BasicMerge_AP (PrefixSkip_AP b)
    (ades_obs True s0 c {z}) \<longleftrightarrow>
    (c \<and> a = b \<and> rad_state.tr\<^sub>v z = [a])"
  by (simp only: BasicMerge_AP_parallel_started_zero[OF assms(1,2)]
      BasicMerge_AP_prefix_singleton BasicMerge_RAD_prefix_singleton[OF assms(2)];
      auto simp: basic_merge_state_def assms zero_list_def intro!: exI[where x=z])

lemma basic_merge_seed_not_APM:
  "\<not> ((basic_merge_seed :: ('t::trace, 'e) rad_merge_rel) is APM)"
proof
  let ?M = "basic_merge_seed :: ('t, 'e) rad_merge_rel"
  let ?s0 = "\<lparr>tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = True, \<dots> = ()\<rparr>
    :: ('t, 'e) rad_state"
  let ?p = "ades_normal_output False {}"
  assume h: "?M is APM"
  have fixed: "APM ?M = ?M" by (rule Healthy_if[OF h])
  have eq: "merge_slice BasicMerge_AP ?p ?p (ades_obs True ?s0 True {?s0}) =
    merge_slice ?M ?p ?p (ades_obs True ?s0 True {?s0})"
    by (simp only: BasicMerge_AP_def fixed)
  show False using eq
    by (simp add: BasicMerge_AP_def APM_def RA3APM_eval II_AP_eval basic_merge_seed_eval)
qed

end
