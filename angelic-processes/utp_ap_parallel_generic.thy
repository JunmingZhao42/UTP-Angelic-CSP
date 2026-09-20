section \<open>Angelic Process Parallel with Full Merge Predicates\<close>

theory utp_ap_parallel_generic
  imports utp_ap_parallel
    "UTP-Reactive-Angelic-Designs.utp_rad_parallel_generic"
begin

text \<open>
  The full merge observes the prior observation, both complete branch
  observations, and the complete final observation. The parallel operator
  uses OkM followed by AP merge healthiness.

  Waiting is an input condition: when the prior state is waiting, the
  merge supplies the angelic-process identity.  For a nonwaiting prior,
  the merge can depend on both branch observations.
\<close>

subsection \<open>Waiting Merge Healthiness\<close>

definition RA3APM ::
  "('t::trace, 'e) rad_state ades_merge_rel \<Rightarrow>
   ('t, 'e) rad_state ades_merge_rel"
where
  "RA3APM = merge_health RA3AP"

lemma RA3APM_eval:
  "ades_merge_eval (RA3APM M) x p q out \<longleftrightarrow>
   (if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
    then II_AP (x, out) else ades_merge_eval M x p q out)"
  by (simp add: RA3APM_def merge_health_def merge_slice_def RA3AP_eval)

lemma RA3APM_idem: "RA3APM (RA3APM M) = RA3APM M"
  unfolding RA3APM_def
  by (rule merge_health_idem, rule RA3AP_Idempotent)

lemma RA3APM_Idempotent [closure]: "Idempotent RA3APM"
  by (simp add: Idempotent_def RA3APM_idem)

lemma RA3APM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> RA3APM M \<sqsubseteq> RA3APM N"
  unfolding RA3APM_def
  by (rule merge_health_mono; simp add: RA3AP_Monotonic)

lemma RA3APM_Monotonic [closure]: "Monotonic RA3APM"
  by (rule MonotonicI, rule RA3APM_mono)

lemma RA3APM_healthy [closure]: "RA3APM M is RA3APM"
  by (simp add: Healthy_def' RA3APM_idem)

lemma RA3APM_MergeSym:
  assumes "MergeSym M"
  shows "MergeSym (RA3APM M)"
  unfolding RA3APM_def
  by (rule merge_health_MergeSym[OF assms])

lemma RA3APM_healthy_wait:
  assumes "M is RA3APM"
    "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))"
  shows "ades_merge_eval M x p q out \<longleftrightarrow> II_AP (x, out)"
  using RA3APM_eval[of M x p q out] assms
  by (simp add: Healthy_def')

lemma II_AP_is_A [closure]:
  "(II_AP :: ('t::trace, 'e) reactive_angelic_design) is A"
proof -
  have identity: "(II_AP :: ('t, 'e) reactive_angelic_design) = Skip_AD"
    by (simp add: II_AP_design Skip_AD_def arel_to_ades_def
        ades_state_choice_def rdesign_def design_def; pred_auto)
  show ?thesis
    by (rule Healthy_intro; simp only: identity Skip_AD_A)
qed

lemma RA3AP_H1_closure:
  assumes "P is H1"
  shows "RA3AP P is H1"
  using assms
  by (auto simp add: H1_healthy_obs_iff RA3AP_eval II_AP_eval)

lemma H2_RA3AP_commute:
  "H2 (RA3AP P) = RA3AP (H2 P)"
  by (rule ades_obs_ext;
      auto simp add: H2_obs RA3AP_eval II_AP_eval split: if_splits)

lemma RA3AP_A0_closure:
  assumes "P is A0"
  shows "RA3AP P is A0"
  using assms
  by (auto simp add: A0_healthy_obs_iff RA3AP_eval II_AP_eval)

lemma RA3AP_A_closure:
  assumes "P is A"
  shows "RA3AP P is A"
proof -
  have parts: "P is H1" "P is H2" "P is PBMH_ades" "P is A0"
    using assms by (simp_all add: A_healthy_components_iff)
  have closed_H2: "RA3AP P is H2"
    by (simp add: Healthy_def' H2_RA3AP_commute Healthy_if[OF parts(2)])
  show ?thesis
    using RA3AP_H1_closure[OF parts(1)] closed_H2
      RA3AP_PBMH_ades_closure[OF parts(3)] RA3AP_A0_closure[OF parts(4)]
    by (auto simp: A_healthy_components_iff)
qed

lemma RA3APM_preserves_ADM:
  assumes "M is ADM"
  shows "RA3APM M is ADM"
  using assms
  by (auto simp add: ADM_healthy_iff RA3APM_def
      intro: RA3AP_A_closure)

lemma RA2M_preserves_H1M:
  assumes "M is H1M"
  shows "RA2M M is H1M"
  using assms
  by (auto simp add: H1M_healthy_iff H1_healthy_obs_iff
      RA2M_eval rad_merge_input_def rad_merge_output_def)

lemma RA2M_preserves_A0M:
  assumes "M is A0M"
  shows "RA2M M is A0M"
  using assms
  by (auto simp add: A0M_healthy_iff A0_healthy_obs_iff
      RA2M_eval rad_merge_input_def rad_merge_output_def
      rad_normalise_choices_def)

lemma RA2M_preserves_ADM:
  assumes "M is ADM"
  shows "RA2M M is ADM"
  using assms
  by (auto simp add: ADM_components_iff
      intro: RA2M_preserves_H1M RA2M_preserves_H2M
        RA2M_preserves_PBMHM RA2M_preserves_A0M)

lemma RA2M_RA3APM_commute:
  fixes M :: "('t::trace, 'e) rad_state ades_merge_rel"
  shows "RA2M (RA3APM M) = RA3APM (RA2M M)"
proof -
  have wait_zero: "rad_state.wait\<^sub>v (rad_zero_trace s0) =
      rad_state.wait\<^sub>v s0" for s0 :: "('t, 'e) rad_state"
    by (simp add: rad_zero_trace_def)
  show ?thesis
    by (rule merge_slice_ext, rule ades_obs_ext;
        simp add: RA2M_eval RA3APM_eval rad_merge_input_def
          rad_merge_output_def II_AP_eval rad_zero_trace_in_normalise wait_zero)
qed

lemma RA3APM_preserves_RA2M:
  assumes "M is RA2M"
  shows "RA3APM M is RA2M"
  by (simp add: Healthy_def' RA2M_RA3APM_commute Healthy_if[OF assms])

definition APM ::
  "('t::trace, 'e) rad_state ades_merge_rel \<Rightarrow>
   ('t, 'e) rad_state ades_merge_rel"
where
  "APM = RA3APM \<circ> RA2M \<circ> ADM"

lemma APM_preserves_ADM: "APM M is ADM"
  unfolding APM_def comp_apply
  by (intro RA3APM_preserves_ADM RA2M_preserves_ADM ADM_healthy)

lemma APM_preserves_RA2M: "APM M is RA2M"
  unfolding APM_def comp_apply
  by (intro RA3APM_preserves_RA2M RA2M_healthy)

lemma APM_preserves_RA3APM: "APM M is RA3APM"
  by (simp add: APM_def RA3APM_healthy)

lemma APM_idem: "APM (APM M) = APM M"
proof -
  have "APM (APM M) = RA3APM (RA2M (ADM (APM M)))"
    by (simp only: APM_def comp_apply)
  also have "... = APM M"
    by (simp only: Healthy_if[OF APM_preserves_ADM]
        Healthy_if[OF APM_preserves_RA2M]
        Healthy_if[OF APM_preserves_RA3APM])
  finally show ?thesis .
qed

lemma APM_Idempotent [closure]: "Idempotent APM"
  by (simp add: Idempotent_def APM_idem)

lemma APM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> APM M \<sqsubseteq> APM N"
  unfolding APM_def comp_apply
  by (intro RA3APM_mono RA2M_mono ADM_mono)

lemma APM_Monotonic [closure]: "Monotonic APM"
  by (rule MonotonicI, rule APM_mono)

lemma APM_healthy [closure]: "APM M is APM"
  by (simp add: Healthy_def' APM_idem)

lemma APM_MergeSym:
  assumes "MergeSym M"
  shows "MergeSym (APM M)"
  unfolding APM_def comp_apply ADM_def
  by (intro RA3APM_MergeSym RA2M_MergeSym merge_health_MergeSym assms)

lemma APM_healthy_iff:
  "M is APM \<longleftrightarrow>
    ((M is ADM) \<and> (M is RA2M) \<and> (M is RA3APM))"
proof
  assume h: "M is APM"
  show "(M is ADM) \<and> (M is RA2M) \<and> (M is RA3APM)"
    using APM_preserves_ADM[of M] APM_preserves_RA2M[of M]
      APM_preserves_RA3APM[of M]
    by (simp only: Healthy_if[OF h])
next
  assume "(M is ADM) \<and> (M is RA2M) \<and> (M is RA3APM)"
  then show "M is APM"
    by (simp add: Healthy_def' APM_def)
qed

subsection \<open>A Right-Branch Merge Example\<close>

lemma ADM_right_merge_singletons:
  fixes s0 l r :: 's
  shows "merge_slice (ADM (merge_ades_up ades_right_merge))
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    (ades_obs b s0 c X) \<longleftrightarrow> (\<not> b \<or> (c \<and> r \<in> X))"
proof -
  let ?S = "merge_slice (merge_ades_up ades_right_merge)
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>"
  have slice: "?S (ades_obs b s0 c X) \<longleftrightarrow> (c \<and> r \<in> X)"
    for b s0 c X
    by (simp add: merge_ades_up_eval ades_merge_image_right)
  have healthy: "H1 ?S is A"
    unfolding A_healthy_components_iff
  proof (intro conjI)
    show "H1 ?S is H1" by (simp add: Healthy_def' H1_idem)
    show "H1 ?S is H2"
      by (rule Healthy_intro, rule ades_obs_ext;
          simp only: H2_obs H1_obs slice; auto)
    show "H1 ?S is PBMH_ades"
      by (rule Healthy_intro, rule ades_obs_ext;
          simp only: PBMH_ades_obs H1_obs slice;
          blast intro: subset_refl dest: subsetD)
    show "H1 ?S is A0"
      by (simp only: A0_healthy_obs_iff H1_obs slice; simp)
  qed
  have repaired: "A ?S = H1 ?S"
    using A_H1_commute[of ?S] A_is_H1[of ?S] Healthy_if[OF healthy]
    by (simp only: comp_apply)
  show ?thesis
    by (simp only: ADM_def merge_health_slice repaired H1_obs slice)
qed

text \<open>
  In this example the prior is not waiting, the left branch is waiting,
  and the right branch is not waiting.  The repaired right merge accepts
  the right branch's state, including its distinct refusal set.  Therefore
  the combined merge healthiness neither forces the final waiting flag to
  be the disjunction of the branch flags nor restricts this merge to skip.
\<close>

lemma APM_right_merge_wait_example:
  fixes s0 l r :: "(unit list, unit) rad_state"
  defines prior_def:
    "s0 \<equiv> \<lparr>tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = False, \<dots> = ()\<rparr>"
    and left_def:
    "l \<equiv> \<lparr>tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = True, \<dots> = ()\<rparr>"
    and right_def:
    "r \<equiv> \<lparr>tr\<^sub>v = 0, ref\<^sub>v = {()}, wait\<^sub>v = False, \<dots> = ()\<rparr>"
  shows "ades_merge_eval (APM (merge_ades_up ades_right_merge))
    \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>"
    and "rad_state.wait\<^sub>v r \<noteq>
      (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r)"
    and "r \<noteq> s0"
proof -
  have repaired: "ades_merge_eval (ADM (merge_ades_up ades_right_merge))
    \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>"
    by (rule iffD2[OF ADM_right_merge_singletons[simplified merge_slice_eval]]; simp)
  show "ades_merge_eval (APM (merge_ades_up ades_right_merge))
    \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>
    \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>"
    using repaired by (simp add: APM_def RA3APM_eval RA2M_zero prior_def)
  show "rad_state.wait\<^sub>v r \<noteq>
      (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r)"
    and "r \<noteq> s0"
    by (simp_all add: prior_def left_def right_def)
qed

subsection \<open>Conjunctive-ok Seed and Healthy Parallel\<close>

definition APOKM ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where [pred]: "APOKM = APM \<circ> OkM"

lemma APOKM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> APOKM M \<sqsubseteq> APOKM N"
  unfolding APOKM_def comp_apply by (intro APM_mono OkM_mono)

lemma APOKM_Monotonic [closure]: "Monotonic APOKM"
  by (rule MonotonicI, rule APOKM_mono)

lemma APOKM_is_APM [closure]: "APOKM M is APM"
  by (simp add: APOKM_def APM_healthy)

lemma APOKM_form:
  "APOKM M = RA3APM (RA2M (ADOKM M))"
  by (simp add: APOKM_def APM_def ADOKM_def)

lemma APOKM_obs:
  "merge_slice (APOKM M) p q (ades_obs b s0 c X) =
    (if rad_state.wait\<^sub>v s0 then II_AP (ades_obs b s0 c X)
     else merge_slice (ADOKM M) (rad_merge_output s0 p) (rad_merge_output s0 q)
       (ades_obs b (rad_zero_trace s0) c (rad_normalise_choices s0 X)))"
  by (simp add: APOKM_form RA3APM_eval RA2M_eval)

lemma APOKM_active:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "merge_slice (APOKM M) p q (ades_obs b s0 c X) =
    merge_slice (ADOKM M) p q (ades_obs b s0 c X)"
  using assms by (simp add: APOKM_form RA3APM_eval RA2M_zero)

lemma ADOKM_APOKM_active:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "merge_slice (ADOKM (APOKM M)) p q (ades_obs b s0 c X) =
    merge_slice (ADOKM M) p q (ades_obs b s0 c X)"
proof -
  have "merge_slice (ADOKM (APOKM M)) p q (ades_obs b s0 c X) =
    merge_slice (ADOKM (ADOKM M)) p q (ades_obs b s0 c X)"
    using assms
    by (simp add: ADOKM_eval APOKM_active[simplified merge_slice_eval, OF assms])
  then show ?thesis by (simp add: ADOKM_idem)
qed

lemma APOKM_idem: "APOKM (APOKM M) = APOKM M"
  apply (rule merge_slice_ext, rule ades_obs_ext)
  apply (simp only: APOKM_obs)
  subgoal for p q b s0 c X
  proof -
    have zero: "rad_state.tr\<^sub>v (rad_zero_trace s0) = 0"
      by (simp add: rad_zero_trace_def)
    show ?thesis
      by (cases "rad_state.wait\<^sub>v s0";
          simp add: ADOKM_APOKM_active[OF zero, simplified merge_slice_eval])
  qed
  done

lemma APOKM_Idempotent [closure]: "Idempotent APOKM"
  by (simp add: Idempotent_def APOKM_idem)

lemma APOKM_healthy [closure]: "APOKM M is APOKM"
  by (simp add: Healthy_def' APOKM_idem)

lemma APOKM_MergeSym: "MergeSym M \<Longrightarrow> MergeSym (APOKM M)"
  unfolding APOKM_def comp_apply
  by (intro APM_MergeSym OkM_MergeSym)

lemma APOKM_state_lift:
  "APOKM (merge_ades_up j) = APM (merge_ades_up j)"
  by (simp add: APOKM_def)

text \<open>
  The public operator first restricts the supplied merge with OkM and then
  applies the layer healthiness operator. Its choice-set policy comes from
  the supplied merge, subject to that healthiness transformation. The seed's
  conjunction of branch ok flags need not hold globally after completion.
\<close>

abbreviation ap_par_full ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) rad_merge_rel \<Rightarrow>
   ('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t::trace, 'e) reactive_angelic_design"
where "ap_par_full P M Q \<equiv> P \<parallel>\<^bsub>APOKM M\<^esub> Q"

lemma ap_par_full_eval:
  "ap_par_full P M Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and>
      ades_merge_eval (APOKM M) x p q out)"
proof -
  have eval: "par_by_merge P N Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval N x p q out)" for N
    by (cases x; cases out;
        simp add: par_by_merge_def par_sep_def; pred_auto; blast)
  show ?thesis by (rule eval)
qed

lemma ap_par_full_PBMH_closure [closure]: "ap_par_full P M Q is PBMH_ades"
proof -
  have healthy: "APOKM M is PBMHM"
    using APOKM_is_APM[of M] by (auto simp: APM_healthy_iff APM_preserves_ADM ADM_components_iff)
  have slices: "PBMH_ades (merge_slice (APOKM M) p q) (ades_obs b s0 c X) =
      merge_slice (APOKM M) p q (ades_obs b s0 c X)" for p q b s0 c X
    using healthy[unfolded PBMHM_healthy_iff]
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: PBMH_ades_obs ap_par_full_eval;
        use slices[unfolded PBMH_ades_obs merge_slice_eval] in \<open>blast\<close>)
qed

lemma ap_par_full_H2_closure [closure]: "ap_par_full P M Q is H2"
proof -
  have healthy: "APOKM M is H2M"
    using APOKM_is_APM[of M] by (auto simp: APM_healthy_iff APM_preserves_ADM ADM_components_iff)
  have slices: "H2 (merge_slice (APOKM M) p q) (ades_obs b s0 c X) =
      merge_slice (APOKM M) p q (ades_obs b s0 c X)" for p q b s0 c X
    using healthy[unfolded H2M_healthy_iff]
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: H2_obs ap_par_full_eval;
        use slices[unfolded H2_obs merge_slice_eval] in \<open>blast\<close>)
qed

lemma ap_par_full_A0_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  shows "ap_par_full P M Q is A0"
proof -
  have healthy: "APOKM M is A0M"
    using APOKM_is_APM[of M] by (auto simp: APM_healthy_iff APM_preserves_ADM ADM_components_iff)
  show ?thesis
    using healthy[unfolded A0M_healthy_iff A0_healthy_obs_iff]
    by (auto simp only: A0_healthy_obs_iff ap_par_full_eval merge_slice_eval; blast)
qed

lemma ap_par_full_H1_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  assumes "P is H1" "Q is H1"
  shows "ap_par_full P M Q is H1"
proof -
  have healthy: "APOKM M is H1M"
    using APOKM_is_APM[of M] by (auto simp: APM_healthy_iff APM_preserves_ADM ADM_components_iff)
  show ?thesis
    using healthy[unfolded H1M_healthy_iff H1_healthy_obs_iff] assms[unfolded H1_healthy_obs_iff]
    by (auto simp only: H1_healthy_obs_iff ap_par_full_eval merge_slice_eval; blast)
qed

lemma ap_par_full_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "ap_par_full P M Q is A"
  using ap_par_full_H1_closure[OF assms] ap_par_full_H2_closure
    ap_par_full_PBMH_closure ap_par_full_A0_closure
  by (auto simp: A_healthy_components_iff)

lemma ap_par_full_RA2_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_merge_rel"
  assumes "P is RA2" "Q is RA2"
  shows "ap_par_full P M Q is RA2"
proof -
  have healthy: "APOKM M is RA2M"
    using APOKM_is_APM[of M] by (auto simp: APM_healthy_iff ADM_components_iff)
  have Pnorm: "P (x,out) = P (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x out
    using fun_cong[OF Healthy_if[OF assms(1)], of "(x,out)"]
    by (simp only: RA2_merge_eval)
  have Qnorm: "Q (x,out) = Q (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x out
    using fun_cong[OF Healthy_if[OF assms(2)], of "(x,out)"]
    by (simp only: RA2_merge_eval)
  have Mnorm: "ades_merge_eval (APOKM M) x p q out =
      ades_merge_eval (APOKM M) (rad_merge_input x)
        (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) p)
        (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) q)
        (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x p q out
    using arg_cong[where f="\<lambda>N. ades_merge_eval N x p q out",
      OF Healthy_if[OF healthy]]
    by (simp only: RA2M_eval)
  have reindex: "(\<exists>p q. F (rad_merge_output s0 p) (rad_merge_output s0 q)) =
      (\<exists>p q. F p q)" for F and s0 :: "('t, 'e) rad_state"
    by (metis rad_merge_output_surj)
  show ?thesis
  proof (rule Healthy_intro, rule ext, clarify)
    fix x out
    show "RA2 (ap_par_full P M Q) (x,out) = ap_par_full P M Q (x,out)"
      by (simp only: RA2_merge_eval ap_par_full_eval;
          subst Pnorm; subst Qnorm; subst Mnorm; rule reindex[symmetric])
  qed
qed

lemma II_AP_has_result:
  fixes x :: "('t::trace, 'e) rad_state astate des_vars_ext"
  obtains out where "II_AP (x,out)"
proof -
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  have "II_AP (x,\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s0}, \<dots> = ()\<rparr>)"
    by (simp add: II_AP_eval)
  then show thesis by (rule that)
qed

lemma ap_par_full_RA3AP_closure [closure]:
  assumes "P is RA3AP" "Q is RA3AP"
  shows "ap_par_full P M Q is RA3AP"
proof -
  have healthy: "APOKM M is RA3APM"
    using APOKM_is_APM[of M] by (auto simp: APM_healthy_iff ADM_components_iff)
  have waiting: "ap_par_full P M Q (x,out) = II_AP (x,out)"
    if w: "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))" for x out
  proof -
    have Pw: "P (x,p) = II_AP (x,p)" for p
      using RA3AP_healthy_wait_eval[OF assms(1) w] .
    have Qw: "Q (x,q) = II_AP (x,q)" for q
      using RA3AP_healthy_wait_eval[OF assms(2) w] .
    have Mw: "ades_merge_eval (APOKM M) x p q out = II_AP (x,out)" for p q
    proof -
      have "merge_slice (APOKM M) p q is RA3AP"
        using healthy by (simp add: RA3APM_def merge_health_healthy_iff)
      from RA3AP_healthy_wait_eval[OF this w]
      show ?thesis by simp
    qed
    obtain y where y: "II_AP (x,y)" by (rule II_AP_has_result)
    show ?thesis
      using y by (simp add: ap_par_full_eval Pw Qw Mw; blast)
  qed
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp add: RA3AP_eval waiting)
qed

lemma AP_is_RA2:
  assumes "P is AP"
  shows "P is RA2"
proof -
  have "RA2 (AP P) = AP P"
    by (simp only: AP_RA3AP_design RA2_RA3AP_commute[simplified comp_apply]
        Healthy_if[OF AP_body_is_RA2])
  then show ?thesis using assms by (simp add: Healthy_def')
qed

lemma ap_par_full_AP_closure [closure]:
  assumes "P is AP" "Q is AP"
  shows "ap_par_full P M Q is AP"
proof -
  have ph: "P is H1" and qh: "Q is H1"
    using AP_is_H[OF assms(1)] AP_is_H[OF assms(2)]
    by (auto intro: H_implies_H1)
  have a: "ap_par_full P M Q is A"
    by (rule ap_par_full_A_closure[OF ph qh])
  have r2: "ap_par_full P M Q is RA2"
    by (rule ap_par_full_RA2_closure[OF AP_is_RA2[OF assms(1)] AP_is_RA2[OF assms(2)]])
  have r3: "ap_par_full P M Q is RA3AP"
    by (rule ap_par_full_RA3AP_closure[OF AP_is_RA3AP[OF assms(1)] AP_is_RA3AP[OF assms(2)]])
  from RA3AP_AP_intro[OF a r2] show ?thesis
    by (simp only: Healthy_if[OF r3])
qed

lemma ap_par_full_normalise:
  "ap_par_full P (APOKM M) Q = ap_par_full P M Q"
  by (simp only: APOKM_idem)

lemma ap_par_full_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2" "M1 \<sqsubseteq> M2"
  shows "ap_par_full P1 M1 Q1 \<sqsubseteq> ap_par_full P2 M2 Q2"
  using assms(1,2) APOKM_mono[OF assms(3)]
  by (auto simp: pred_refine_iff ap_par_full_eval split: prod.splits; blast)

lemma ap_par_full_comm:
  assumes "MergeSym M"
  shows "ap_par_full P M Q = ap_par_full Q M P"
  by (rule par_by_merge_comm; use APOKM_MergeSym[OF assms] in \<open>simp add: MergeSym_iff_swap\<close>)

lemma ap_par_full_comm_iff:
  "MergeSym (APOKM M) \<longleftrightarrow> (\<forall>P Q. ap_par_full P M Q = ap_par_full Q M P)"
proof
  assume "MergeSym (APOKM M)"
  then show "\<forall>P Q. ap_par_full P M Q = ap_par_full Q M P"
    by (auto simp: fun_eq_iff ap_par_full_eval MergeSym_def; blast)
next
  assume comm: "\<forall>P Q. ap_par_full P M Q = ap_par_full Q M P"
  show "MergeSym (APOKM M)"
  proof (unfold MergeSym_def, intro allI)
    fix x p q out
    have eq: "ap_par_full (\<lambda>(x,r). r = p) M (\<lambda>(x,r). r = q) =
        ap_par_full (\<lambda>(x,r). r = q) M (\<lambda>(x,r). r = p)"
      using comm by blast
    from fun_cong[OF eq, of "(x,out)"]
    show "ades_merge_eval (APOKM M) x p q out = ades_merge_eval (APOKM M) x q p out"
      by (simp add: ap_par_full_eval)
  qed
qed

lemma ap_par_full_assoc:
  assumes "MergeAssoc (APOKM M)"
  shows "ap_par_full (ap_par_full P M Q) M R =
    ap_par_full P M (ap_par_full Q M R)"
proof (rule ext, clarify)
  fix x out
  have assoc: "(\<exists>y. ades_merge_eval (APOKM M) x p q y \<and> ades_merge_eval (APOKM M) x y r out) =
      (\<exists>y. ades_merge_eval (APOKM M) x q r y \<and> ades_merge_eval (APOKM M) x p y out)"
    for p q r
    using assms by (simp add: MergeAssoc_def)
  show "ap_par_full (ap_par_full P M Q) M R (x,out) =
      ap_par_full P M (ap_par_full Q M R) (x,out)"
    unfolding ap_par_full_eval using assoc by blast
qed

lemma ap_par_full_assoc_iff:
  "MergeAssoc (APOKM M) \<longleftrightarrow>
    (\<forall>P Q R. ap_par_full (ap_par_full P M Q) M R =
      ap_par_full P M (ap_par_full Q M R))"
proof
  assume "MergeAssoc (APOKM M)"
  then show "\<forall>P Q R. ap_par_full (ap_par_full P M Q) M R =
      ap_par_full P M (ap_par_full Q M R)"
    by (blast intro: ap_par_full_assoc)
next
  assume assoc: "\<forall>P Q R. ap_par_full (ap_par_full P M Q) M R =
      ap_par_full P M (ap_par_full Q M R)"
  show "MergeAssoc (APOKM M)"
  proof (unfold MergeAssoc_def, intro allI)
    fix x p q r out
    have eq: "ap_par_full
        (ap_par_full (\<lambda>(x,u). u = p) M (\<lambda>(x,u). u = q)) M
        (\<lambda>(x,u). u = r) =
      ap_par_full (\<lambda>(x,u). u = p) M
        (ap_par_full (\<lambda>(x,u). u = q) M (\<lambda>(x,u). u = r))"
      using assoc by blast
    from fun_cong[OF eq, of "(x,out)"]
    show "(\<exists>y. ades_merge_eval (APOKM M) x p q y \<and> ades_merge_eval (APOKM M) x y r out) =
        (\<exists>y. ades_merge_eval (APOKM M) x q r y \<and> ades_merge_eval (APOKM M) x p y out)"
      by (simp add: ap_par_full_eval)
  qed
qed

lemma ap_par_full_disj_left:
  "ap_par_full (P \<or> Q) M R = (ap_par_full P M R \<or> ap_par_full Q M R)"
  by (auto simp: fun_eq_iff ap_par_full_eval disj_pred_def split: prod.splits)

lemma ap_par_full_disj_right:
  "ap_par_full P M (Q \<or> R) = (ap_par_full P M Q \<or> ap_par_full P M R)"
  by (auto simp: fun_eq_iff ap_par_full_eval disj_pred_def split: prod.splits)

lemma ap_par_full_false_left [simp]: "ap_par_full false M P = false"
  by (rule par_by_merge_left_false)

lemma ap_par_full_false_right [simp]: "ap_par_full P M false = false"
  by (rule par_by_merge_right_false)

end
