section \<open>Angelic Process Parallel with Full Merge Predicates\<close>

theory utp_ap_parallel_generic
  imports utp_ap_parallel
    "UTP-Reactive-Angelic-Designs.utp_rad_parallel_generic"
begin

text \<open>
  The full merge observes the prior observation, both complete branch
  observations, and the complete final observation.  The parallel operator
  adds no equations relating their termination or waiting flags.

  Waiting is an input condition: when the prior state is waiting, the
  merge supplies the angelic-process identity.  For a nonwaiting prior,
  the merge can depend on both branch observations.
\<close>

abbreviation ap_par_full ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) rad_state ades_merge_rel \<Rightarrow>
   ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design"
where
  "ap_par_full P M Q \<equiv> ades_par_full P M Q"

subsection \<open>Parallel Algebra\<close>

lemma ap_par_full_mono:
  fixes P1 P2 Q1 Q2 :: "('t::trace, 'e) reactive_angelic_design"
    and M1 M2 :: "('t, 'e) rad_state ades_merge_rel"
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2" "M1 \<sqsubseteq> M2"
  shows "ap_par_full P1 M1 Q1 \<sqsubseteq> ap_par_full P2 M2 Q2"
  by (rule ades_par_full_mono[OF assms])

lemma ap_par_full_comm:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_state ades_merge_rel"
  assumes "MergeSym M"
  shows "ap_par_full P M Q = ap_par_full Q M P"
  by (rule ades_par_full_comm[OF assms])

lemma ap_par_full_assoc:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_state ades_merge_rel"
  assumes "MergeAssoc M"
  shows "ap_par_full (ap_par_full P M Q) M R =
    ap_par_full P M (ap_par_full Q M R)"
  by (rule ades_par_full_assoc[OF assms])

lemma ap_par_full_disj_left:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_state ades_merge_rel"
  shows "ap_par_full (P \<or> Q) M R =
    (ap_par_full P M R \<or> ap_par_full Q M R)"
  by (rule ades_par_full_disj_left)

lemma ap_par_full_disj_right:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_state ades_merge_rel"
  shows "ap_par_full P M (Q \<or> R) =
    (ap_par_full P M Q \<or> ap_par_full P M R)"
  by (rule ades_par_full_disj_right)

lemma ap_par_full_false_left:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_state ades_merge_rel"
  shows "ap_par_full false M P = false"
  by (rule ades_par_full_false_left)

lemma ap_par_full_false_right:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_state ades_merge_rel"
  shows "ap_par_full P M false = false"
  by (rule ades_par_full_false_right)

subsection \<open>Waiting Merge Healthiness\<close>

text \<open>
  RA3APM is sufficient but not weakest for RA3AP closure with RA3AP-healthy
  operands. At a started, waiting input such operands cannot produce a branch
  output with ok = False. Merge entries for that impossible branch can be
  removed without changing parallel, although RA3APM requires the II_AP slice
  on those branch pairs too. This is an explanatory mathematical argument,
  not a separate Isabelle counterexample lemma.
\<close>

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

lemma II_AP_full_parallel_wait:
  fixes M :: "('t::trace, 'e) rad_state ades_merge_rel"
    and x :: "('t, 'e) rad_state astate des_vars_ext"
    and out :: "('t, 'e) rad_state achoices des_vars_ext"
  assumes "M is RA3APM"
    "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))"
  shows "ap_par_full II_AP M II_AP (x, out) \<longleftrightarrow>
    II_AP (x, out)"
proof -
  let ?p = "\<lparr>ok\<^sub>v = True,
    ac\<^sub>v = {astate.s\<^sub>v (des_vars.more x)}, \<dots> = ()\<rparr>"
  have witness: "II_AP (x, ?p)"
    by (simp add: II_AP_eval)
  show ?thesis
    by (simp only: ades_par_full_eval RA3APM_healthy_wait[OF assms];
        blast intro: witness)
qed

lemma RA3AP_full_parallel:
  fixes M :: "('t::trace, 'e) rad_state ades_merge_rel"
  assumes "M is RA3APM"
  shows "ap_par_full (RA3AP P) M (RA3AP Q) =
    RA3AP (ap_par_full P M Q)"
proof (rule ext)
  fix w :: "('t, 'e) rad_state astate des_vars_ext \<times>
    ('t, 'e) rad_state achoices des_vars_ext"
  obtain x out where w: "w = (x, out)" by (cases w) auto
  show "ap_par_full (RA3AP P) M (RA3AP Q) w =
    RA3AP (ap_par_full P M Q) w"
  proof (cases "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))")
    case False
    then show ?thesis
      by (simp add: w ades_par_full_eval RA3AP_eval)
  next
    case True
    have identity: "ap_par_full II_AP M II_AP (x, out) = II_AP (x, out)"
      by (rule II_AP_full_parallel_wait[OF assms True])
    then show ?thesis
      by (simp add: w ades_par_full_eval RA3AP_eval True)
  qed
qed

lemma ades_par_full_RA3AP_closure [closure]:
  assumes "P is RA3AP" "Q is RA3AP" "M is RA3APM"
  shows "ap_par_full P M Q is RA3AP"
  using RA3AP_full_parallel[OF assms(3), of P Q] assms(1,2)
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
    by (simp add: A_healthy_components_iff)
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

text \<open>
  APM is sufficient but not weakest for AP closure with AP-healthy operands,
  when merges are compared on all observations. The same unreachable-branch
  deletion described for RA3APM preserves every AP parallel result but breaks
  the RA3APM component of an APM-healthy merge. The component equivalence below
  therefore characterises the chosen merge class, not all AP-closure-preserving
  merges. Non-necessity is explained mathematically, rather than by an
  additional mechanised counterexample.
\<close>

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

lemma ap_par_full_comm_APM:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "MergeSym M"
  shows "ap_par_full P (APM M) Q = ap_par_full Q (APM M) P"
  by (rule ap_par_full_comm[OF APM_MergeSym[OF assms]])

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

subsection \<open>Combined Closure\<close>

lemma ap_par_full_AP_closure_components:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_state ades_merge_rel"
  assumes "P is AP" "Q is AP"
    "M is ADM" "M is RA2M" "M is RA3APM"
  shows "ap_par_full P M Q is AP"
proof -
  let ?NP = "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
    (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t))"
  let ?NQ = "((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f)) \<turnstile>
    (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t))"
  have P_form: "P = RA3AP ?NP"
    by (simp only: AP_RA3AP_design[symmetric] Healthy_if[OF assms(1)])
  have Q_form: "Q = RA3AP ?NQ"
    by (simp only: AP_RA3AP_design[symmetric] Healthy_if[OF assms(2)])
  have NP_H1: "?NP is H1" and NQ_H1: "?NQ is H1"
    using A_is_H1[of ?NP] A_is_H1[of ?NQ]
    by (simp_all only: Healthy_if[OF AP_body_is_A] Healthy_def')
  have body_A: "ap_par_full ?NP M ?NQ is A"
    by (rule ades_par_full_A_closure[OF NP_H1 NQ_H1 assms(3)])
  have body_RA2: "ap_par_full ?NP M ?NQ is RA2"
    by (rule ades_par_full_RA2_closure[OF
          AP_body_is_RA2 AP_body_is_RA2 assms(4)])
  have closed: "RA3AP (ap_par_full ?NP M ?NQ) is AP"
    by (rule RA3AP_AP_intro[OF body_A body_RA2])
  show ?thesis
    apply (subst P_form)
    apply (subst Q_form)
    apply (subst RA3AP_full_parallel[OF assms(5)])
    by (rule closed)
qed

lemma ap_par_full_AP_closure [closure]:
  assumes "P is AP" "Q is AP" "M is APM"
  shows "ap_par_full P M Q is AP"
  using assms
  by (auto simp only: APM_healthy_iff
      intro: ap_par_full_AP_closure_components)

lemma ap_par_full_AP_closure_image [closure]:
  assumes "P is AP" "Q is AP"
  shows "ap_par_full P (APM M) Q is AP"
  by (rule ap_par_full_AP_closure[OF assms APM_healthy])

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

end
