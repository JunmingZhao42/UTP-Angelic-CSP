section \<open>Reactive Angelic Parallel with Full Merge Predicates\<close>

theory utp_rad_parallel_generic
  imports utp_rad_parallel
    "UTP-Angelic-Designs.utp_ades_parallel_generic"
begin

text \<open>
  The merge sees complete branch observations, including termination flags
  and choice sets of reactive states. Merge healthiness provides the closure kit.
  The public operator below restricts the seed to conjunctive branch ok flags
  before applying reactive merge healthiness. Waiting policies remain in M.
\<close>

type_synonym ('t, 'e) rad_merge_rel =
  "(('t, 'e) rad_state) ades_merge_rel"

subsection \<open>Simultaneous trace normalisation\<close>

definition rad_merge_input ::
  "('t::trace, 'e) rad_state astate des_vars_ext \<Rightarrow>
   ('t, 'e) rad_state astate des_vars_ext"
where
  "rad_merge_input x = des_vars.more_update
    (\<lambda>_. astate.s\<^sub>v_update
      (\<lambda>_. rad_zero_trace (astate.s\<^sub>v (des_vars.more x)))
      (des_vars.more x)) x"

definition rad_merge_output ::
  "('t::trace, 'e) rad_state \<Rightarrow>
   ('t, 'e) rad_state achoices des_vars_ext \<Rightarrow>
   ('t, 'e) rad_state achoices des_vars_ext"
where
  "rad_merge_output s0 out = des_vars.more_update
    (\<lambda>_. achoices.ac\<^sub>v_update
      (\<lambda>_. rad_normalise_choices s0 (achoices.ac\<^sub>v (des_vars.more out)))
      (des_vars.more out)) out"

lemma rad_merge_input_zero [simp]:
  "rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more (rad_merge_input x))) = 0"
  by (simp add: rad_merge_input_def rad_zero_trace_def)

lemma rad_merge_input_idem [simp]:
  "rad_merge_input (rad_merge_input x) = rad_merge_input x"
  by (cases x; simp add: rad_merge_input_def rad_zero_trace_def)

lemma rad_normalise_choices_zero:
  assumes "rad_state.tr\<^sub>v s0 = 0"
  shows "rad_normalise_choices s0 X = X"
  using assms
  by (simp add: rad_normalise_choices_def rad_trace_difference_def)

lemma rad_merge_output_zero:
  assumes "rad_state.tr\<^sub>v s0 = 0"
  shows "rad_merge_output s0 out = out"
  using assms
  by (cases out; simp add: rad_merge_output_def rad_normalise_choices_zero)

lemma rad_merge_input_identity:
  assumes "rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x)) = 0"
  shows "rad_merge_input x = x"
proof -
  have zero: "rad_zero_trace s0 = s0"
    if "rad_state.tr\<^sub>v s0 = 0" for s0
    using that by (cases s0; simp add: rad_zero_trace_def)
  show ?thesis
    using assms
    by (cases x; simp add: rad_merge_input_def zero)
qed

lemma rad_merge_output_surj:
  fixes s0 :: "('t::trace, 'e) rad_state"
  obtains out where "rad_merge_output s0 out = target"
proof -
  let ?prepend = "\<lambda>z :: ('t, 'e) rad_state. rad_state.tr\<^sub>v_update
    (\<lambda>t. rad_state.tr\<^sub>v s0 + t) z"
  let ?X = "image ?prepend (achoices.ac\<^sub>v (des_vars.more target))"
  let ?out = "des_vars.more_update (achoices.ac\<^sub>v_update (\<lambda>_. ?X)) target"
  have inj: "inj ?prepend"
  proof (rule injI)
    fix a b :: "('t, 'e) rad_state"
    assume eq: "?prepend a = ?prepend b"
    show "a = b" using eq
      by (cases a; cases b; auto dest: left_cancel_monoid_class.add_left_imp_eq)
  qed
  have "rad_normalise_choices s0 ?X =
      achoices.ac\<^sub>v (des_vars.more target)"
    by (auto simp add: rad_normalise_choices_as_prepend inj_eq[OF inj])
  then have "rad_merge_output s0 ?out = target"
    by (cases target; simp add: rad_merge_output_def)
  then show thesis by (rule that)
qed

lemma RA2_merge_eval:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "RA2 P (x,out) =
    P (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)"
  by (simp add: RA2_def rad_merge_input_def rad_merge_output_def Let_def;
      pred_auto)

definition RA2M ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "RA2M M = (\<lambda>(m,out).
    let x = mrg_prior\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x)
    in ades_merge_eval M (rad_merge_input x)
      (rad_merge_output s0 (mrg_left\<^sub>v m))
      (rad_merge_output s0 (mrg_right\<^sub>v m))
      (rad_merge_output s0 out))"

lemma RA2M_eval:
  "ades_merge_eval (RA2M M) x p q out =
    ades_merge_eval M (rad_merge_input x)
      (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) p)
      (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) q)
      (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)"
  by (simp add: RA2M_def Let_def)

lemma RA2M_zero:
  assumes "rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x)) = 0"
  shows "ades_merge_eval (RA2M M) x p q out = ades_merge_eval M x p q out"
  by (simp add: RA2M_eval rad_merge_input_identity[OF assms]
      rad_merge_output_zero[OF assms])

lemma RA2M_idem: "RA2M (RA2M M) = RA2M M"
  by (simp add: RA2M_def fun_eq_iff Let_def rad_merge_output_zero)

lemma RA2M_Idempotent [closure]: "Idempotent RA2M"
  by (simp add: Idempotent_def RA2M_idem)

lemma RA2M_mono:
  "M \<sqsubseteq> N \<Longrightarrow> RA2M M \<sqsubseteq> RA2M N"
  by (auto simp add: RA2M_def pred_refine_iff Let_def split: prod.splits)

lemma RA2M_Monotonic [closure]: "Monotonic RA2M"
  by (rule MonotonicI, rule RA2M_mono)

lemma RA2M_healthy [closure]: "RA2M M is RA2M"
  by (simp add: Healthy_def' RA2M_idem)

subsection \<open>Healthiness of prior/output slices\<close>

definition RA1M ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where "RA1M = merge_health RA1"

definition RA3M ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where "RA3M = merge_health RA3"

definition CSPA1M ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where "CSPA1M = merge_health CSPA1"

definition CSPA2M ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where "CSPA2M = merge_health CSPA2"

lemma RA1M_idem: "RA1M (RA1M M) = RA1M M"
  unfolding RA1M_def by (rule merge_health_idem, rule RA1_Idempotent)

lemma RA1M_Idempotent [closure]: "Idempotent RA1M"
  by (simp add: Idempotent_def RA1M_idem)

lemma RA1M_mono: "M \<sqsubseteq> N \<Longrightarrow> RA1M M \<sqsubseteq> RA1M N"
  unfolding RA1M_def by (rule merge_health_mono; simp add: RA1_Monotonic)

lemma RA1M_Monotonic [closure]: "Monotonic RA1M"
  by (rule MonotonicI, rule RA1M_mono)

lemma RA3M_idem: "RA3M (RA3M M) = RA3M M"
  unfolding RA3M_def by (rule merge_health_idem, rule RA3_Idempotent)

lemma RA3M_Idempotent [closure]: "Idempotent RA3M"
  by (simp add: Idempotent_def RA3M_idem)

lemma RA3M_mono: "M \<sqsubseteq> N \<Longrightarrow> RA3M M \<sqsubseteq> RA3M N"
  unfolding RA3M_def by (rule merge_health_mono; simp add: RA3_Monotonic)

lemma RA3M_Monotonic [closure]: "Monotonic RA3M"
  by (rule MonotonicI, rule RA3M_mono)

lemma CSPA1M_idem: "CSPA1M (CSPA1M M) = CSPA1M M"
  unfolding CSPA1M_def by (rule merge_health_idem, rule CSPA1_Idempotent)

lemma CSPA1M_Idempotent [closure]: "Idempotent CSPA1M"
  by (simp add: Idempotent_def CSPA1M_idem)

lemma CSPA1M_mono: "M \<sqsubseteq> N \<Longrightarrow> CSPA1M M \<sqsubseteq> CSPA1M N"
  unfolding CSPA1M_def by (rule merge_health_mono; simp add: CSPA1_Monotonic)

lemma CSPA1M_Monotonic [closure]: "Monotonic CSPA1M"
  by (rule MonotonicI, rule CSPA1M_mono)

lemma CSPA2M_idem: "CSPA2M (CSPA2M M) = CSPA2M M"
  unfolding CSPA2M_def by (rule merge_health_idem, rule CSPA2_Idempotent)

lemma CSPA2M_Idempotent [closure]: "Idempotent CSPA2M"
  by (simp add: Idempotent_def CSPA2M_idem)

lemma CSPA2M_mono: "M \<sqsubseteq> N \<Longrightarrow> CSPA2M M \<sqsubseteq> CSPA2M N"
  unfolding CSPA2M_def by (rule merge_health_mono; simp add: CSPA2_Monotonic)

lemma CSPA2M_Monotonic [closure]: "Monotonic CSPA2M"
  by (rule MonotonicI, rule CSPA2M_mono)

lemma RA1M_healthy_iff:
  "M is RA1M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is RA1)"
  by (simp only: RA1M_def merge_health_healthy_iff)

lemma RA3M_healthy_iff:
  "M is RA3M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is RA3)"
  by (simp only: RA3M_def merge_health_healthy_iff)

lemma CSPA1M_healthy_iff:
  "M is CSPA1M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is CSPA1)"
  by (simp only: CSPA1M_def merge_health_healthy_iff)

lemma CSPA2M_H2M: "CSPA2M M = H2M M"
  by (rule merge_slice_ext; simp add: CSPA2M_def H2M_def CSPA2_def)

lemma rad_merge_input_obs [simp]:
  "rad_merge_input \<lparr>ok\<^sub>v = b, s\<^sub>v = s0, \<dots> = ()\<rparr> =
    \<lparr>ok\<^sub>v = b, s\<^sub>v = rad_zero_trace s0, \<dots> = ()\<rparr>"
  by (simp add: rad_merge_input_def)

lemma rad_merge_output_obs [simp]:
  "rad_merge_output s0 \<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr> =
    \<lparr>ok\<^sub>v = c, ac\<^sub>v = rad_normalise_choices s0 X, \<dots> = ()\<rparr>"
  by (simp add: rad_merge_output_def)

lemma RA1_obs:
  "RA1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c (rad_trace_extensions s0 \<inter> X)) \<and>
      rad_trace_extensions s0 \<inter> X \<noteq> {})"
  by (simp add: RA1_def Let_def)

lemma CSPA1_obs:
  "CSPA1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c X) \<or>
      (\<not> b \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}))"
  by (simp add: CSPA1_def RA1_not_ok_eval; pred_auto)

lemma RA3_obs:
  "RA3 P (ades_obs b s0 c X) \<longleftrightarrow>
    (if rad_state.wait\<^sub>v s0 then II_Rac (ades_obs b s0 c X)
      else P (ades_obs b s0 c X))"
  by (simp add: RA3_eval)

lemma rad_normalise_choices_subsets:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "Y \<subseteq> rad_normalise_choices s0 X"
  obtains Z where "Z \<subseteq> X" "rad_normalise_choices s0 Z = Y"
proof -
  let ?Z = "{z \<in> X. rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
    rad_trace_difference s0 z \<in> Y}"
  have sub: "?Z \<subseteq> X" by auto
  have eq: "rad_normalise_choices s0 ?Z = Y"
    using assms by (auto simp add: rad_normalise_choices_def)
  show thesis by (rule that[OF sub eq])
qed

lemma rad_normalise_choices_exists_subset:
  "(\<exists>Y \<subseteq> X. F (rad_normalise_choices s0 Y)) \<longleftrightarrow>
    (\<exists>Y \<subseteq> rad_normalise_choices s0 X. F Y)"
proof
  assume "\<exists>Y \<subseteq> X. F (rad_normalise_choices s0 Y)"
  then obtain Y where sub: "Y \<subseteq> X"
    and f: "F (rad_normalise_choices s0 Y)" by blast
  have "rad_normalise_choices s0 Y \<subseteq> rad_normalise_choices s0 X"
    by (rule rad_normalise_choices_mono[OF sub])
  then show "\<exists>Y \<subseteq> rad_normalise_choices s0 X. F Y"
    using f by blast
next
  assume "\<exists>Y \<subseteq> rad_normalise_choices s0 X. F Y"
  then obtain Y where sub: "Y \<subseteq> rad_normalise_choices s0 X"
    and f: "F Y" by blast
  obtain Z where z: "Z \<subseteq> X" "rad_normalise_choices s0 Z = Y"
    by (rule rad_normalise_choices_subsets[OF sub])
  show "\<exists>Y \<subseteq> X. F (rad_normalise_choices s0 Y)"
    using z f by blast
qed

lemma RA2M_H2M_commute:
  "H2M (RA2M M) = RA2M (H2M M)"
  by (rule merge_slice_ext, rule ades_obs_ext;
      simp add: H2M_def merge_health_eval H2_obs RA2M_eval)

lemma RA2M_PBMHM_commute:
  "PBMHM (RA2M M) = RA2M (PBMHM M)"
  by (rule merge_slice_ext, rule ades_obs_ext;
      simp add: PBMHM_def merge_health_eval PBMH_ades_obs RA2M_eval;
      rule rad_normalise_choices_exists_subset)

lemma RA2M_RA1M_commute:
  "RA1M (RA2M M) = RA2M (RA1M M)"
  by (rule merge_slice_ext, rule ades_obs_ext;
      simp add: RA1M_def merge_health_eval RA1_obs RA2M_eval
        rad_normalise_choices_extensions rad_normalise_choices_nonempty
        rad_zero_trace_extensions)

lemma RA2M_CSPA1M_commute:
  "CSPA1M (RA2M M) = RA2M (CSPA1M M)"
  by (rule merge_slice_ext, rule ades_obs_ext;
      simp add: CSPA1M_def merge_health_eval CSPA1_obs RA2M_eval
        rad_normalise_choices_nonempty rad_zero_trace_extensions)

lemma rad_zero_trace_wait [simp]:
  "rad_state.wait\<^sub>v (rad_zero_trace s0) = rad_state.wait\<^sub>v s0"
  by (simp add: rad_zero_trace_def)

lemma RA2M_RA3M_commute:
  "RA3M (RA2M M) = RA2M (RA3M M)"
  by (rule merge_slice_ext, rule ades_obs_ext;
      simp add: RA3M_def merge_health_eval RA3_obs RA2M_eval
        II_Rac_eval rad_normalise_choices_nonempty rad_zero_trace_in_normalise
        rad_zero_trace_extensions)

lemma RA2M_preserves_PBMHM:
  "M is PBMHM \<Longrightarrow> RA2M M is PBMHM"
  by (simp add: Healthy_def' RA2M_PBMHM_commute)

lemma RA2M_preserves_H2M:
  "M is H2M \<Longrightarrow> RA2M M is H2M"
  by (simp add: Healthy_def' RA2M_H2M_commute)

lemma RA2M_preserves_RA1M:
  "M is RA1M \<Longrightarrow> RA2M M is RA1M"
  by (simp add: Healthy_def' RA2M_RA1M_commute)

lemma RA2M_preserves_CSPA1M:
  "M is CSPA1M \<Longrightarrow> RA2M M is CSPA1M"
  by (simp add: Healthy_def' RA2M_CSPA1M_commute)

lemma RA1M_healthy [closure]: "RA1M M is RA1M"
  by (simp add: Healthy_def' RA1M_idem)

lemma RA3M_healthy [closure]: "RA3M M is RA3M"
  by (simp add: Healthy_def' RA3M_idem)

lemma CSPA1M_healthy [closure]: "CSPA1M M is CSPA1M"
  by (simp add: Healthy_def' CSPA1M_idem)

lemma H2M_preserves_PBMHM:
  "M is PBMHM \<Longrightarrow> H2M M is PBMHM"
  by (simp only: PBMHM_healthy_iff H2M_def merge_health_slice;
      simp add: Healthy_def' PBMH_ades_H2_commute')

lemma CSPA1M_preserves_PBMHM:
  "M is PBMHM \<Longrightarrow> CSPA1M M is PBMHM"
  by (simp only: PBMHM_healthy_iff CSPA1M_def merge_health_slice;
      simp only: Healthy_def';
      blast intro: CSPA1_PBMH_ades_closure)

lemma CSPA1M_preserves_H2M:
  "M is H2M \<Longrightarrow> CSPA1M M is H2M"
  by (simp only: H2M_healthy_iff CSPA1M_def merge_health_slice;
      simp add: Healthy_def' H2_CSPA1_commute)

lemma RA1M_preserves_PBMHM:
  "M is PBMHM \<Longrightarrow> RA1M M is PBMHM"
  by (simp only: PBMHM_healthy_iff RA1M_def merge_health_slice;
      blast intro: RA1_PBMH_ades_closure)

lemma RA1M_preserves_H2M:
  "M is H2M \<Longrightarrow> RA1M M is H2M"
  by (simp only: H2M_healthy_iff RA1M_def merge_health_slice;
      simp add: Healthy_def' H2_RA1_commute)

lemma RA1M_preserves_CSPA1M:
  "M is CSPA1M \<Longrightarrow> RA1M M is CSPA1M"
  by (simp only: CSPA1M_healthy_iff RA1M_def merge_health_slice;
      simp add: Healthy_def'
        RA1_CSPA1_commute[simplified comp_apply, symmetric])

lemma RA3M_preserves_PBMHM:
  "M is PBMHM \<Longrightarrow> RA3M M is PBMHM"
  by (simp only: PBMHM_healthy_iff RA3M_def merge_health_slice;
      blast intro: RA3_PBMH_ades_closure)

lemma RA3M_preserves_H2M:
  "M is H2M \<Longrightarrow> RA3M M is H2M"
  by (simp only: H2M_healthy_iff RA3M_def merge_health_slice;
      simp add: Healthy_def' H2_RA3_commute)

lemma CSPA1_RA3_commute:
  "CSPA1 (RA3 P) = RA3 (CSPA1 P)"
  by (rule ades_obs_ext;
      auto simp add: CSPA1_obs RA3_obs II_Rac_eval split: if_splits)

lemma RA3M_preserves_CSPA1M:
  "M is CSPA1M \<Longrightarrow> RA3M M is CSPA1M"
  by (simp only: CSPA1M_healthy_iff RA3M_def merge_health_slice;
      simp add: Healthy_def' CSPA1_RA3_commute)

lemma RA3M_preserves_RA1M:
  "M is RA1M \<Longrightarrow> RA3M M is RA1M"
  by (simp only: RA1M_healthy_iff RA3M_def merge_health_slice;
      simp add: Healthy_def' RA1_RA3_commute[simplified comp_apply])

lemma RA3M_preserves_RA2M:
  "M is RA2M \<Longrightarrow> RA3M M is RA2M"
  by (simp add: Healthy_def' RA2M_RA3M_commute[symmetric])

subsection \<open>Combined reactive merge healthiness\<close>

definition RADM_full ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "RADM_full = RA3M \<circ> RA2M \<circ> RA1M \<circ> CSPA1M \<circ> H2M \<circ> PBMHM"

lemma RADM_full_components:
  "RADM_full M is PBMHM"
  "RADM_full M is H2M"
  "RADM_full M is CSPA1M"
  "RADM_full M is RA1M"
  "RADM_full M is RA2M"
  "RADM_full M is RA3M"
proof -
  show "RADM_full M is PBMHM"
    unfolding RADM_full_def comp_apply
    by (intro RA3M_preserves_PBMHM RA2M_preserves_PBMHM
        RA1M_preserves_PBMHM CSPA1M_preserves_PBMHM
        H2M_preserves_PBMHM PBMHM_healthy)
  show "RADM_full M is H2M"
    unfolding RADM_full_def comp_apply
    by (intro RA3M_preserves_H2M RA2M_preserves_H2M
        RA1M_preserves_H2M CSPA1M_preserves_H2M H2M_healthy)
  show "RADM_full M is CSPA1M"
    unfolding RADM_full_def comp_apply
    by (intro RA3M_preserves_CSPA1M RA2M_preserves_CSPA1M
        RA1M_preserves_CSPA1M CSPA1M_healthy)
  show "RADM_full M is RA1M"
    unfolding RADM_full_def comp_apply
    by (intro RA3M_preserves_RA1M RA2M_preserves_RA1M RA1M_healthy)
  show "RADM_full M is RA2M"
    unfolding RADM_full_def comp_apply
    by (intro RA3M_preserves_RA2M RA2M_healthy)
  show "RADM_full M is RA3M"
    unfolding RADM_full_def comp_apply
    by (rule RA3M_healthy)
qed

lemma RADM_full_intro:
  assumes "M is PBMHM" "M is H2M" "M is CSPA1M"
    "M is RA1M" "M is RA2M" "M is RA3M"
  shows "M is RADM_full"
  using assms by (simp add: Healthy_def' RADM_full_def)

lemma RADM_full_idem: "RADM_full (RADM_full M) = RADM_full M"
  using RADM_full_intro[OF RADM_full_components]
  by (simp add: Healthy_def')

lemma RADM_full_Idempotent [closure]: "Idempotent RADM_full"
  by (simp add: Idempotent_def RADM_full_idem)

lemma RADM_full_mono:
  "M \<sqsubseteq> N \<Longrightarrow> RADM_full M \<sqsubseteq> RADM_full N"
  unfolding RADM_full_def comp_apply
  by (intro RA3M_mono RA2M_mono RA1M_mono CSPA1M_mono H2M_mono PBMHM_mono)

lemma RADM_full_Monotonic [closure]: "Monotonic RADM_full"
  by (rule MonotonicI, rule RADM_full_mono)

lemma RADM_full_healthy [closure]: "RADM_full M is RADM_full"
  by (simp add: Healthy_def' RADM_full_idem)

lemma RADM_full_healthy_iff:
  "M is RADM_full \<longleftrightarrow>
    ((M is PBMHM) \<and> (M is H2M) \<and> (M is CSPA1M) \<and>
      (M is RA1M) \<and> (M is RA2M) \<and> (M is RA3M))"
proof
  assume h: "M is RADM_full"
  show "(M is PBMHM) \<and> (M is H2M) \<and> (M is CSPA1M) \<and>
      (M is RA1M) \<and> (M is RA2M) \<and> (M is RA3M)"
    using RADM_full_components[of M] h
    by (simp only: Healthy_if; blast)
next
  assume "(M is PBMHM) \<and> (M is H2M) \<and> (M is CSPA1M) \<and>
      (M is RA1M) \<and> (M is RA2M) \<and> (M is RA3M)"
  then show "M is RADM_full" by (blast intro: RADM_full_intro)
qed

lemma CSPA1_healthy_obs_iff:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "P is CSPA1 \<longleftrightarrow>
    (\<forall>s0 c X. rad_trace_extensions s0 \<inter> X \<noteq> {} \<longrightarrow>
      P (ades_obs False s0 c X))"
proof
  assume h: "P is CSPA1"
  show "\<forall>s0 c X. rad_trace_extensions s0 \<inter> X \<noteq> {} \<longrightarrow>
      P (ades_obs False s0 c X)"
    using CSPA1_obs[of P False] h by (simp only: Healthy_if; blast)
next
  assume h: "\<forall>s0 c X. rad_trace_extensions s0 \<inter> X \<noteq> {} \<longrightarrow>
      P (ades_obs False s0 c X)"
  show "P is CSPA1"
    by (rule Healthy_intro, rule ades_obs_ext; simp only: CSPA1_obs;
        insert h; auto; blast)
qed

lemma II_Rac_has_result:
  fixes x :: "('t::trace, 'e) rad_state astate des_vars_ext"
  obtains out where "II_Rac (x,out)"
proof -
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  let ?out = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s0}, \<dots> = ()\<rparr>"
  have "II_Rac (x,?out)" by (simp add: II_Rac_eval)
  then show thesis by (rule that)
qed

lemma RAD_is_CSPA1_full:
  assumes "P is RAD"
  shows "P is CSPA1"
proof -
  have c2: "CSPA1 (RA2 P) = RA2 (CSPA1 P)" for P
    by (rule ades_obs_ext;
        simp add: CSPA1_obs RA2_merge_eval rad_normalise_choices_nonempty
          rad_zero_trace_extensions)
  have "CSPA1 (RAD P) = RAD P"
    by (simp add: RAD_def RA_def RA1_CSPA1_commute[simplified comp_apply, symmetric]
        c2 CSPA1_RA3_commute CSPA1_idem)
  then show ?thesis using assms by (simp add: Healthy_def')
qed

lemma RA2M_MergeSym:
  assumes "MergeSym M"
  shows "MergeSym (RA2M M)"
  using assms by (auto simp add: MergeSym_def RA2M_eval)

lemma RADM_full_MergeSym:
  assumes "MergeSym M"
  shows "MergeSym (RADM_full M)"
  unfolding RADM_full_def comp_apply RA3M_def RA1M_def CSPA1M_def
    H2M_def PBMHM_def
  by (intro merge_health_MergeSym RA2M_MergeSym assms)

subsection \<open>Conjunctive-ok Seed and Healthy Parallel\<close>

lemma OkM_RA1M_commute:
  "(OkM \<circ> RA1M) M = (RA1M \<circ> OkM) M"
  unfolding comp_apply
  by (rule merge_slice_ext, rule ades_obs_ext;
      auto simp: OkM_eval RA1M_def merge_health_eval RA1_obs)

lemmas OkM_RA1M_commute' = OkM_RA1M_commute[simplified comp_apply]

lemma OkM_RA2M_commute:
  "(OkM \<circ> RA2M) M = (RA2M \<circ> OkM) M"
  unfolding comp_apply
  by (rule merge_slice_ext, rule ades_obs_ext;
      simp add: OkM_eval RA2M_eval rad_merge_output_def)

lemmas OkM_RA2M_commute' = OkM_RA2M_commute[simplified comp_apply]

definition rad_ok_body ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where [pred]: "rad_ok_body M = RA1M (CSPA1M (H2M (PBMHM (OkM M))))"

lemma rad_ok_body_obs:
  "merge_slice (rad_ok_body M) p q (ades_obs b s0 c X) \<longleftrightarrow>
    (rad_trace_extensions s0 \<inter> X \<noteq> {} \<and>
     (\<not> b \<or>
      (if des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q
       then c \<and> (\<exists>Y \<subseteq> rad_trace_extensions s0 \<inter> X.
         merge_slice M p q (ades_obs b s0 True Y))
       else (\<exists>Y \<subseteq> rad_trace_extensions s0 \<inter> X.
         merge_slice M p q (ades_obs b s0 False Y)))))"
  by (cases b; cases c; cases "des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q";
      auto simp: rad_ok_body_def RA1M_def CSPA1M_def H2M_def PBMHM_def
        merge_health_eval RA1_obs CSPA1_obs H2_obs PBMH_ades_obs OkM_eval)

lemmas rad_ok_body_eval = rad_ok_body_obs[simplified merge_slice_eval]

lemma ok_merge_extensions_subset_twice:
  assumes "E \<inter> X \<noteq> {}"
  shows "(\<exists>Y \<subseteq> E \<inter> X. E \<inter> Y \<noteq> {} \<and>
      (\<exists>Z \<subseteq> E \<inter> Y. F Z)) \<longleftrightarrow>
    (\<exists>Z \<subseteq> E \<inter> X. F Z)"
proof
  assume "\<exists>Y \<subseteq> E \<inter> X. E \<inter> Y \<noteq> {} \<and>
    (\<exists>Z \<subseteq> E \<inter> Y. F Z)"
  then obtain Y Z where "Y \<subseteq> E \<inter> X" "Z \<subseteq> E \<inter> Y" "F Z"
    by blast
  then have "Z \<subseteq> E \<inter> X" "F Z" by auto
  then show "\<exists>Z \<subseteq> E \<inter> X. F Z" by blast
next
  assume "\<exists>Z \<subseteq> E \<inter> X. F Z"
  with assms show "\<exists>Y \<subseteq> E \<inter> X. E \<inter> Y \<noteq> {} \<and>
    (\<exists>Z \<subseteq> E \<inter> Y. F Z)"
    by (intro exI[of _ "E \<inter> X"]; simp)
qed

lemma rad_ok_body_idem: "rad_ok_body (rad_ok_body M) = rad_ok_body M"
  apply (rule merge_slice_ext, rule ades_obs_ext)
  subgoal for p q b s0 c X
  proof (cases "rad_trace_extensions s0 \<inter> X = {}")
    case True
    then show ?thesis by (simp add: rad_ok_body_eval)
  next
    case False
    have flat:
      "(\<exists>Y \<subseteq> rad_trace_extensions s0 \<inter> X.
        rad_trace_extensions s0 \<inter> Y \<noteq> {} \<and>
        (\<exists>Z \<subseteq> rad_trace_extensions s0 \<inter> Y.
          merge_slice M p q (ades_obs a s0 d Z))) =
       (\<exists>Z \<subseteq> rad_trace_extensions s0 \<inter> X.
          merge_slice M p q (ades_obs a s0 d Z))" for a d
      by (rule ok_merge_extensions_subset_twice[OF False])
    show ?thesis
      using False
      apply (simp only: rad_ok_body_obs)
      by (simp add: flat[simplified] split: if_splits)
  qed
  done

lemma rad_ok_body_RA2M_commute:
  "(rad_ok_body \<circ> RA2M) M = (RA2M \<circ> rad_ok_body) M"
  unfolding comp_apply
  by (simp only: rad_ok_body_def OkM_RA2M_commute'
      RA2M_PBMHM_commute RA2M_H2M_commute RA2M_CSPA1M_commute
      RA2M_RA1M_commute)

lemmas rad_ok_body_RA2M_commute' = rad_ok_body_RA2M_commute[simplified comp_apply]

lemma rad_ok_body_RA3M_absorb:
  "RA3M (rad_ok_body (RA3M M)) = RA3M (rad_ok_body M)"
  by (rule merge_slice_ext, rule ades_obs_ext;
      simp add: RA3M_def merge_health_eval RA3_obs rad_ok_body_eval
        split: if_splits)

definition RADOKM ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where [pred]: "RADOKM = RADM_full \<circ> OkM"

lemma RADOKM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> RADOKM M \<sqsubseteq> RADOKM N"
  unfolding RADOKM_def comp_apply by (intro RADM_full_mono OkM_mono)

lemma RADOKM_Monotonic [closure]: "Monotonic RADOKM"
  by (rule MonotonicI, rule RADOKM_mono)

lemma RADOKM_is_RADM_full [closure]: "RADOKM M is RADM_full"
  by (simp add: RADOKM_def RADM_full_healthy)

lemma RADOKM_form:
  "RADOKM M = RA2M (RA3M (rad_ok_body M))"
  by (simp add: RADOKM_def RADM_full_def rad_ok_body_def RA2M_RA3M_commute)

lemma RADOKM_idem: "RADOKM (RADOKM M) = RADOKM M"
  by (simp only: RADOKM_form rad_ok_body_RA2M_commute'
      RA2M_RA3M_commute RA2M_idem rad_ok_body_RA3M_absorb rad_ok_body_idem)

lemma RADOKM_Idempotent [closure]: "Idempotent RADOKM"
  by (simp add: Idempotent_def RADOKM_idem)

lemma RADOKM_healthy [closure]: "RADOKM M is RADOKM"
  by (simp add: Healthy_def' RADOKM_idem)

lemma RADOKM_MergeSym: "MergeSym M \<Longrightarrow> MergeSym (RADOKM M)"
  unfolding RADOKM_def comp_apply
  by (intro RADM_full_MergeSym OkM_MergeSym)

lemma RADOKM_state_lift:
  "RADOKM (merge_ades_up j) = RADM_full (merge_ades_up j)"
  by (simp add: RADOKM_def)

text \<open>
  The public operator first restricts the supplied merge with OkM and then
  applies the layer healthiness operator. Its choice-set policy comes from
  the supplied merge, subject to that healthiness transformation. The seed's
  conjunction of branch ok flags need not hold globally after completion.
\<close>

abbreviation rad_par_full ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) rad_merge_rel \<Rightarrow>
   ('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t::trace, 'e) reactive_angelic_design"
where "rad_par_full P M Q \<equiv> P \<parallel>\<^bsub>RADOKM M\<^esub> Q"

lemma rad_par_full_eval:
  "rad_par_full P M Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and>
      ades_merge_eval (RADOKM M) x p q out)"
proof -
  have eval: "par_by_merge P N Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval N x p q out)" for N
    by (cases x; cases out;
        simp add: par_by_merge_def par_sep_def; pred_auto; blast)
  show ?thesis by (rule eval)
qed

lemma rad_par_full_PBMH_closure [closure]: "rad_par_full P M Q is PBMH_ades"
proof -
  have healthy: "RADOKM M is PBMHM"
    using RADOKM_is_RADM_full[of M] by (auto simp: RADM_full_healthy_iff)
  have slices: "PBMH_ades (merge_slice (RADOKM M) p q) (ades_obs b s0 c X) =
      merge_slice (RADOKM M) p q (ades_obs b s0 c X)" for p q b s0 c X
    using healthy[unfolded PBMHM_healthy_iff]
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: PBMH_ades_obs rad_par_full_eval;
        use slices[unfolded PBMH_ades_obs merge_slice_eval] in \<open>blast\<close>)
qed

lemma rad_par_full_H2_closure [closure]: "rad_par_full P M Q is H2"
proof -
  have healthy: "RADOKM M is H2M"
    using RADOKM_is_RADM_full[of M] by (auto simp: RADM_full_healthy_iff)
  have slices: "H2 (merge_slice (RADOKM M) p q) (ades_obs b s0 c X) =
      merge_slice (RADOKM M) p q (ades_obs b s0 c X)" for p q b s0 c X
    using healthy[unfolded H2M_healthy_iff]
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: H2_obs rad_par_full_eval;
        use slices[unfolded H2_obs merge_slice_eval] in \<open>blast\<close>)
qed

lemma rad_par_full_RA1_closure [closure]: "rad_par_full P M Q is RA1"
proof -
  have healthy: "RADOKM M is RA1M"
    using RADOKM_is_RADM_full[of M] by (auto simp: RADM_full_healthy_iff)
  have slices: "RA1 (merge_slice (RADOKM M) p q) (ades_obs b s0 c X) =
      merge_slice (RADOKM M) p q (ades_obs b s0 c X)" for p q b s0 c X
    using healthy[unfolded RA1M_healthy_iff]
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: RA1_obs rad_par_full_eval;
        use slices[unfolded RA1_obs merge_slice_eval] in \<open>blast\<close>)
qed

lemma rad_par_full_RA2_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_merge_rel"
  assumes "P is RA2" "Q is RA2"
  shows "rad_par_full P M Q is RA2"
proof -
  have healthy: "RADOKM M is RA2M"
    using RADOKM_is_RADM_full[of M] by (auto simp: RADM_full_healthy_iff)
  have Pnorm: "P (x,out) = P (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x out
    using fun_cong[OF Healthy_if[OF assms(1)], of "(x,out)"]
    by (simp only: RA2_merge_eval)
  have Qnorm: "Q (x,out) = Q (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x out
    using fun_cong[OF Healthy_if[OF assms(2)], of "(x,out)"]
    by (simp only: RA2_merge_eval)
  have Mnorm: "ades_merge_eval (RADOKM M) x p q out =
      ades_merge_eval (RADOKM M) (rad_merge_input x)
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
    show "RA2 (rad_par_full P M Q) (x,out) = rad_par_full P M Q (x,out)"
      by (simp only: RA2_merge_eval rad_par_full_eval;
          subst Pnorm; subst Qnorm; subst Mnorm; rule reindex[symmetric])
  qed
qed

lemma rad_par_full_CSPA1_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is CSPA1" "Q is CSPA1"
  shows "rad_par_full P M Q is CSPA1"
proof -
  have healthy: "RADOKM M is CSPA1M"
    using RADOKM_is_RADM_full[of M] by (auto simp: RADM_full_healthy_iff)
  have P: "P (ades_obs False s0 c X)"
    if "rad_trace_extensions s0 \<inter> X \<noteq> {}" for s0 c X
    using assms(1) that by (simp add: CSPA1_healthy_obs_iff)
  have Q: "Q (ades_obs False s0 c X)"
    if "rad_trace_extensions s0 \<inter> X \<noteq> {}" for s0 c X
    using assms(2) that by (simp add: CSPA1_healthy_obs_iff)
  have merge: "merge_slice (RADOKM M) p q (ades_obs False s0 c X)"
    if "rad_trace_extensions s0 \<inter> X \<noteq> {}" for p q s0 c X
    using healthy that
    by (simp add: CSPA1M_healthy_iff CSPA1_healthy_obs_iff)
  show ?thesis
    unfolding CSPA1_healthy_obs_iff
  proof (intro allI impI)
    fix s0 :: "('t, 'e) rad_state" and c :: bool
      and X :: "('t, 'e) rad_state set"
    assume ne: "rad_trace_extensions s0 \<inter> X \<noteq> {}"
    show "rad_par_full P M Q (ades_obs False s0 c X)"
      unfolding rad_par_full_eval
      using P[OF ne, of c] Q[OF ne, of c]
        merge[OF ne, of "\<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr>"
          "\<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr>" c]
      by auto
  qed
qed

lemma rad_par_full_RA3_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is RA3" "Q is RA3"
  shows "rad_par_full P M Q is RA3"
proof -
  have healthy: "RADOKM M is RA3M"
    using RADOKM_is_RADM_full[of M] by (auto simp: RADM_full_healthy_iff)
  have waiting: "rad_par_full P M Q (x,out) = II_Rac (x,out)"
    if w: "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))" for x out
  proof -
    have Pw: "P (x,p) = II_Rac (x,p)" for p
      using RA3_healthy_wait_eval[OF assms(1) w] .
    have Qw: "Q (x,q) = II_Rac (x,q)" for q
      using RA3_healthy_wait_eval[OF assms(2) w] .
    have Mw: "ades_merge_eval (RADOKM M) x p q out = II_Rac (x,out)" for p q
    proof -
      have "merge_slice (RADOKM M) p q is RA3"
        using healthy by (simp add: RA3M_healthy_iff)
      from RA3_healthy_wait_eval[OF this w]
      show ?thesis by simp
    qed
    obtain y where y: "II_Rac (x,y)" by (rule II_Rac_has_result)
    show ?thesis
      using y by (simp add: rad_par_full_eval Pw Qw Mw; blast)
  qed
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp add: RA3_obs waiting)
qed

lemma rad_par_full_RAD_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "rad_par_full P M Q is RAD"
proof -
  let ?W = "rad_par_full P M Q"
  have pb: "PBMH_ades ?W = ?W"
    using rad_par_full_PBMH_closure by (simp add: Healthy_def')
  have h2: "H2 ?W = ?W"
    using rad_par_full_H2_closure by (simp add: Healthy_def')
  have c1: "CSPA1 ?W = ?W"
    using rad_par_full_CSPA1_closure[OF RAD_is_CSPA1_full[OF assms(1)]
      RAD_is_CSPA1_full[OF assms(2)]] by (simp add: Healthy_def')
  have r1: "RA1 ?W = ?W"
    using rad_par_full_RA1_closure by (simp add: Healthy_def')
  have r2: "RA2 ?W = ?W"
    using rad_par_full_RA2_closure[OF RA_is_RA2[OF RAD_is_RA[OF assms(1)]]
      RA_is_RA2[OF RAD_is_RA[OF assms(2)]]] by (simp add: Healthy_def')
  have r3: "RA3 ?W = ?W"
    using rad_par_full_RA3_closure[OF RA_is_RA3[OF RAD_is_RA[OF assms(1)]]
      RA_is_RA3[OF RAD_is_RA[OF assms(2)]]] by (simp add: Healthy_def')
  show ?thesis
    by (simp add: Healthy_def' RAD_def RA_def CSPA2_def pb h2 c1 r1 r2 r3)
qed

lemma rad_par_full_normalise:
  "rad_par_full P (RADOKM M) Q = rad_par_full P M Q"
  by (simp only: RADOKM_idem)

lemma rad_par_full_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2" "M1 \<sqsubseteq> M2"
  shows "rad_par_full P1 M1 Q1 \<sqsubseteq> rad_par_full P2 M2 Q2"
  using assms(1,2) RADOKM_mono[OF assms(3)]
  by (auto simp: pred_refine_iff rad_par_full_eval split: prod.splits; blast)

lemma rad_par_full_comm:
  assumes "MergeSym M"
  shows "rad_par_full P M Q = rad_par_full Q M P"
  by (rule par_by_merge_comm; use RADOKM_MergeSym[OF assms] in \<open>simp add: MergeSym_iff_swap\<close>)

lemma rad_par_full_comm_iff:
  "MergeSym (RADOKM M) \<longleftrightarrow> (\<forall>P Q. rad_par_full P M Q = rad_par_full Q M P)"
proof
  assume "MergeSym (RADOKM M)"
  then show "\<forall>P Q. rad_par_full P M Q = rad_par_full Q M P"
    by (auto simp: fun_eq_iff rad_par_full_eval MergeSym_def; blast)
next
  assume comm: "\<forall>P Q. rad_par_full P M Q = rad_par_full Q M P"
  show "MergeSym (RADOKM M)"
  proof (unfold MergeSym_def, intro allI)
    fix x p q out
    have eq: "rad_par_full (\<lambda>(x,r). r = p) M (\<lambda>(x,r). r = q) =
        rad_par_full (\<lambda>(x,r). r = q) M (\<lambda>(x,r). r = p)"
      using comm by blast
    from fun_cong[OF eq, of "(x,out)"]
    show "ades_merge_eval (RADOKM M) x p q out = ades_merge_eval (RADOKM M) x q p out"
      by (simp add: rad_par_full_eval)
  qed
qed

lemma rad_par_full_assoc:
  assumes "MergeAssoc (RADOKM M)"
  shows "rad_par_full (rad_par_full P M Q) M R =
    rad_par_full P M (rad_par_full Q M R)"
proof (rule ext, clarify)
  fix x out
  have assoc: "(\<exists>y. ades_merge_eval (RADOKM M) x p q y \<and> ades_merge_eval (RADOKM M) x y r out) =
      (\<exists>y. ades_merge_eval (RADOKM M) x q r y \<and> ades_merge_eval (RADOKM M) x p y out)"
    for p q r
    using assms by (simp add: MergeAssoc_def)
  show "rad_par_full (rad_par_full P M Q) M R (x,out) =
      rad_par_full P M (rad_par_full Q M R) (x,out)"
    unfolding rad_par_full_eval using assoc by blast
qed

lemma rad_par_full_assoc_iff:
  "MergeAssoc (RADOKM M) \<longleftrightarrow>
    (\<forall>P Q R. rad_par_full (rad_par_full P M Q) M R =
      rad_par_full P M (rad_par_full Q M R))"
proof
  assume "MergeAssoc (RADOKM M)"
  then show "\<forall>P Q R. rad_par_full (rad_par_full P M Q) M R =
      rad_par_full P M (rad_par_full Q M R)"
    by (blast intro: rad_par_full_assoc)
next
  assume assoc: "\<forall>P Q R. rad_par_full (rad_par_full P M Q) M R =
      rad_par_full P M (rad_par_full Q M R)"
  show "MergeAssoc (RADOKM M)"
  proof (unfold MergeAssoc_def, intro allI)
    fix x p q r out
    have eq: "rad_par_full
        (rad_par_full (\<lambda>(x,u). u = p) M (\<lambda>(x,u). u = q)) M
        (\<lambda>(x,u). u = r) =
      rad_par_full (\<lambda>(x,u). u = p) M
        (rad_par_full (\<lambda>(x,u). u = q) M (\<lambda>(x,u). u = r))"
      using assoc by blast
    from fun_cong[OF eq, of "(x,out)"]
    show "(\<exists>y. ades_merge_eval (RADOKM M) x p q y \<and> ades_merge_eval (RADOKM M) x y r out) =
        (\<exists>y. ades_merge_eval (RADOKM M) x q r y \<and> ades_merge_eval (RADOKM M) x p y out)"
      by (simp add: rad_par_full_eval)
  qed
qed

lemma rad_par_full_disj_left:
  "rad_par_full (P \<or> Q) M R = (rad_par_full P M R \<or> rad_par_full Q M R)"
  by (auto simp: fun_eq_iff rad_par_full_eval disj_pred_def split: prod.splits)

lemma rad_par_full_disj_right:
  "rad_par_full P M (Q \<or> R) = (rad_par_full P M Q \<or> rad_par_full P M R)"
  by (auto simp: fun_eq_iff rad_par_full_eval disj_pred_def split: prod.splits)

lemma rad_par_full_false_left [simp]: "rad_par_full false M P = false"
  by (rule par_by_merge_left_false)

lemma rad_par_full_false_right [simp]: "rad_par_full P M false = false"
  by (rule par_by_merge_right_false)

end
