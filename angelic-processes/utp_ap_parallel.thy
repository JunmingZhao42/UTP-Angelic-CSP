section \<open>Angelic Process Parallel-by-Merge\<close>

theory utp_ap_parallel
  imports utp_ap_ops
    "UTP-Reactive-Angelic-Designs.utp_rad_parallel"
begin

text \<open>
  The full merge observes the prior observation, both complete branch
  observations, and the complete final observation. The parallel operator
  uses the conjunctive-ok AD completion, trace normalisation, and the
  process waiting condition directly.

  Waiting is an input condition: when the prior state is waiting, the
  merge supplies the angelic-process identity.  For a nonwaiting prior,
  the merge can depend on both branch observations.
\<close>

subsection \<open>Waiting Merge Healthiness\<close>

definition RA3APM ::
  "('t::trace, 'e) rad_state ades_merge_rel \<Rightarrow>
   ('t, 'e) rad_state ades_merge_rel"
where
  "RA3APM M = (\<lambda>(m,out).
    if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m)))
    then II_AP (mrg_prior\<^sub>v m,out) else M (m,out))"

lemma RA3APM_eval:
  "ades_merge_eval (RA3APM M) x p q out \<longleftrightarrow>
   (if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
    then II_AP (x, out) else ades_merge_eval M x p q out)"
  by (simp add: RA3APM_def)


lemma RA3APM_idem: "RA3APM (RA3APM M) = RA3APM M"
  by (auto simp: RA3APM_def fun_eq_iff)

lemma RA3APM_Idempotent [closure]: "Idempotent RA3APM"
  by (simp add: Idempotent_def RA3APM_idem)

lemma RA3APM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> RA3APM M \<sqsubseteq> RA3APM N"
  by (auto simp: RA3APM_def pred_refine_iff split: prod.splits)

lemma RA3APM_Monotonic [closure]: "Monotonic RA3APM"
  by (rule MonotonicI, rule RA3APM_mono)

lemma RA3APM_healthy [closure]: "RA3APM M is RA3APM"
  by (simp add: Healthy_def' RA3APM_idem)

lemma RA3APM_SymMerge:
  "M is SymMerge \<Longrightarrow> (RA3APM M) is SymMerge"
  by (auto simp: SymMerge_ades RA3APM_eval)

lemma RA3APM_healthy_wait:
  assumes "M is RA3APM"
    "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))"
  shows "ades_merge_eval M x p q out \<longleftrightarrow> II_AP (x, out)"
  using RA3APM_eval[of M x p q out] assms
  by (simp add: Healthy_def')

lemma RA2M_RA3APM_commute:
  fixes M :: "('t::trace, 'e) rad_state ades_merge_rel"
  shows "RA2M (RA3APM M) = RA3APM (RA2M M)"
proof -
  have wait_zero: "rad_state.wait\<^sub>v (rad_zero_trace s0) =
      rad_state.wait\<^sub>v s0" for s0 :: "('t, 'e) rad_state"
    by (simp add: rad_zero_trace_def)
  show ?thesis
    by (rule ades_merge_ext, rule ades_obs_ext;
        simp add: RA2M_eval RA3APM_eval rad_merge_input_def
          rad_merge_output_def II_AP_eval rad_zero_trace_in_normalise wait_zero)
qed

lemma RA3APM_preserves_RA2M:
  assumes "M is RA2M"
  shows "RA3APM M is RA2M"
  by (simp add: Healthy_def' RA2M_RA3APM_commute Healthy_if[OF assms])


subsection \<open>Conjunctive-ok process merge\<close>

definition APOKM ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "APOKM M = RA3APM (RA2M (A0m (A1m (\<lambda>(m,out).
    des_vars.ok\<^sub>v out =
      (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
    M (m,out)))))"

lemmas APOKM_form = APOKM_def

lemma APOKM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> APOKM M \<sqsubseteq> APOKM N"
  unfolding APOKM_def
  by (intro RA3APM_mono RA2M_mono A0m_mono A1m_mono;
      auto simp: pred_refine_iff)

lemma APOKM_Monotonic [closure]: "Monotonic APOKM"
  by (rule MonotonicI, rule APOKM_mono)

lemma APOKM_obs:
  "(\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) (ades_obs b s0 c X) =
    (if rad_state.wait\<^sub>v s0 then II_AP (ades_obs b s0 c X)
     else \<not> b \<or>
       (if des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q
        then c \<and> rad_normalise_choices s0 X \<noteq> {} \<and>
          (\<exists>Y\<subseteq>rad_normalise_choices s0 X.
            (\<lambda>(x,out). ades_merge_eval M x (rad_merge_output s0 p)
              (rad_merge_output s0 q) out) (ades_obs True (rad_zero_trace s0) True Y))
        else (\<exists>Y\<subseteq>rad_normalise_choices s0 X.
          (\<lambda>(x,out). ades_merge_eval M x (rad_merge_output s0 p)
            (rad_merge_output s0 q) out) (ades_obs True (rad_zero_trace s0) False Y))))"
  by (auto simp: APOKM_def RA3APM_eval RA2M_eval A0m_design A1m_design
      A_def[symmetric] A_obs rad_merge_output_def
      A0m_def A1m_def A0_obs A1_obs Let_def)

lemmas APOKM_eval = APOKM_obs[simplified]

lemma APOKM_active:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "(\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) (ades_obs b s0 c X) =
    (\<not> b \<or>
      (if des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q
       then c \<and> X \<noteq> {} \<and>
         (\<exists>Y\<subseteq>X. (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs True s0 True Y))
       else (\<exists>Y\<subseteq>X. (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs True s0 False Y))))"
  using assms
  by (auto simp: APOKM_def RA3APM_eval RA2M_zero A0m_design A1m_design
      A_def[symmetric] A_obs A0m_def A1m_def A0_obs A1_obs Let_def)

lemma APOKM_idem: "APOKM (APOKM M) = APOKM M"
  apply (rule ades_merge_ext, rule ades_obs_ext)
  subgoal for p q b s0 c X
  proof -
    have zero: "rad_state.tr\<^sub>v (rad_zero_trace s0) = 0"
      by (simp add: rad_zero_trace_def)
    have wait_zero: "rad_state.wait\<^sub>v (rad_zero_trace s0) = rad_state.wait\<^sub>v s0"
      by (simp add: rad_zero_trace_def)
    show ?thesis
      apply (subst APOKM_obs)
      apply (subst (3) APOKM_obs)
      apply (cases "rad_state.wait\<^sub>v s0")
       apply simp
      apply (simp add: APOKM_active[OF zero, simplified] wait_zero rad_merge_output_def
          split: if_splits)
      by blast
  qed
  done

lemma APOKM_Idempotent [closure]: "Idempotent APOKM"
  by (simp add: Idempotent_def APOKM_idem)

lemma APOKM_healthy [closure]: "APOKM M is APOKM"
  by (simp add: Healthy_def' APOKM_idem)


lemma APOKM_SymMerge:
  assumes "M is SymMerge"
  shows "(APOKM M) is SymMerge"
  unfolding APOKM_def
  apply (intro RA3APM_SymMerge RA2M_SymMerge)
  unfolding SymMerge_ades_observations
  apply (simp only: A0m_design A1m_design)
  using assms
  by (auto simp: SymMerge_ades fun_eq_iff conj_commute)

lemma RA3APM_design:
  "(\<lambda>(x,out). ades_merge_eval (RA3APM M) x p q out) =
    RA3AP (\<lambda>(x,out). ades_merge_eval M x p q out)"
  by (simp add: fun_eq_iff RA3APM_eval RA3AP_eval)

lemma RA2M_A_design_PBMH:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  shows "(\<lambda>(x,out). ades_merge_eval (RA2M (A0m (A1m M))) x p q out) is PBMH_ades"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c X
  let ?p = "rad_merge_output s0 p"
  let ?q = "rad_merge_output s0 q"
  let ?F = "\<lambda>Y. ades_merge_eval (A0m (A1m M))
    \<lparr>ok\<^sub>v = b, s\<^sub>v = rad_zero_trace s0, \<dots> = ()\<rparr> ?p ?q
    \<lparr>ok\<^sub>v = c, ac\<^sub>v = Y, \<dots> = ()\<rparr>"
  have h: "(\<lambda>(x,out). ades_merge_eval (A0m (A1m M)) x ?p ?q out) is PBMH_ades"
    by (rule A_is_PBMH_ades;
        simp add: A0m_design A1m_design A_def[symmetric] Healthy_def' A_idem)
  have closed: "(\<exists>Y \<subseteq> rad_normalise_choices s0 X. ?F Y) =
      ?F (rad_normalise_choices s0 X)"
    using fun_cong[OF Healthy_if[OF h],
      of "ades_obs b (rad_zero_trace s0) c (rad_normalise_choices s0 X)"]
    by (simp only: PBMH_ades_obs case_prod_conv)
  show "PBMH_ades (\<lambda>(x,out). ades_merge_eval (RA2M (A0m (A1m M))) x p q out)
      (ades_obs b s0 c X) =
    (\<lambda>(x,out). ades_merge_eval (RA2M (A0m (A1m M))) x p q out) (ades_obs b s0 c X)"
    by (simp only: PBMH_ades_obs case_prod_conv RA2M_eval
        rad_merge_input_obs rad_merge_output_obs astate.select_convs des_vars.select_convs;
        simp only: rad_normalise_choices_exists_subset[of X ?F s0] closed)
qed

lemma APOKM_design_A [closure]:
  "(\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) is A"
proof -
  let ?S = "\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out"
  have h1: "?S is H1"
    by (simp add: H1_healthy_obs_iff APOKM_eval II_AP_eval)
  have h2: "?S is H2"
    by (rule Healthy_intro, rule ades_obs_ext;
        auto simp: H2_obs APOKM_eval II_AP_eval
          split: if_splits)
  have pb: "?S is PBMH_ades"
    unfolding APOKM_def RA3APM_design
    by (rule RA3AP_PBMH_ades_closure, rule RA2M_A_design_PBMH)
  have a0: "?S is A0"
    by (simp add: A0_healthy_obs_iff APOKM_eval II_AP_eval
        rad_normalise_choices_def split: if_splits)
  show ?thesis
    using h1 h2 pb a0 by (simp add: A_healthy_components_iff)
qed

lemma APOKM_RA2M [closure]: "APOKM M is RA2M"
  unfolding APOKM_def
  by (intro RA3APM_preserves_RA2M RA2M_healthy)

lemma APOKM_RA3APM [closure]: "APOKM M is RA3APM"
  by (simp add: APOKM_def RA3APM_healthy)

text \<open>
  The public operator first adds the conjunctive termination constraint and then
  applies the layer healthiness operator. Its choice-set policy comes from
  the supplied merge, subject to that healthiness transformation. The seed's
  conjunction of branch ok flags need not hold globally after completion.
\<close>

abbreviation ap_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) rad_merge_rel \<Rightarrow>
   ('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t::trace, 'e) reactive_angelic_design"
where "ap_par P M Q \<equiv> P \<parallel>\<^bsub>APOKM M\<^esub> Q"

lemma ap_par_eval:
  "ap_par P M Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and>
      ades_merge_eval (APOKM M) x p q out)"
proof -
  have eval: "par_by_merge P N Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval N x p q out)" for N
    by (cases x; cases out;
        simp add: par_by_merge_def par_sep_def; pred_auto; blast)
  show ?thesis by (rule eval)
qed

lemma ap_par_PBMH_closure [closure]: "ap_par P M Q is PBMH_ades"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) is PBMH_ades"
    for p q
    using APOKM_design_A[of M p q] by (simp add: A_healthy_components_iff)
  have slices: "PBMH_ades ((\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out)) (ades_obs b s0 c X) =
      (\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) (ades_obs b s0 c X)" for p q b s0 c X
    using healthy
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: PBMH_ades_obs ap_par_eval;
        use slices[unfolded PBMH_ades_obs case_prod_conv] in \<open>blast\<close>)
qed

lemma ap_par_H2_closure [closure]: "ap_par P M Q is H2"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) is H2"
    for p q
    using APOKM_design_A[of M p q] by (simp add: A_healthy_components_iff)
  have slices: "H2 ((\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out)) (ades_obs b s0 c X) =
      (\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) (ades_obs b s0 c X)" for p q b s0 c X
    using healthy
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: H2_obs ap_par_eval;
        use slices[unfolded H2_obs case_prod_conv] in \<open>blast\<close>)
qed

lemma ap_par_A0_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  shows "ap_par P M Q is A0"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) is A0"
    for p q
    using APOKM_design_A[of M p q] by (simp add: A_healthy_components_iff)
  show ?thesis
    using healthy[unfolded A0_healthy_obs_iff]
    by (auto simp only: A0_healthy_obs_iff ap_par_eval case_prod_conv; blast)
qed

lemma ap_par_H1_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  assumes "P is H1" "Q is H1"
  shows "ap_par P M Q is H1"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (APOKM M) x p q out) is H1"
    for p q
    using APOKM_design_A[of M p q] by (simp add: A_healthy_components_iff)
  show ?thesis
    using healthy[unfolded H1_healthy_obs_iff] assms[unfolded H1_healthy_obs_iff]
    by (auto simp only: H1_healthy_obs_iff ap_par_eval case_prod_conv; blast)
qed

lemma ap_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "ap_par P M Q is A"
  using ap_par_H1_closure[OF assms] ap_par_H2_closure
    ap_par_PBMH_closure ap_par_A0_closure
  by (auto simp: A_healthy_components_iff)

lemma ap_par_RA2_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_merge_rel"
  assumes "P is RA2" "Q is RA2"
  shows "ap_par P M Q is RA2"
proof -
  have healthy: "APOKM M is RA2M" by (rule APOKM_RA2M)
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
    show "RA2 (ap_par P M Q) (x,out) = ap_par P M Q (x,out)"
      by (simp only: RA2_merge_eval ap_par_eval;
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

lemma ap_par_RA3AP_closure [closure]:
  assumes "P is RA3AP" "Q is RA3AP"
  shows "ap_par P M Q is RA3AP"
proof -
  have healthy: "APOKM M is RA3APM" by (rule APOKM_RA3APM)
  have waiting: "ap_par P M Q (x,out) = II_AP (x,out)"
    if w: "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))" for x out
  proof -
    have Pw: "P (x,p) = II_AP (x,p)" for p
      using RA3AP_healthy_wait_eval[OF assms(1) w] .
    have Qw: "Q (x,q) = II_AP (x,q)" for q
      using RA3AP_healthy_wait_eval[OF assms(2) w] .
    have Mw: "ades_merge_eval (APOKM M) x p q out = II_AP (x,out)" for p q
      by (simp add: APOKM_def RA3APM_eval w)
    obtain y where y: "II_AP (x,y)" by (rule II_AP_has_result)
    show ?thesis
      using y by (simp add: ap_par_eval Pw Qw Mw; blast)
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

lemma ap_par_AP_closure [closure]:
  assumes "P is AP" "Q is AP"
  shows "ap_par P M Q is AP"
proof -
  have ph: "P is H1" and qh: "Q is H1"
    using AP_is_H[OF assms(1)] AP_is_H[OF assms(2)]
    by (auto intro: H_implies_H1)
  have a: "ap_par P M Q is A"
    by (rule ap_par_A_closure[OF ph qh])
  have r2: "ap_par P M Q is RA2"
    by (rule ap_par_RA2_closure[OF AP_is_RA2[OF assms(1)] AP_is_RA2[OF assms(2)]])
  have r3: "ap_par P M Q is RA3AP"
    by (rule ap_par_RA3AP_closure[OF AP_is_RA3AP[OF assms(1)] AP_is_RA3AP[OF assms(2)]])
  from RA3AP_AP_intro[OF a r2] show ?thesis
    by (simp only: Healthy_if[OF r3])
qed

lemma ap_par_normalise:
  "ap_par P (APOKM M) Q = ap_par P M Q"
  by (simp only: APOKM_idem)

lemma ap_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2" "M1 \<sqsubseteq> M2"
  shows "ap_par P1 M1 Q1 \<sqsubseteq> ap_par P2 M2 Q2"
  using assms(1,2) APOKM_mono[OF assms(3)]
  by (auto simp: pred_refine_iff ap_par_eval split: prod.splits; blast)

lemma ap_par_comm:
  assumes "M is SymMerge"
  shows "ap_par P M Q = ap_par Q M P"
  by (rule par_by_merge_comm; use APOKM_SymMerge[OF assms] in \<open>simp add: Healthy_def'\<close>)

lemma ap_par_comm_iff:
  "APOKM M is SymMerge \<longleftrightarrow> (\<forall>P Q. ap_par P M Q = ap_par Q M P)"
  by (rule ades_par_comm_iff)

lemma ap_par_assoc:
  assumes "APOKM M is SymMerge" "AssocMerge (APOKM M)"
  shows "ap_par (ap_par P M Q) M R =
    ap_par P M (ap_par Q M R)"
  by (rule ades_par_assoc[OF assms])

lemma ap_par_assoc_iff:
  assumes "APOKM M is SymMerge"
  shows "AssocMerge (APOKM M) \<longleftrightarrow>
    (\<forall>P Q R. ap_par (ap_par P M Q) M R =
      ap_par P M (ap_par Q M R))"
  by (rule ades_par_assoc_iff[OF assms])

lemma ap_par_disj_left:
  "ap_par (P \<or> Q) M R = (ap_par P M R \<or> ap_par Q M R)"
  by (auto simp: fun_eq_iff ap_par_eval disj_pred_def split: prod.splits)

lemma ap_par_disj_right:
  "ap_par P M (Q \<or> R) = (ap_par P M Q \<or> ap_par P M R)"
  by (auto simp: fun_eq_iff ap_par_eval disj_pred_def split: prod.splits)

lemma ap_par_false_left [simp]: "ap_par false M P = false"
  by (rule par_by_merge_left_false)

lemma ap_par_false_right [simp]: "ap_par P M false = false"
  by (rule par_by_merge_right_false)

end
