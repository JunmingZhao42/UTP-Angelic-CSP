section \<open>Non-Divergent Reactive Angelic Designs\<close>

theory utp_rad_nd
  imports utp_rad_seq
begin

(* Paper Definition 45: the angelic choice with the most nondeterministic
   non-divergent process. *)
definition NDRAD :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "NDRAD P = P \<squnion>\<^sub>R\<^sub>A\<^sub>D Choice\<^sub>R\<^sub>A\<^sub>D"

lemma NDRAD_idem: "NDRAD (NDRAD P) = NDRAD P"
  by (simp add: NDRAD_def inf_assoc)

lemma NDRAD_Idempotent [closure]: "Idempotent NDRAD"
  by (simp add: Idempotent_def NDRAD_idem)

lemma NDRAD_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> NDRAD P \<sqsubseteq> NDRAD Q"
  unfolding NDRAD_def RAD_angelic_choice
  by (intro pred_ba.inf_mono; simp)

lemma NDRAD_Monotonic [closure]: "Monotonic NDRAD"
  by (rule MonotonicI, rule NDRAD_mono)

lemma NDRAD_RAD_closure [closure]:
  assumes "P is RAD"
  shows "NDRAD P is RAD"
  unfolding NDRAD_def
  by (rule RAD_angelic_closure[OF assms Choice_RAD_is_RAD])

(* Paper Theorem 34: the NDRAD image keeps the postcondition but has
   precondition true, so it cannot diverge. *)
theorem NDRAD_design_form:
  assumes "P is RAD"
  shows "NDRAD P = (RA \<circ> A) (true \<turnstile> (P \<^sub>f)\<^sup>t)"
  using Choice_RAD_angelic_choice[OF assms]
  by (simp add: NDRAD_def inf_commute)

(* Paper Theorem 35 / thesis T.5.5.3. The implication restricts the
   non-divergence requirement to observations in which the process has started,
   mirroring the thesis' case analysis on initial ok. *)
theorem NDRAD_fixed_point:
  assumes "P is RAD"
  shows "NDRAD P = P \<longleftrightarrow>
    (\<forall>s0 ac'. (ok\<^sup>< \<longrightarrow> (\<not> (P \<^sub>f)\<^sup>f)) (s0, ac'))"
proof
  assume fixed: "NDRAD P = P"
  have "((NDRAD P) \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> =
      ((P \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> \<and>
       (Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    unfolding NDRAD_def RAD_angelic_choice
    by (simp only: rad_wait_false_conj usubst)
  also have "... = false"
    by (simp only: Choice_RAD_wf_ok_false_subst; pred_auto)
  finally have failure_false: "(P \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: fixed)
  show "\<forall>s0 ac'. (ok\<^sup>< \<longrightarrow> (\<not> (P \<^sub>f)\<^sup>f)) (s0, ac')"
    using failure_false
    by (simp add: fun_eq_iff usubst usubst_eval; pred_auto)
next
  assume nondiv: "\<forall>s0 ac'. (ok\<^sup>< \<longrightarrow> (\<not> (P \<^sub>f)\<^sup>f)) (s0, ac')"
  have guard_true: "(\<not> (P \<^sub>f)\<^sup>f)\<lbrakk>True/ok\<^sup><\<rbrakk> = true"
    using nondiv
    by (simp add: fun_eq_iff usubst usubst_eval; pred_auto)
  have design_eq:
      "((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t) =
       (true \<turnstile> (P \<^sub>f)\<^sup>t)"
    by (rule design_ok_in_cong; simp only: guard_true pred_true_ok_in_subst)
  show "NDRAD P = P"
    by (simp only: NDRAD_design_form[OF assms] design_eq[symmetric] RAD_design_form'[OF assms, symmetric])
qed

lemma NDRAD_wf_ok_false_subst:
  assumes "P is RAD" "P is NDRAD"
  shows "(P \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
proof -
  have nondiv:
    "\<forall>s0 ac'. (ok\<^sup>< \<longrightarrow> (\<not> (P \<^sub>f)\<^sup>f)) (s0, ac')"
    using NDRAD_fixed_point[OF assms(1)] Healthy_if[OF assms(2)]
    by blast
  show ?thesis
    using nondiv
    by (simp add: fun_eq_iff usubst usubst_eval; pred_auto)
qed

(* Thesis Theorem T.G.6.1: sequential composition of two non-divergent
   reactive angelic designs has a true precondition. *)
lemma NDRAD_seq_design:
  assumes "P is RAD" "Q is RAD" "P is NDRAD" "Q is NDRAD"
  shows "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) =
    (RA \<circ> A) (true \<turnstile>
      (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>D
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        RA2 (RA1 ((Q \<^sub>f)\<^sup>t)))))"
proof -
  let ?Pf = "(P \<^sub>f)\<^sup>f" and ?Pt = "(P \<^sub>f)\<^sup>t"
  let ?Qf = "(Q \<^sub>f)\<^sup>f" and ?Qt = "(Q \<^sub>f)\<^sup>t"
  let ?pre = "((\<not> (RA1 ?Pf ;;\<^sub>A\<^sub>D RA1 true)) \<and>
    (\<not> (RA1 ?Pt ;;\<^sub>A\<^sub>D
      ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Qf)))))"
  let ?post = "(RA1 ?Pt ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ((\<not> ?Qf) \<longrightarrow> ?Qt))))"
  let ?postND = "(RA1 ?Pt ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ?Qt)))"
  have Pf_false: "?Pf\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    and Qf_false: "?Qf\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (rule NDRAD_wf_ok_false_subst[OF assms(1,3)],
        rule NDRAD_wf_ok_false_subst[OF assms(2,4)])
  have Pf_RA1_false:
    "(RA1 ?Pf)\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: RA1_ok_in_subst Pf_false RA1_false)
  have Qf_RA1_false:
    "(RA1 ?Qf)\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: RA1_ok_in_subst Qf_false RA1_false)
  have Qf_RA2_RA1_false:
    "(RA2 (RA1 ?Qf))\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: RA2_ok_in_subst Qf_RA1_false RA2_false)
  have Qguard_false:
    "(((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Qf)))
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: subst_pred Qf_RA2_RA1_false pred_ba.inf_bot_right)
  have Pt_RA1_push:
    "(RA1 ?Pt)\<lbrakk>True/ok\<^sup><\<rbrakk> =
      RA1 (?Pt\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (rule RA1_ok_in_subst)
  have initial_failure_false:
    "(RA1 ?Pf ;;\<^sub>A\<^sub>D RA1 true)
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: aseq_ades_ok_in_subst Pf_RA1_false
        aseq_ades_false_left)
  have handover_failure_false:
    "(RA1 ?Pt ;;\<^sub>A\<^sub>D
      ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Qf)))
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: aseq_ades_ok_in_subst Pt_RA1_push
        Qguard_false RA1_aseq_false)
  have pre_push: "?pre\<lbrakk>True/ok\<^sup><\<rbrakk> =
      true\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: subst_pred initial_failure_false
        handover_failure_false pred_ba.compl_bot_eq
        pred_ba.inf_top_left)
  have continuation_push:
    "(RA2 (RA1 ((\<not> ?Qf) \<longrightarrow> ?Qt)))
      \<lbrakk>True/ok\<^sup><\<rbrakk> =
     (RA2 (RA1 ?Qt))\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: RA2_ok_in_subst RA1_ok_in_subst subst_pred
        Qf_false pred_ba.compl_bot_eq pred_impl_laws(1))
  have post_push: "?post\<lbrakk>True/ok\<^sup><\<rbrakk> =
      ?postND\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: aseq_ades_ok_in_subst rad_wait_cond_ok_in_subst
        continuation_push)
  have design_eq: "(?pre \<turnstile> ?post) = (true \<turnstile> ?postND)"
    by (rule design_ok_in_cong[OF pre_push post_push])
  show ?thesis
    by (simp only: RAD_seq_design[OF assms(1,2)] design_eq)
qed

(* Paper Example 20: divergence is avoided at the bottom of the lattice. *)
lemma NDRAD_Chaos:
  "NDRAD Chaos\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  unfolding NDRAD_def
  by (rule Chaos_RAD_angelic_choice_unit[OF Choice_RAD_is_RAD])

lemma NDRAD_Choice:
  "NDRAD Choice\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  by (simp add: NDRAD_def)

subsection \<open>Counterexample to the Original Theorem 35\<close>

(* Choice_RAD satisfies the fixed-point LHS of the original paper theorem. *)
lemma theorem35_counterexample_lhs: "NDRAD Choice\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  by (rule NDRAD_Choice)

(* Its unguarded failure predicate refutes the universally quantified RHS when
   the process has not started. *)
lemma theorem35_counterexample_rhs:
  "\<not> (\<forall>s0 ac'. (\<not> (Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f) (s0, ac'))"
proof -
  have failure:
    "(Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f
      (\<lparr>ok\<^sub>v = False,
        \<dots> = StateII (undefined :: ('t::trace, 'e) rad_state)\<rparr>,
       \<lparr>ok\<^sub>v = False,
        \<dots> = \<lparr>ac\<^sub>v = {undefined :: ('t, 'e) rad_state}, \<dots> = ()\<rparr>\<rparr>)"
    by (simp only: Choice_RAD_wf_ok_false RA1_RA2_commute'[symmetric] RA2_not_ok_expr; pred_auto)
  show ?thesis using failure by (auto simp: not_pred_def)
qed

(* Hence the LHS of the original paper theorem does not imply its RHS. *)
lemma theorem35_counterexample:
  "\<not> (let P = Choice\<^sub>R\<^sub>A\<^sub>D in
    NDRAD P = P \<longrightarrow> (\<forall>s0 ac'. (\<not> (P \<^sub>f)\<^sup>f) (s0, ac')))"
  using theorem35_counterexample_lhs theorem35_counterexample_rhs by simp

end
