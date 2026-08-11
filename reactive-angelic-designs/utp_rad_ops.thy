section \<open>Reactive Angelic Design Operators\<close>

theory utp_rad_ops
  imports utp_rad_csp
begin

subsection \<open>Angelic Choice\<close>

(* Paper Definition 37. *)
abbreviation achoice_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  (infixl "\<squnion>\<^sub>R\<^sub>A\<^sub>D" 70) 
where "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q \<equiv> P \<squnion> Q"

lemma RAD_angelic_choice:
  "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

(* Paper Theorem 19. *)
(* P \<squnion> Q = RA \<circ> A ( \<not>P_f^f \<or> \<not>Q_f^f \<turnstile> (\<not>P_f^f \<Rightarrow> P_f^t) \<and> (\<not>Q_f^f \<Rightarrow> Q_f^t)) *)
theorem RAD_angelic_choice_design:
  assumes "P is RAD" "Q is RAD"
  shows "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q =
     (RA \<circ> A) (((\<not> (P \<^sub>wf)\<^sup>f) \<or> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
              (((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t) \<and>
              ((\<not> (Q \<^sub>wf)\<^sup>f) \<longrightarrow> (Q \<^sub>wf)\<^sup>t)))"
proof -
  let ?DP = "(\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t"
  let ?DQ = "(\<not> (Q \<^sub>wf)\<^sup>f) \<turnstile> (Q \<^sub>wf)\<^sup>t"
  have "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q =
      (RA \<circ> A) ?DP \<squnion> (RA \<circ> A) ?DQ"
    using arg_cong2[where f=inf,
        OF RAD_design_form'[OF assms(1)] RAD_design_form'[OF assms(2)]] .
  also have "... = (RA \<circ> A) (?DP \<squnion> ?DQ)"
    by (rule RA_A_angelic_choice[OF
          RAD_design_PBMH[OF assms(1)] RAD_design_PBMH[OF assms(2)]
          rad_wait_false_design_is_H rad_wait_false_design_is_H])
  also have "... = (RA \<circ> A)
        (((\<not> (P \<^sub>wf)\<^sup>f) \<or> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
         (((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t) \<and>
          ((\<not> (Q \<^sub>wf)\<^sup>f) \<longrightarrow> (Q \<^sub>wf)\<^sup>t)))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed

lemma RAD_angelic_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q is RAD"
proof -
  let ?D =
    "((\<not> (P \<^sub>wf)\<^sup>f) \<or> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
      (((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t) \<and>
       ((\<not> (Q \<^sub>wf)\<^sup>f) \<longrightarrow> (Q \<^sub>wf)\<^sup>t))"
  have "(RA \<circ> A) ?D is RAD"
    by rad_closure
  then show ?thesis
    by (simp only: RAD_angelic_choice_design[OF assms])
qed

(* Paper Theorem 20 / Thesis Theorem T.5.4.2. *)
theorem RAD_angelic_choice_CSP:
  "rad_ac2p (rad_p2ac P \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q) = P \<squnion> Q"
proof -
  have distribute:
      "rad_ac2p (rad_p2ac P \<and> rad_p2ac Q) =
       (rad_ac2p (rad_p2ac P) \<and> rad_ac2p (rad_p2ac Q))"
    unfolding rad_ac2p_def comp_apply
    apply (subst ac2p_conj)
      apply (rule rad_p2ac_PBMH_ades)+
    by (simp add: rad2csp_rel_def fun_eq_iff conj_pred_def)
  show ?thesis
    apply (simp only: RAD_angelic_choice distribute rad_ac2p_p2ac_inverse')
    by (simp only: conj_pred_def)
qed

(* Paper Theorem 21 / Thesis Theorem T.5.4.3. *)
theorem RAD_angelic_choice_CSP_refine:
  assumes "P is RAD" "Q is RAD"
  shows "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q \<sqsubseteq> rad_p2ac (rad_ac2p P \<squnion> rad_ac2p Q)"
proof -
  have P_round: "P \<sqsubseteq> rad_p2ac (rad_ac2p P)"
    by (rule rad_p2ac_ac2p_refine'[OF RAD_is_PBMH_ades[OF assms(1)]])
  have Q_round: "Q \<sqsubseteq> rad_p2ac (rad_ac2p Q)"
    by (rule rad_p2ac_ac2p_refine'[OF RAD_is_PBMH_ades[OF assms(2)]])
  have "(P \<and> Q) \<sqsubseteq>
      (rad_p2ac (rad_ac2p P) \<and> rad_p2ac (rad_ac2p Q))"
    by (rule pred_ba.inf_mono[OF P_round Q_round])
  also have "... \<sqsubseteq>
      rad_p2ac (rad_ac2p P \<and> rad_ac2p Q)"
    by (rule rad_p2ac_conj)
  finally show ?thesis
    apply (simp only: RAD_angelic_choice)
    by (simp only: conj_pred_def)
qed

subsection \<open>Demonic Choice\<close>

(* Paper Definition 38. *)
abbreviation dchoice_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  (infixl "\<sqinter>\<^sub>R\<^sub>A\<^sub>D" 65)
where "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q \<equiv> P \<sqinter> Q"

lemma RAD_demonic_choice:
  "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

(* Paper Theorem 22 / Thesis Theorem T.5.4.4. *)
theorem RAD_demonic_choice_design:
  assumes "P is RAD" "Q is RAD"
  shows "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q =
    (RA \<circ> A) (((\<not> (P \<^sub>wf)\<^sup>f) \<and> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
      ((P \<^sub>wf)\<^sup>t \<or> (Q \<^sub>wf)\<^sup>t))"
proof -
  let ?DP = "(\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t"
  let ?DQ = "(\<not> (Q \<^sub>wf)\<^sup>f) \<turnstile> (Q \<^sub>wf)\<^sup>t"
  have "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q =
      (RA \<circ> A) ?DP \<sqinter> (RA \<circ> A) ?DQ"
    using arg_cong2[where f=sup,
        OF RAD_design_form'[OF assms(1)] RAD_design_form'[OF assms(2)]] .
  also have "... = (RA \<circ> A) (?DP \<sqinter> ?DQ)"
    by (rule RA_A_demonic_choice)
  also have "... = (RA \<circ> A)
      (((\<not> (P \<^sub>wf)\<^sup>f) \<and> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
        ((P \<^sub>wf)\<^sup>t \<or> (Q \<^sub>wf)\<^sup>t))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    by (simp only: angelic_design_demonic design_union)
  finally show ?thesis .
qed

lemma RAD_demonic_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q is RAD"
proof -
  let ?D =
    "((\<not> (P \<^sub>wf)\<^sup>f) \<and> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
      ((P \<^sub>wf)\<^sup>t \<or> (Q \<^sub>wf)\<^sup>t)"
  have "(RA \<circ> A) ?D is RAD"
    by rad_closure
  then show ?thesis
    by (simp only: RAD_demonic_choice_design[OF assms])
qed

(* Paper Theorem 23 / Thesis Theorem T.5.4.5. *)
theorem RAD_demonic_choice_CSP_distrib:
  "rad_p2ac (rad_ac2p P \<sqinter> rad_ac2p Q) =
   rad_p2ac (rad_ac2p P) \<sqinter>\<^sub>R\<^sub>A\<^sub>D rad_p2ac (rad_ac2p Q)"
  by (rule rad_p2ac_disj[simplified disj_pred_def])

(* Paper Lemma 7 / Thesis Lemma L.5.4.1. *)
lemma RAD_demonic_choice_CSP_A2:
  assumes "P is RAD" "Q is RAD"
    and "P is A2" "Q is A2"
  shows "rad_p2ac (rad_ac2p P \<sqinter> rad_ac2p Q) = P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q"
  by (simp only: RAD_demonic_choice_CSP_distrib
      rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

(* Paper Theorem 24 / Thesis Theorem T.5.4.6. *)
theorem RAD_demonic_choice_CSP:
  "rad_ac2p (rad_p2ac P \<sqinter>\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q) = P \<sqinter> Q"
  by (simp only: rad_ac2p_disj[simplified disj_pred_def]
      rad_ac2p_p2ac_inverse')

(* Paper Section 6.4.2: angelic and demonic choice distribute over each other. *)
(* P \<squnion> (Q \<Sqinter> R) = (P \<squnion> Q) \<sqinter> (P \<squnion> R) *)
lemma RAD_angelic_demonic_distrib:
  "P \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) =
   (P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (P \<squnion>\<^sub>R\<^sub>A\<^sub>D R)"
  by (rule inf_sup_distrib1)

(* P \<sqinter> (Q \<squnion> R) = (P \<sqinter> Q) \<squnion> (P \<sqinter> R) *)
lemma RAD_demonic_angelic_distrib:
  "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R) =
   (P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P \<sqinter>\<^sub>R\<^sub>A\<^sub>D R)"
  by (rule sup_inf_distrib1)

subsection \<open>Chaos\<close>

(* Paper Definition 39. *)
definition Chaos_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Chaos\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Chaos_RAD = (RA \<circ> A) (false \<turnstile> ac_non_empty)"

lemma Chaos_RAD':
  "Chaos\<^sub>R\<^sub>A\<^sub>D = (RA \<circ> A) (false \<turnstile> true)"
  by (simp only: Chaos_RAD_def design_false_pre)

(* Chaos_RAD is the RAD image of true. *)
lemma Chaos_RAD_RAD: "Chaos\<^sub>R\<^sub>A\<^sub>D = RAD true"
  by (simp only: Chaos_RAD' RAD_design_form comp_apply
      rad_wait_false_true subst_pred(1) pred_ba.compl_top_eq)

lemma bottom_RAD_is_Chaos:
  "(\<^bold>\<bottom>\<^sub>R\<^sub>A\<^sub>D ::
      ('t::trace, 'e) reactive_angelic_design) = Chaos\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: Chaos_RAD_RAD)

lemma Chaos_RAD_RA: "Chaos\<^sub>R\<^sub>A\<^sub>D = RA true"
  apply (simp only: Chaos_RAD' design_false_pre comp_apply)
  apply (subst RA_A')
   apply (simp add: Healthy_def' H1_H2_comp comp_apply H1_def H2_true)
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma Chaos_RAD_is_RAD [closure]: "Chaos\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Chaos_RAD_def
  by rad_closure

(* Paper Theorem 25. *)
theorem Chaos_RAD_angelic_choice_unit:
  assumes "P is RAD"
  shows "Chaos\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P = P"
proof -
  have P_RA: "RA P = P"
    by (rule Healthy_if[OF RAD_is_RA[OF assms]])
  show ?thesis
    apply (simp only: RAD_angelic_choice Chaos_RAD_RA)
    apply (subst P_RA[symmetric])
    apply (simp add: RA_conj[symmetric])
    by (rule P_RA)
qed

(* The dual law of Paper Theorem 25. *)
theorem Chaos_RAD_demonic_choice_zero:
  assumes "P is RAD"
  shows "Chaos\<^sub>R\<^sub>A\<^sub>D \<sqinter>\<^sub>R\<^sub>A\<^sub>D P = Chaos\<^sub>R\<^sub>A\<^sub>D"
proof -
  have P_RA: "RA P = P"
    by (rule Healthy_if[OF RAD_is_RA[OF assms]])
  show ?thesis
    apply (simp only: RAD_demonic_choice Chaos_RAD_RA)
    apply (subst P_RA[symmetric])
    by (simp add: RA_disj[symmetric])
qed

subsection \<open>Choice\<close>

(* Paper Definition 40. *)
definition Choice_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Choice\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Choice_RAD = (RA \<circ> A) (true \<turnstile> ac_non_empty)"

lemma Choice_RAD_alt:
  "Choice\<^sub>R\<^sub>A\<^sub>D = (RA \<circ> A) (true \<turnstile> true)"
  apply (simp only: Choice_RAD_def comp_apply)
  apply (rule arg_cong[where f=RA])
  by (simp add: A_design_form ac_non_empty_def PBMH_def pbmh_step_def
      fun_eq_iff; pred_auto)

lemma Choice_RAD_is_RAD [closure]: "Choice\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Choice_RAD_def
  by rad_closure

lemma Choice_RAD_RA: "Choice\<^sub>R\<^sub>A\<^sub>D = RA (true \<turnstile> true)"
  apply (simp only: Choice_RAD_alt)
  by (rule RA_A_absorb_design_true[OF true_PBMH_ades];
      simp add: unrest)

(* The wait-conditional design form of Choice_RAD under RA1. *)
lemma Choice_RAD_design:
  "Choice\<^sub>R\<^sub>A\<^sub>D =
   RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         true))"
  by (simp only: Choice_RAD_RA RA_true_design RA2_true)

(* Choice_RAD can only fail to stabilise when it has not started. *)
lemma Choice_RAD_wf_ok_false:
  "(Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>f = RA2 (RA1 (\<not> ok\<^sup><))"
proof -
  have design_norm:
      "((\<not> (ok\<^sup>> \<^sub>wf)\<^sup>f) \<turnstile> (ok\<^sup>> \<^sub>wf)\<^sup>t) = (true \<turnstile> true)"
    by (simp add: rad_wait_false_def usubst usubst_eval; pred_auto)
  have disj_norm:
      "((\<not> ok\<^sup><) \<or> (ok\<^sup>> \<^sub>wf)\<^sup>f) = (\<not> ok\<^sup><)"
    by (simp add: rad_wait_false_def usubst usubst_eval; pred_auto)
  have "((rad_wait_false \<circ> RA \<circ> A) (true \<turnstile> true))\<^sup>f =
      (RA2 \<circ> RA1 \<circ> PBMH_ades) ((\<not> ok\<^sup><) \<or> (ok\<^sup>> \<^sub>wf)\<^sup>f)"
    using RA_design_wf_ok_false[of "ok\<^sup>>"]
    by (simp only: design_norm)
  then show ?thesis
    by (simp only: Choice_RAD_alt disj_norm comp_apply PBMH_ades_not_ok_expr)
qed

lemma Choice_RAD_wf_ok_false_subst:
  "(Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
proof -
  have not_true: "(\<not> (True)\<^sub>e :: ('t::trace, 'e) reactive_angelic_design) = false"
    by pred_auto
  show ?thesis
    apply (simp only: Choice_RAD_wf_ok_false RA2_ok_in_subst RA1_ok_in_subst)
    apply (simp add: usubst usubst_eval)
    by (simp only: not_true RA1_false RA2_false)
qed

(* Paper Theorem 26. *)
theorem Choice_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Choice\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P = (RA \<circ> A) (true \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f"
  let ?T = "(P \<^sub>wf)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  let ?Z = "(\<not> ok\<^sup><) \<or> ?F \<or> ?T"
  have T_form: "?T = RA2 (RA1 (PBMH_ades ?Z))"
    using arg_cong[where f="\<lambda>R. (R \<^sub>wf)\<^sup>t",
        OF RAD_design_form'[OF assms]]
    by (simp only: comp_apply RA_design_wf_ok_true')
  have "Choice\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> true) \<squnion> (RA \<circ> A) ?DP"
    using arg_cong2[where f=inf,
        OF Choice_RAD_alt RAD_design_form'[OF assms]] .
  also have "... = (RA \<circ> A) ((true \<turnstile> true) \<squnion> ?DP)"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' PBMH_ades_def fun_eq_iff; pred_auto)
      apply (rule RAD_design_PBMH[OF assms])
     apply (rule design_is_H1_H2; simp add: unrest)
    by (rule rad_wait_false_design_is_H)
  also have "... = (RA \<circ> A) (true \<turnstile> ?Z)"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  also have "... = (RA \<circ> A) (true \<turnstile> ?T)"
    apply (rule RA_A_true_design_post)
       apply (rule design_is_H1_H2; simp add: unrest)
      apply (rule design_is_H1_H2; simp add: unrest)
     apply (rule T_form[symmetric])
    by (rule Healthy_if[OF RAD_wf_ok_true_PBMH[OF assms]])
  finally show ?thesis .
qed

(* Paper Theorem 27. *)
theorem Choice_RAD_demonic_choice:
  assumes "P is RAD"
  shows "Choice\<^sub>R\<^sub>A\<^sub>D \<sqinter>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> ac_non_empty)"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f"
  let ?T = "(P \<^sub>wf)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  have "Choice\<^sub>R\<^sub>A\<^sub>D \<sqinter>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> true) \<sqinter> (RA \<circ> A) ?DP"
    using arg_cong2[where f=sup,
        OF Choice_RAD_alt RAD_design_form'[OF assms]] .
  also have "... = (RA \<circ> A) ((true \<turnstile> true) \<sqinter> ?DP)"
    by (rule RA_A_demonic_choice)
  also have "... = (RA \<circ> A) ((\<not> ?F) \<turnstile> ac_non_empty)"
    apply (simp only: comp_apply)
    apply (rule arg_cong[where f=RA])
    by (simp add: angelic_design_demonic design_union A_design_form
        ac_non_empty_def PBMH_def pbmh_step_def fun_eq_iff; pred_auto)
  finally show ?thesis .
qed

subsection \<open>Stop\<close>

(* Paper Definition 41: \<in>\<^sub>a\<^sub>c y \<bullet> y.tr = s.tr \<and> y.wait *)
definition stop_post :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "stop_post = (\<in>\<^sub>a\<^sub>c y. (\<lambda> (s0, ac1).
  rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
  rad_state.wait\<^sub>v y))"

(* Paper Definition 41. *)
definition Stop_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Stop\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Stop_RAD = (RA \<circ> A) (true \<turnstile> stop_post)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma stop_post_p2ac:
  "stop_post = p2ac \<lceil>(\<lambda> (s, y).
    rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s \<and> rad_state.wait\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: stop_post_def ades_singleton_choice_def p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma stop_post_PBMH [simp]: "PBMH_ades stop_post = stop_post"
  by (simp only: stop_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_stop_post: "(stop_post \<^sub>wf) = stop_post"
  by (simp add: stop_post_def ades_singleton_choice_def rad_wait_false_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma stop_post_unrest_ok [unrest]: "$ok\<^sup>> \<sharp> stop_post"
  apply (simp add: unrest_lens stop_post_def ades_singleton_choice_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma stop_post_unrest_ok_in [unrest]: "$ok\<^sup>< \<sharp> stop_post"
  apply (simp add: unrest_lens stop_post_def ades_singleton_choice_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

(* The Stop postcondition only relates the traces of the initial and
   final states, so trace normalisation leaves it fixed. *)
lemma RA2_stop_post: "RA2 stop_post = stop_post"
  by (simp add: RA2_def stop_post_def ades_singleton_choice_def rad_normalise_choices_def
      rad_trace_difference_def rad_zero_trace_def fun_eq_iff Let_def;
      pred_auto; force dest: minus_zero_eq[rotated])

lemma stop_post_ok_in_subst [usubst]:
  "stop_post\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> = stop_post"
  by (simp add: stop_post_def ades_singleton_choice_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      astate.s_def des_vars.more\<^sub>L_def)

lemma stop_post_ok_out_subst [usubst]:
  "stop_post\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk> = stop_post"
  by (simp add: stop_post_def ades_singleton_choice_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      astate.s_def des_vars.more\<^sub>L_def)

(* Component normal forms of the design body \<open>stop_post \<and> ok\<^sup>>\<close>
   witnessing Stop's projections. *)
lemma stop_design_wf_norm:
  "((stop_post \<and> ok\<^sup>>) \<^sub>wf) = (stop_post \<and> ok\<^sup>>)"
  by (simp only: rad_wait_false_conj rad_wait_false_stop_post
      rad_wait_false_ok_out)

lemma stop_design_ok_false: "(stop_post \<and> ok\<^sup>>)\<^sup>f = false"
  by (simp add: usubst usubst_eval; pred_auto)

lemma stop_design_ok_true: "(stop_post \<and> ok\<^sup>>)\<^sup>t = stop_post"
  by (simp add: usubst usubst_eval; pred_auto)

(* Stop can only fail to stabilise when it has not started. *)
lemma Stop_RAD_wf_ok_false:
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>f = RA2 (RA1 (\<not> ok\<^sup><))"
proof -
  have design_norm:
      "((\<not> ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>f) \<turnstile>
        ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>t) =
       (true \<turnstile> stop_post)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        stop_design_ok_true pred_ba.compl_bot_eq)
  have disj_norm:
      "((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>f) = (\<not> ok\<^sup><)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        pred_ba.sup_bot_right)
  have "((rad_wait_false \<circ> RA \<circ> A) (true \<turnstile> stop_post))\<^sup>f =
      (RA2 \<circ> RA1 \<circ> PBMH_ades)
        ((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>f)"
    using RA_design_wf_ok_false[of "stop_post \<and> ok\<^sup>>"]
    by (simp only: design_norm)
  then show ?thesis
    by (simp only: Stop_RAD_def comp_apply disj_norm
        PBMH_ades_not_ok_expr)
qed

lemma Stop_RAD_wf_ok_false_subst:
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
proof -
  have not_true: "(\<not> (True)\<^sub>e :: ('t::trace, 'e) reactive_angelic_design) = false"
    by pred_auto
  show ?thesis
    apply (simp only: Stop_RAD_wf_ok_false RA2_ok_in_subst
        RA1_ok_in_subst)
    apply (simp add: usubst usubst_eval)
    by (simp only: not_true RA1_false RA2_false)
qed

lemma Stop_RAD_wf_ok_true:
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>t = RA2 (RA1 ((\<not> ok\<^sup><) \<or> stop_post))"
proof -
  have design_norm:
      "((\<not> ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>f) \<turnstile>
        ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>t) =
       (true \<turnstile> stop_post)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        stop_design_ok_true pred_ba.compl_bot_eq)
  have disj_norm:
      "((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>f \<or>
        ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>t) =
       ((\<not> ok\<^sup><) \<or> stop_post)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        stop_design_ok_true pred_ba.sup_bot_left)
  have PBMH_norm:
      "PBMH_ades ((\<not> ok\<^sup><) \<or> stop_post) = ((\<not> ok\<^sup><) \<or> stop_post)"
    by (simp add: PBMH_ades_disj)
  have "((rad_wait_false \<circ> RA \<circ> A) (true \<turnstile> stop_post))\<^sup>t =
      (RA2 \<circ> RA1 \<circ> PBMH_ades)
        ((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>f \<or>
         ((stop_post \<and> ok\<^sup>>) \<^sub>wf)\<^sup>t)"
    using RA_design_wf_ok_true[of "stop_post \<and> ok\<^sup>>"]
    by (simp only: design_norm)
  then show ?thesis
    by (simp only: Stop_RAD_def comp_apply disj_norm PBMH_norm)
qed

lemma Stop_RAD_wf_ok_true_subst:
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>t\<lbrakk>True/ok\<^sup><\<rbrakk> = RA2 (RA1 stop_post)"
proof -
  have subst_norm:
      "((\<not> ok\<^sup><) \<or> stop_post)\<lbrakk>True/ok\<^sup><\<rbrakk> = stop_post"
    by (simp add: usubst usubst_eval; pred_auto)
  show ?thesis
    by (simp only: Stop_RAD_wf_ok_true RA2_ok_in_subst
        RA1_ok_in_subst subst_norm)
qed

lemma stop_design_is_H [closure]: "(true \<turnstile> stop_post) is \<^bold>H"
  by (rule design_is_H1_H2; simp add: unrest)

lemma Stop_RAD_is_RAD [closure]: "Stop\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Stop_RAD_def
  apply (rule RAD_design_closure)
   apply (rule stop_design_is_H)
  by (simp add: rad_wait_false_distrib rad_wait_false_stop_post)

(* Stop with the A absorbed into RA. *)
lemma Stop_RAD_RA: "Stop\<^sub>R\<^sub>A\<^sub>D = RA (true \<turnstile> stop_post)"
  unfolding Stop_RAD_def
  by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)

(* The wait-conditional design form of Stop_RAD under RA1. *)
lemma Stop_RAD_design:
  "Stop\<^sub>R\<^sub>A\<^sub>D =
   RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         stop_post))"
  by (simp only: Stop_RAD_RA RA_true_design RA2_stop_post)

(* Paper Theorem 28. *)
theorem Stop_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile> (((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t) \<and> stop_post))"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f"
  let ?T = "(P \<^sub>wf)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  have "Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> stop_post) \<squnion> (RA \<circ> A) ?DP"
    by (simp only: Stop_RAD_def RAD_design_form'[OF assms, symmetric])
  also have "... = (RA \<circ> A) ((true \<turnstile> stop_post) \<squnion> ?DP)"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (rule RAD_design_PBMH[OF assms])
     apply (rule stop_design_is_H)
    by (rule rad_wait_false_design_is_H)
  also have "... = (RA \<circ> A)
      (true \<turnstile> (((\<not> ?F) \<longrightarrow> ?T) \<and> stop_post))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed

subsection \<open>Skip\<close>

(* Paper Definition 42: \<in>\<^sub>a\<^sub>c y \<bullet> \<not> y.wait \<and> y.tr = s.tr *)
definition skip_post :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "skip_post = (\<in>\<^sub>a\<^sub>c y. (\<lambda> (s0, ac1).
  \<not> rad_state.wait\<^sub>v y \<and> rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0))))"

(* Paper Definition 42. *)
definition Skip_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Skip\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Skip_RAD = (RA \<circ> A) (true \<turnstile> skip_post)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma skip_post_p2ac:
  "skip_post = p2ac \<lceil>(\<lambda> (s, y).
    \<not> rad_state.wait\<^sub>v y \<and> rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s)\<rceil>\<^sub>D"
  by (simp add: skip_post_def ades_singleton_choice_def p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma skip_post_PBMH [simp]: "PBMH_ades skip_post = skip_post"
  by (simp only: skip_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_skip_post: "(skip_post \<^sub>wf) = skip_post"
  by (simp add: skip_post_def ades_singleton_choice_def rad_wait_false_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA1_skip_post: "RA1 skip_post = skip_post"
  apply (simp add: RA1_def skip_post_def ades_singleton_choice_def
      rad_trace_extensions_def fun_eq_iff Let_def)
  apply (auto intro: order_refl)
  subgoal for a b y
    apply (drule arg_cong[where f="\<lambda>S. y \<in> S"])
    by simp
  done

lemma RA2_skip_post: "RA2 skip_post = skip_post"
  by (simp add: RA2_def skip_post_def ades_singleton_choice_def rad_normalise_choices_def
      rad_trace_difference_def rad_zero_trace_def fun_eq_iff Let_def;
      pred_auto; force dest: minus_zero_eq[rotated])

lemma skip_post_unrest_ok_in [unrest]: "$ok\<^sup>< \<sharp> skip_post"
  apply (simp add: unrest_lens skip_post_def ades_singleton_choice_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma skip_post_unrest_ok [unrest]: "$ok\<^sup>> \<sharp> skip_post"
  apply (simp add: unrest_lens skip_post_def ades_singleton_choice_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma skip_post_ok_in_subst [usubst]:
  "skip_post\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> = skip_post"
  by (simp add: skip_post_def ades_singleton_choice_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      astate.s_def des_vars.more\<^sub>L_def)

lemma skip_post_ok_out_subst [usubst]:
  "skip_post\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk> = skip_post"
  by (simp add: skip_post_def ades_singleton_choice_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      astate.s_def des_vars.more\<^sub>L_def)

lemma skip_design_is_H [closure]: "(true \<turnstile> skip_post) is \<^bold>H"
  by (rule design_is_H1_H2; simp add: unrest)

lemma Skip_RAD_is_RAD [closure]: "Skip\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Skip_RAD_def
  apply (rule RAD_design_closure)
   apply (rule skip_design_is_H)
  by (simp add: rad_wait_false_distrib rad_wait_false_skip_post)

(* Skip with the A absorbed into RA. *)
lemma Skip_RAD_RA: "Skip\<^sub>R\<^sub>A\<^sub>D = RA (true \<turnstile> skip_post)"
  unfolding Skip_RAD_def
  by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)

(* The wait-conditional design form of Skip_RAD under RA1. *)
lemma Skip_RAD_design:
  "Skip\<^sub>R\<^sub>A\<^sub>D =
   RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         skip_post))"
  by (simp only: Skip_RAD_RA RA_true_design RA2_skip_post)

(* Paper Theorem 29. *)
theorem Skip_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Skip\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile> (skip_post \<and> ((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t)))"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f"
  let ?T = "(P \<^sub>wf)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  have "Skip\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> skip_post) \<squnion> (RA \<circ> A) ?DP"
    by (simp only: Skip_RAD_def RAD_design_form'[OF assms, symmetric])
  also have "... = (RA \<circ> A) ((true \<turnstile> skip_post) \<squnion> ?DP)"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (rule RAD_design_PBMH[OF assms])
     apply (rule skip_design_is_H)
    by (rule rad_wait_false_design_is_H)
  also have "... = (RA \<circ> A)
      (true \<turnstile> (skip_post \<and> ((\<not> ?F) \<longrightarrow> ?T)))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed

subsection \<open>Sequential Composition\<close>

text \<open>
  Paper Section 6.4.7: sequential composition of reactive angelic designs
  is exactly \<open>;;\<^sub>D\<^sub>A\<close> from the theory of angelic designs.  The notation
  remains here because the compound prefix operator below uses it.  Its
  laws, CSP correspondence, paper Theorem 30 normal form, and RAD closure
  law are proved in \<open>utp_rad_seq\<close>.
\<close>

abbreviation seq_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design" (infixl ";;\<^sub>R\<^sub>A\<^sub>D" 75)
where "P ;;\<^sub>R\<^sub>A\<^sub>D Q \<equiv> P ;;\<^sub>D\<^sub>A Q"

subsection \<open>Prefixing\<close>

(* \<exists> y \<in> ac' \<bullet> (y.tr = s.tr \<and> a \<notin> y.ref) \<triangleleft> y.wait \<triangleright> y.tr = s.tr @ [a] *)
definition prefix_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design" where
[pred]: "prefix_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac'). (((\<lambda> z. rad_state.tr\<^sub>v z =
          rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
        a \<notin> rad_state.ref\<^sub>v z)
      \<triangleleft> $rad_state.wait \<triangleright>
      (\<lambda> z. rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a])) y))"

(* Paper Definition 43 / Thesis Definition 124. *)
definition PrefixSkip_RAD :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design" where
[pred]: "PrefixSkip_RAD a = (RA \<circ> A) (true \<turnstile> prefix_post a)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma prefix_post_p2ac:
  "prefix_post a = p2ac \<lceil>(\<lambda> (s, y).
    if rad_state.wait\<^sub>v y
    then rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s \<and>
      a \<notin> rad_state.ref\<^sub>v y
    else rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s @ [a])\<rceil>\<^sub>D"
  by (simp add: prefix_post_def expr_if_def rad_state.wait_def
      p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma prefix_post_PBMH [simp]:
  "PBMH_ades (prefix_post a) = prefix_post a"
  by (simp only: prefix_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_prefix_post:
  "((prefix_post a) \<^sub>wf) = prefix_post a"
  by (simp add: prefix_post_def expr_if_def rad_state.wait_def
      rad_wait_false_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma prefix_post_unrest_ok [unrest]: "$ok\<^sup>> \<sharp> prefix_post a"
  apply (simp add: unrest_lens prefix_post_def expr_if_def
      rad_state.wait_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma prefix_design_is_H [closure]:
  "(true \<turnstile> prefix_post a) is \<^bold>H"
  by (rule design_is_H1_H2; simp add: unrest)

lemma PrefixSkip_RAD_is_RAD [closure]: "PrefixSkip_RAD a is RAD"
  unfolding PrefixSkip_RAD_def
  apply (rule RAD_design_closure)
   apply (rule prefix_design_is_H)
  by (simp add: rad_wait_false_distrib rad_wait_false_prefix_post)

(* Prefixing with the A absorbed into RA. *)
lemma PrefixSkip_RAD_RA:
  "PrefixSkip_RAD a = RA (true \<turnstile> prefix_post a)"
  unfolding PrefixSkip_RAD_def
  by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)

(* Paper Theorem 31 / Thesis Theorem T.5.4.26. *)
theorem PrefixSkip_RAD_angelic_choice:
  assumes "P is RAD"
  shows "PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile> (((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t) \<and> prefix_post a))"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f"
  let ?T = "(P \<^sub>wf)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  have "PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> prefix_post a) \<squnion> (RA \<circ> A) ?DP"
    by (simp only: PrefixSkip_RAD_def
        RAD_design_form'[OF assms, symmetric])
  also have "... = (RA \<circ> A) ((true \<turnstile> prefix_post a) \<squnion> ?DP)"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (rule RAD_design_PBMH[OF assms])
     apply (rule prefix_design_is_H)
    by (rule rad_wait_false_design_is_H)
  also have "... = (RA \<circ> A)
      (true \<turnstile> (((\<not> ?F) \<longrightarrow> ?T) \<and> prefix_post a))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed

(* Thesis Section 5.4.8: the compound process a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P
   abbreviates (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) ;;\<^sub>R\<^sub>A\<^sub>D P.  Its
   Theorem T.5.4.29 normal form is future work; RAD closure is proved
   in \<open>utp_rad_seq\<close>. *)
definition Prefix_RAD ::
  "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
   ('e list, 'e) reactive_angelic_design"
  (infixr "\<rightarrow>\<^sub>R\<^sub>A\<^sub>D" 80) where
[pred]: "Prefix_RAD a P = (PrefixSkip_RAD a ;;\<^sub>R\<^sub>A\<^sub>D P)"

subsection \<open>External Choice\<close>

(*  \<exists> y \<in> ac' \<bullet>
    (P \<and> Q)[{y}/ac'] \<triangleleft> y.tr = s.tr \<and> y.wait \<triangleright>
    (P \<or> Q)[{y}/ac'] *)
definition extchoice_post ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design" where
[pred]: "extchoice_post P Q = (\<in>\<^sub>a\<^sub>c y. (\<lambda> (s0, ac1).
  (((\<lambda> z. P (s0, ac1) \<and> Q (s0, ac1))
    \<triangleleft> $rad_state.tr = \<guillemotleft>rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0))\<guillemotright> \<and>
       $rad_state.wait \<triangleright>
    (\<lambda> z. P (s0, ac1) \<or> Q (s0, ac1))) y)))"

lemma rad_wait_false_extchoice_post:
  "((extchoice_post P Q) \<^sub>wf) =
   extchoice_post (P \<^sub>wf) (Q \<^sub>wf)"
  by (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_state.wait_def
      rad_state.tr_def SEXP_def rad_wait_false_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def Let_def)

lemma extchoice_post_ok_in_subst:
  "(extchoice_post P Q)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> =
   extchoice_post (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>) (Q\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_state.wait_def
      rad_state.tr_def SEXP_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs des_vars.ok_def
      astate.s_def des_vars.more\<^sub>L_def des_more_ok_update_commute
      Let_def; pred_auto)

(* Paper Definition 44 / Thesis Definition 125. *)
definition extchoice_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design" (infixl "\<box>\<^sub>R\<^sub>A\<^sub>D" 68) where
[pred]: "P \<box>\<^sub>R\<^sub>A\<^sub>D Q = (RA \<circ> A)
  (((\<not> (P \<^sub>wf)\<^sup>f) \<and> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
   extchoice_post ((P \<^sub>wf)\<^sup>t) ((Q \<^sub>wf)\<^sup>t))"

lemma extchoice_post_unrest_ok [unrest]:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "$ok\<^sup>> \<sharp> extchoice_post P Q"
proof -
  have put_P:
      "\<forall> s0 ac1 v. P (s0, ac1\<lparr>des_vars.ok\<^sub>v := v\<rparr>) = P (s0, ac1)"
    using assms(1)
    apply (subst (asm) unrest_lens)
     apply simp
    by (simp add: lens_defs des_vars.ok_def case_prod_beta
        split_paired_All)
  have put_Q:
      "\<forall> s0 ac1 v. Q (s0, ac1\<lparr>des_vars.ok\<^sub>v := v\<rparr>) = Q (s0, ac1)"
    using assms(2)
    apply (subst (asm) unrest_lens)
     apply simp
    by (simp add: lens_defs des_vars.ok_def case_prod_beta
        split_paired_All)
  show ?thesis
    apply (subst unrest_lens)
     apply simp
    apply (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_state.wait_def
      rad_state.tr_def SEXP_def Let_def lens_defs
        des_vars.ok_def case_prod_beta)
    using put_P put_Q
    by (simp add: des_more_ok_update_commute)
qed

lemma extchoice_RAD_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Q is RAD"
  unfolding extchoice_RAD_def
  apply (rule RAD_design_closure)
   apply (rule design_is_H1_H2; simp add: unrest)
  by (simp add: rad_wait_false_distrib rad_wait_false_extchoice_post)

(* Composition with the Stop postcondition reduces both branches to
   the bare singleton choice: the waiting branch of Stop holds exactly
   on the states admitted by the conditional's guard. *)
lemma extchoice_post_stop:
  "extchoice_post X (RA2 (RA1 stop_post)) = \<in>\<^sub>a\<^sub>c(X)"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_stop_post)
  apply (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_state.wait_def
      rad_state.tr_def SEXP_def ades_singleton_choice_def
      RA1_def stop_post_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_state.wait_def astate.s_def
      des_vars.more\<^sub>L_def)
  by (pred_auto; blast)

(* Paper Theorem 32 / Thesis Theorem T.5.4.30:
   Stop is not a unit of external choice in RAD (without A2). *)
(* RA \<circ> A (\<not> P_f^f \<turnstile> \<exists> y \<in> ac'. P_f^t[{y}/ac'])*)
theorem extchoice_RAD_Stop:
  assumes "P is RAD"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D =
    (RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile>
      (\<lambda> (s0, ac'). \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
          ((P \<^sub>wf)\<^sup>t) (s0, des_vars.more_update
              (achoices.ac\<^sub>v_update (\<lambda>_. {y})) ac')))"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f" and ?T = "(P \<^sub>wf)\<^sup>t"
  let ?SF = "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>f"
  let ?ST = "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>t"
  have pre_push:
      "((\<not> ?F) \<and> (\<not> ?SF))\<lbrakk>True/ok\<^sup><\<rbrakk> =
       (\<not> ?F)\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: subst_pred(3,4) Stop_RAD_wf_ok_false_subst
        pred_ba.compl_bot_eq pred_ba.inf_top_right)
  have post_push:
      "(extchoice_post ?T ?ST)\<lbrakk>True/ok\<^sup><\<rbrakk> =
       (\<in>\<^sub>a\<^sub>c(?T))\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: extchoice_post_ok_in_subst
        ades_singleton_choice_ok_in_subst
        Stop_RAD_wf_ok_true_subst extchoice_post_stop)
  have "(((\<not> ?F) \<and> (\<not> ?SF)) \<turnstile> extchoice_post ?T ?ST) =
        ((\<not> ?F) \<turnstile> \<in>\<^sub>a\<^sub>c(?T))"
    using arg_cong2[where f=design, OF pre_push post_push]
    by (simp only: design_subst_ok)
  then show ?thesis
    by (simp only: extchoice_RAD_def ades_singleton_choice_def)
qed

(* Paper Theorem 33 / Thesis Theorem T.5.4.31 *)
theorem extchoice_RAD_Stop_unit:
  assumes "P is RAD" "P is A2"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D = P"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f" and ?T = "(P \<^sub>wf)\<^sup>t"
  have not_F_PBMH: "(\<not> (\<not> ?F)) is PBMH_ades"
    by (simp only: pred_ba.double_compl
        RAD_wf_ok_false_PBMH[OF assms(1)])
  have unrests: "$ok\<^sup>> \<sharp> (\<not> ?F)" "$ok\<^sup>> \<sharp> ?T"
    by (simp_all add: unrest)
  have singleton_reduce:
      "\<in>\<^sub>a\<^sub>c(?T) \<sqsubseteq> (?T \<and> ac_non_empty)"
  proof -
    have fixed: "A2 P = P"
      using assms(2) by (simp add: Healthy_def')
    have "\<in>\<^sub>a\<^sub>c(((A2 P) \<^sub>wf)\<^sup>t) \<sqsubseteq>
        ((((A2 P) \<^sub>wf)\<^sup>t) \<and> ac_non_empty)"
      apply (simp add: A2_def ades_singleton_choice_def ac_non_empty_def
          rad_wait_false_def A2_rel_eq_expanded A2_rel_expanded_def
          pred_refine_iff fun_eq_iff usubst usubst_eval Let_def)
      by (pred_auto; blast)
    then show ?thesis
      by (simp only: fixed)
  qed
  have singleton_weaken: "?T \<sqsubseteq> \<in>\<^sub>a\<^sub>c(?T)"
    using RAD_wf_ok_true_PBMH[OF assms(1)]
    apply (simp add: Healthy_def' PBMH_ades_def PBMH_def pbmh_step_def
        ades_singleton_choice_def pred_refine_iff fun_eq_iff Let_def)
    by (pred_auto; blast)
  have RA1_eq: "RA1 (\<in>\<^sub>a\<^sub>c(?T)) = RA1 ?T"
  proof (rule ref_antisym)
    have absorb: "RA1 (?T \<and> ac_non_empty) = RA1 ?T"
      by (subst pred_ba.inf_commute) (rule RA1_ac_non_empty_absorb)
    show "RA1 (\<in>\<^sub>a\<^sub>c(?T)) \<sqsubseteq> RA1 ?T"
      using RA1_mono[OF singleton_reduce] by (simp only: absorb)
    show "RA1 ?T \<sqsubseteq> RA1 (\<in>\<^sub>a\<^sub>c(?T))"
      by (rule RA1_mono[OF singleton_weaken])
  qed
  have "P \<box>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D =
      (RA \<circ> A) ((\<not> ?F) \<turnstile> \<in>\<^sub>a\<^sub>c(?T))"
    using extchoice_RAD_Stop[OF assms(1)]
    by (simp only: ades_singleton_choice_def)
  also have "... = RA ((\<not> ?F) \<turnstile> \<in>\<^sub>a\<^sub>c(?T))"
    by (rule RA_A_absorb_design[OF not_F_PBMH _ unrests(1)])
      (simp_all add: Healthy_def' unrest unrests)
  also have "... =
      RA ((\<not> ?F) \<turnstile> (RA2 \<circ> RA1) (\<in>\<^sub>a\<^sub>c(?T)))"
    by (rule RA_design_post)
  also have "... = RA ((\<not> ?F) \<turnstile> (RA2 \<circ> RA1) ?T)"
    by (simp only: comp_apply RA1_eq)
  also have "... = RA ((\<not> ?F) \<turnstile> ?T)"
    by (rule RA_design_post[symmetric])
  also have "... = P"
    by (rule RAD_RA_design_form[OF assms(1), symmetric])
  finally show ?thesis .
qed

end
