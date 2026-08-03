section \<open>Reactive Angelic Design Operators\<close>

theory utp_rad_ops
  imports utp_rad_csp
begin

subsection \<open>Angelic Choice\<close>

(* Paper Definition 37. *)
abbreviation achoice_RAD ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
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
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
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
theorem RAD_demonic_choice_CSP:
  "rad_p2ac (rad_ac2p P \<sqinter> rad_ac2p Q) =
   rad_p2ac (rad_ac2p P) \<sqinter>\<^sub>R\<^sub>A\<^sub>D rad_p2ac (rad_ac2p Q)"
  by (rule rad_p2ac_disj[simplified disj_pred_def])

(* Paper Lemma 7 / Thesis Lemma L.5.4.1. *)
lemma RAD_demonic_choice_CSP_A2:
  assumes "P is RAD" "Q is RAD"
    and "P is A2" "Q is A2"
  shows "rad_p2ac (rad_ac2p P \<sqinter> rad_ac2p Q) = P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q"
  by (simp only: RAD_demonic_choice_CSP
      rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

(* Paper Theorem 24 / Thesis Theorem T.5.4.6. *)
theorem RAD_demonic_choice_CSP_inverse:
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
definition Chaos_RAD :: "'e reactive_angelic_design" ("Chaos\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Chaos_RAD = (RA \<circ> A) (false \<turnstile> ac_non_empty)"

lemma Chaos_RAD_alt:
  "Chaos\<^sub>R\<^sub>A\<^sub>D = (RA \<circ> A) (false \<turnstile> true)"
  by (simp only: Chaos_RAD_def design_false_pre)

lemma Chaos_RAD_RA: "Chaos\<^sub>R\<^sub>A\<^sub>D = RA true"
  apply (simp only: Chaos_RAD_alt design_false_pre comp_apply)
  apply (subst RA_A')
   apply (simp add: Healthy_def' H1_H2_comp comp_apply H1_def H2_true)
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma Chaos_RAD_is_RAD [closure]: "Chaos\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Chaos_RAD_def
  by rad_closure

(* Paper Theorem 25. *)
theorem Chaos_RAD_angelic_choice:
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
theorem Chaos_RAD_demonic_choice:
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
definition Choice_RAD :: "'e reactive_angelic_design" ("Choice\<^sub>R\<^sub>A\<^sub>D") where
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
     apply (rule design_is_H1_H2; pred_auto)
    by (rule rad_wait_false_design_is_H)
  also have "... = (RA \<circ> A) (true \<turnstile> ?Z)"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  also have "... = (RA \<circ> A) (true \<turnstile> ?T)"
    apply (rule RA_A_true_design_post)
       apply (rule design_is_H1_H2; pred_auto)
      apply (rule design_is_H1_H2; pred_auto)
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

(* \<exists> y \<in> ac' \<bullet> y.tr = s.tr \<and> y.wait *)
definition stop_post :: "'e reactive_angelic_design" where
[pred]: "stop_post = (\<lambda> (x, y).
  \<exists> z \<in> achoices.ac\<^sub>v (des_vars.more y).
    rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<and>
    rad_state.wait\<^sub>v z)"

(* Paper Definition 41. *)
definition Stop_RAD :: "'e reactive_angelic_design" ("Stop\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Stop_RAD = (RA \<circ> A) (true \<turnstile> stop_post)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma stop_post_p2ac:
  "stop_post = p2ac \<lceil>(\<lambda> (s, y).
    rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s \<and> rad_state.wait\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: stop_post_def p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma stop_post_PBMH [simp]: "PBMH_ades stop_post = stop_post"
  by (simp only: stop_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_stop_post: "(stop_post \<^sub>wf) = stop_post"
  by (simp add: stop_post_def rad_wait_false_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma stop_post_unrest_ok [unrest]: "$ok\<^sup>> \<sharp> stop_post"
  apply (simp add: unrest_lens stop_post_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma stop_design_is_H [closure]: "(true \<turnstile> stop_post) is \<^bold>H"
  by (rule design_is_H1_H2; simp add: unrest)

lemma Stop_RAD_is_RAD [closure]: "Stop\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Stop_RAD_def
  apply (rule RAD_design_closure)
   apply (rule stop_design_is_H)
  by (simp add: rad_wait_false_distrib rad_wait_false_stop_post)

(* Paper Theorem 28. *)
theorem Stop_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile>
      (((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t) \<and> stop_post))"
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

(* \<exists> y \<in> ac' \<bullet> \<not> y.wait \<and> y.tr = s.tr *)
definition skip_post :: "'e reactive_angelic_design" where
[pred]: "skip_post = (\<lambda> (x, y).
  \<exists> z \<in> achoices.ac\<^sub>v (des_vars.more y).
    \<not> rad_state.wait\<^sub>v z \<and>
    rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x)))"

(* Paper Definition 42. *)
definition Skip_RAD :: "'e reactive_angelic_design" ("Skip\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Skip_RAD = (RA \<circ> A) (true \<turnstile> skip_post)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma skip_post_p2ac:
  "skip_post = p2ac \<lceil>(\<lambda> (s, y).
    \<not> rad_state.wait\<^sub>v y \<and> rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s)\<rceil>\<^sub>D"
  by (simp add: skip_post_def p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma skip_post_PBMH [simp]: "PBMH_ades skip_post = skip_post"
  by (simp only: skip_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_skip_post: "(skip_post \<^sub>wf) = skip_post"
  by (simp add: skip_post_def rad_wait_false_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma skip_post_unrest_ok [unrest]: "$ok\<^sup>> \<sharp> skip_post"
  apply (simp add: unrest_lens skip_post_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma skip_design_is_H [closure]: "(true \<turnstile> skip_post) is \<^bold>H"
  by (rule design_is_H1_H2; simp add: unrest)

lemma Skip_RAD_is_RAD [closure]: "Skip\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Skip_RAD_def
  apply (rule RAD_design_closure)
   apply (rule skip_design_is_H)
  by (simp add: rad_wait_false_distrib rad_wait_false_skip_post)

(* Paper Theorem 29. *)
theorem Skip_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Skip\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile>
      (skip_post \<and> ((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t)))"
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

end
