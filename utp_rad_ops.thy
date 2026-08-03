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
  have D_design: "?D is \<^bold>H"
    by (rule design_is_H1_H2; pred_auto)
  have D_wait: "(?D \<^sub>wf) = ?D"
    by (simp add: rad_wait_false_distrib)
  have "(RA \<circ> A) ?D is RAD"
    by (rule RAD_design_closure[OF D_design D_wait])
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
  have D_design: "?D is \<^bold>H"
    by (rule design_is_H1_H2; pred_auto)
  have D_wait: "(?D \<^sub>wf) = ?D"
    by (simp add: rad_wait_false_distrib)
  have "(RA \<circ> A) ?D is RAD"
    by (rule RAD_design_closure[OF D_design D_wait])
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

lemma Chaos_RAD_RA:
  "Chaos\<^sub>R\<^sub>A\<^sub>D = RA true"
  apply (simp only: Chaos_RAD_alt design_false_pre comp_apply)
  apply (subst RA_A')
   apply (simp add: Healthy_def' H1_H2_comp comp_apply H1_def H2_true)
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma Chaos_RAD_is_RAD [closure]:
  "Chaos\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Chaos_RAD_def
  apply (rule RAD_design_closure)
   apply (rule design_is_H1_H2; pred_auto)
  apply (simp add: rad_wait_false_distrib)
  done

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

lemma Choice_RAD_is_RAD [closure]:
  "Choice\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Choice_RAD_def
  apply (rule RAD_design_closure)
   apply (rule design_is_H1_H2; pred_auto)
  apply (simp add: rad_wait_false_distrib)
  done

(* Paper Theorem 26. *)
theorem Choice_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Choice\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P = (RA \<circ> A) (true \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f"
  let ?T = "(P \<^sub>wf)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  let ?DC = "true \<turnstile> true"
  let ?Z = "(\<not> ok\<^sup><) \<or> ?F \<or> ?T"
  have P_form: "P = (RA \<circ> A) ?DP"
    by (rule RAD_design_form'[OF assms])
  have T_form: "?T = RA2 (RA1 (PBMH_ades ?Z))"
    using arg_cong[where f="\<lambda>R. (R \<^sub>wf)\<^sup>t", OF P_form]
    by (simp only: comp_apply RA_design_wait_false_ok_true')
  have PBMH_true_design:
      "PBMH_ades (true \<turnstile> ?Z) = (true \<turnstile> PBMH_ades ?Z)"
      "PBMH_ades (true \<turnstile> ?T) = (true \<turnstile> PBMH_ades ?T)"
    by (simp_all add: design_as_disj PBMH_ades_disj
        PBMH_ades_conj_ok)
  have normalise:
      "(RA \<circ> A) (true \<turnstile> ?Z) =
       (RA \<circ> A) (true \<turnstile> ?T)"
  proof -
    have "RA (A (true \<turnstile> ?Z)) =
        RA (PBMH_ades (true \<turnstile> ?Z))"
      apply (rule RA_A')
      by (rule design_is_H1_H2; pred_auto)
    also have "... = RA (true \<turnstile> PBMH_ades ?Z)"
      by (simp only: PBMH_true_design(1))
    also have "... = RA (true \<turnstile> RA2 (RA1 (PBMH_ades ?Z)))"
      by (rule RA_design_post[simplified comp_apply])
    also have "... = RA (true \<turnstile> ?T)"
      using arg_cong[where f="\<lambda>X. RA (true \<turnstile> X)",
          OF T_form[symmetric]] .
    also have "... = RA (true \<turnstile> PBMH_ades ?T)"
      by (simp only: Healthy_if[OF RAD_wait_true_PBMH[OF assms]])
    also have "... = RA (PBMH_ades (true \<turnstile> ?T))"
      by (simp only: PBMH_true_design(2))
    also have "... = RA (A (true \<turnstile> ?T))"
      apply (rule RA_A'[symmetric])
      by (rule design_is_H1_H2; pred_auto)
    finally show ?thesis
      by (simp only: comp_apply)
  qed
  have "Choice\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) ?DC \<squnion> (RA \<circ> A) ?DP"
    using arg_cong2[where f=inf, OF Choice_RAD_alt P_form] .
  also have "... = (RA \<circ> A) (?DC \<squnion> ?DP)"
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
    by (rule normalise)
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

end
