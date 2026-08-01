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
  have P_form: "P = (RA \<circ> A) ?DP"
    using assms(1) by (simp only: Healthy_def' RAD_design_form)
  have Q_form: "Q = (RA \<circ> A) ?DQ"
    using assms(2) by (simp only: Healthy_def' RAD_design_form)
  have DP_PBMH: "?DP is PBMH_ades"
    by (rule PBMH_ades_design_closure;
        intro RAD_wait_false_PBMH[OF assms(1)]
          RAD_wait_true_PBMH[OF assms(1)])
  have DQ_PBMH: "?DQ is PBMH_ades"
    by (rule PBMH_ades_design_closure;
        intro RAD_wait_false_PBMH[OF assms(2)]
          RAD_wait_true_PBMH[OF assms(2)])
  have DP_design: "?DP is \<^bold>H"
    by (rule rad_wait_false_design_healthy)
  have DQ_design: "?DQ is \<^bold>H"
    by (rule rad_wait_false_design_healthy)
  have "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q =
      (RA \<circ> A) ?DP \<squnion> (RA \<circ> A) ?DQ"
    using arg_cong2[where f=inf, OF P_form Q_form] .
  also have "... = (RA \<circ> A) (?DP \<squnion> ?DQ)"
    by (rule RA_A_angelic_choice[OF
          DP_PBMH DQ_PBMH DP_design DQ_design])
  also have "... = (RA \<circ> A)
        (((\<not> (P \<^sub>wf)\<^sup>f) \<or> (\<not> (Q \<^sub>wf)\<^sup>f)) \<turnstile>
         (((\<not> (P \<^sub>wf)\<^sup>f) \<longrightarrow> (P \<^sub>wf)\<^sup>t) \<and>
          ((\<not> (Q \<^sub>wf)\<^sup>f) \<longrightarrow> (Q \<^sub>wf)\<^sup>t)))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
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
    apply (simp only: RAD_angelic_choice distribute
        rad_ac2p_p2ac[simplified comp_apply])
    by (simp only: conj_pred_def)
qed

(* Paper Theorem 21 / Thesis Theorem T.5.4.3. *)
theorem RAD_angelic_choice_CSP_refine:
  assumes "P is RAD" "Q is RAD"
  shows "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q \<sqsubseteq> rad_p2ac (rad_ac2p P \<squnion> rad_ac2p Q)"
proof -
  have P_PBMH: "P is PBMH_ades"
    using RAD_PBMH_ades_healthy[of P] assms(1)
    by (simp only: Healthy_def')
  have Q_PBMH: "Q is PBMH_ades"
    using RAD_PBMH_ades_healthy[of Q] assms(2)
    by (simp only: Healthy_def')
  have P_round: "P \<sqsubseteq> rad_p2ac (rad_ac2p P)"
    by (rule rad_p2ac_ac2p_refine[OF P_PBMH, simplified comp_apply])
  have Q_round: "Q \<sqsubseteq> rad_p2ac (rad_ac2p Q)"
    by (rule rad_p2ac_ac2p_refine[OF Q_PBMH, simplified comp_apply])
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

end
