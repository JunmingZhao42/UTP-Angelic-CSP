section \<open>Reactive Angelic Designs\<close>

theory utp_rad_designs
  imports utp_rad_healthy
begin

subsection \<open>CSPA1\<close>

(* Paper definition 33. *)
definition CSPA1 :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "CSPA1 P = (P \<or> RA1 (\<not> ok\<^sup><))"

lemma CSPA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA1 P \<sqsubseteq> CSPA1 Q"
  by (simp add: CSPA1_def, pred_auto)

lemma CSPA1_Monotonic [closure]: "Monotonic CSPA1"
  by (rule MonotonicI, rule CSPA1_mono)

(* Thesis Theorem T.G.5.1. *)
lemma CSPA1_idem: "CSPA1 (CSPA1 P) = CSPA1 P"
  by (simp add: CSPA1_def fun_eq_iff; pred_auto)

lemma CSPA1_Idempotent [closure]: "Idempotent CSPA1"
  by (simp add: Idempotent_def CSPA1_idem)

(* Thesis Theorem T.5.2.19. *)
lemma CSPA1_PBMH_ades_closure:
  assumes "PBMH_ades P = P"
  shows "PBMH_ades (CSPA1 P) = CSPA1 P"
  by (simp add: CSPA1_def PBMH_ades_disj assms)

(* Paper Theorem 10. *)
theorem RA1_CSPA1: "(RA1 \<circ> CSPA1) P = (RA1 \<circ> H1) P"
  apply (simp add: CSPA1_def H1_def RA1_def Let_def)
  apply pred_auto
  done

(* Thesis Theorem T.5.2.18. *)
lemma CSPA1_RA1: "(CSPA1 \<circ> RA1) P = (RA1 \<circ> H1) P"
proof -
  have "(CSPA1 \<circ> RA1) P = (RA1 \<circ> CSPA1) P"
    by (simp add: CSPA1_def RA1_disj RA1_idem)
  also have "... = (RA1 \<circ> H1) P"
    by (rule RA1_CSPA1)
  finally show ?thesis .
qed

(* Thesis Theorem T.G.5.4. *)
lemma RA1_CSPA1_commute: "(RA1 \<circ> CSPA1) P = (CSPA1 \<circ> RA1) P"
  by (simp add: RA1_CSPA1[simplified comp_apply]
      CSPA1_RA1[simplified comp_apply])

lemma RA_CSPA1: "(RA \<circ> CSPA1) P = (RA \<circ> H1) P"
  by (simp add: RA_def RA_comms RA1_CSPA1[simplified comp_apply])

subsection \<open>CSPA2\<close>

(* Paper Definition 34. *)
definition CSPA2 :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
where [pred]: "CSPA2 P = H2 P"

lemma CSPA2_Monotonic [closure]: "Monotonic CSPA2"
  unfolding CSPA2_def
  by (rule Continuous_Monotonic[OF H2_Continuous])

lemma CSPA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA2 P \<sqsubseteq> CSPA2 Q"
  using CSPA2_Monotonic by (auto simp add: Monotonic_refine)

lemma CSPA2_idem: "CSPA2 (CSPA2 P) = CSPA2 P"
  by (simp add: CSPA2_def H2_idem)

lemma CSPA2_Idempotent [closure]: "Idempotent CSPA2"
  by (simp add: Idempotent_def CSPA2_idem)

lemma CSPA2_PBMH_ades_closure:
  assumes "PBMH_ades P = P"
  shows "PBMH_ades (CSPA2 P) = CSPA2 P"
proof -
  have ok_substs:
    "PBMH_ades (P\<^sup>f) = (PBMH_ades P)\<^sup>f \<and>
     PBMH_ades (P\<^sup>t) = (PBMH_ades P)\<^sup>t"
    by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)
  show ?thesis
    using assms ok_substs
    by (simp add: CSPA2_def H2_split PBMH_ades_disj
        PBMH_ades_conj_ok)
qed

subsection \<open>RAD\<close>

(* Paper Definition 35. *)
definition RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RAD = RA \<circ> CSPA1 \<circ> CSPA2 \<circ> PBMH_ades"

lemma RAD_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RAD P \<sqsubseteq> RAD Q"
  by (simp add: RAD_def RA_mono CSPA1_mono CSPA2_mono PBMH_ades_mono)

lemma RAD_Monotonic [closure]: "Monotonic RAD"
  unfolding RAD_def
  by (intro Monotonic_comp RA_Monotonic CSPA1_Monotonic
      CSPA2_Monotonic PBMH_ades_Monotonic)

lemma RAD_PBMH_ades_healthy [closure]: "RAD P is PBMH_ades"
  unfolding RAD_def comp_apply
  apply (rule RA_PBMH_ades_closure)
  apply (simp only: Healthy_def')
  apply (rule CSPA1_PBMH_ades_closure)
  apply (rule CSPA2_PBMH_ades_closure)
  by (simp only: PBMH_ades_idem)

lemma RAD_is_PBMH_ades [closure]:
  assumes "P is RAD"
  shows "P is PBMH_ades"
  using RAD_PBMH_ades_healthy[of P] assms
  by (simp only: Healthy_def')

lemma RAD_H1_H2_PBMH:
  "RAD P = (RA \<circ> H1 \<circ> H2 \<circ> PBMH_ades) P"
  by (simp add: RAD_def CSPA2_def RA_CSPA1[simplified comp_apply])

(* Paper Theorem 11. *)
theorem RAD_design_form:
  "RAD P = (RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  have design_healthy: "H1 (H2 P) is \<^bold>H"
    by (simp only: Healthy_def' H1_H2_idempotent)
  have "RAD P = RA (A (H1 (H2 P)))"
    by (simp only: comp_apply RAD_H1_H2_PBMH
        RA_A'[OF design_healthy]
        PBMH_ades_H1_H2_commute[simplified comp_apply])
  also have "... = RA (A (H1 (H2 (P \<^sub>wf))))"
    unfolding RA_def comp_apply
    by (simp only: RA3_wait_false_absorb[simplified comp_apply,
          of "A (H1 (H2 P))"]
        rad_wait_false_A_commute[simplified comp_apply]
        rad_wait_false_H1_H2_commute[simplified comp_apply])
  finally show ?thesis
    by (simp add: H1_H2_eq_design)
qed

(* Paper Theorem 11, as an elimination rule for RAD-healthy predicates. *)
lemma RAD_design_form':
  assumes "P is RAD"
  shows "P = (RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
  using assms by (simp only: Healthy_def' RAD_design_form)

lemma RAD_wf_ok_false_PBMH:
  assumes "P is RAD"
  shows "(P \<^sub>wf)\<^sup>f is PBMH_ades"
proof -
  have component: "(P \<^sub>wf)\<^sup>f =
      RA2 (RA1 (PBMH_ades ((\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f)))"
    using arg_cong[where f="\<lambda>R. (R \<^sub>wf)\<^sup>f",
        OF RAD_design_form'[OF assms]]
    by (simp only: comp_apply RA_design_wf_ok_false')
  show ?thesis
    unfolding Healthy_def'
    using PBMH_ades_RA2_RA1_absorb[of "(\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f"]
    by (simp only: component[symmetric])
qed

lemma RAD_wf_ok_true_PBMH:
  assumes "P is RAD"
  shows "(P \<^sub>wf)\<^sup>t is PBMH_ades"
proof -
  have component: "(P \<^sub>wf)\<^sup>t =
      RA2 (RA1 (PBMH_ades
        ((\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f \<or> (P \<^sub>wf)\<^sup>t)))"
    using arg_cong[where f="\<lambda>R. (R \<^sub>wf)\<^sup>t",
        OF RAD_design_form'[OF assms]]
    by (simp only: comp_apply RA_design_wf_ok_true')
  show ?thesis
    unfolding Healthy_def'
    using PBMH_ades_RA2_RA1_absorb[of
        "(\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f \<or> (P \<^sub>wf)\<^sup>t"]
    by (simp only: component[symmetric])
qed

(* The normal-form design of a RAD-healthy predicate has PBMH-healthy
   components. *)
lemma RAD_design_PBMH:
  assumes "P is RAD"
  shows "((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t) is PBMH_ades"
  by (rule PBMH_ades_design_closure;
      intro RAD_wf_ok_false_PBMH[OF assms] RAD_wf_ok_true_PBMH[OF assms])

(* The RAD normal form with the A stripped: RAD-healthy predicates are
   RA images of their wait-false design. *)
lemma RAD_RA_design_form:
  assumes "P is RAD"
  shows "P = RA ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
  using RAD_design_form'[OF assms]
  by (simp only: RA_A_absorb[OF RAD_design_PBMH[OF assms]
        rad_wait_false_design_is_H])

lemma RAD_idem: "RAD (RAD P) = RAD P"
  by (simp only: RAD_design_form RA_design_form_idem)

lemma RAD_Idempotent [closure]: "Idempotent RAD"
  by (simp add: Idempotent_def RAD_idem)

lemma RAD_healthy [closure]: "RAD P is RAD"
  by (simp add: Healthy_def' RAD_idem)

lemma RAD_is_RA [closure]:
  assumes "P is RAD"
  shows "P is RA"
proof -
  have "RAD P is RA"
    unfolding RAD_def comp_apply
    by (rule RA_healthy)
  then show ?thesis
    using assms by (simp only: Healthy_def')
qed

lemma RAD_design_closure:
  assumes "P is \<^bold>H" "(P \<^sub>wf) = P"
  shows "(RA \<circ> A) P is RAD"
proof -
  have normal_form:
      "(\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t = P"
    using assms
    by (simp only: Healthy_def' H1_H2_eq_design)
  show ?thesis
    using RAD_healthy[of P]
    by (simp only: RAD_design_form normal_form)
qed

text \<open>
  Closure method for operators in RAD normal form
  \<open>(RA \<circ> A) (F \<turnstile> T)\<close>: discharges the design-healthiness obligation by
  @{method pred_auto} and the wait-false fixed-point obligation by
  @{thm [source] rad_wait_false_distrib}.  Extra simp rules (for example an
  operator's definition) can be passed via \<open>add\<close>.
\<close>

method rad_closure uses add =
  (rule RAD_design_closure,
   (rule design_is_H1_H2; pred_auto),
   (simp add: rad_wait_false_distrib add))

end
