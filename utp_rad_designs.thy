section \<open>Reactive Angelic Designs\<close>

theory utp_rad_designs
  imports utp_rad_healthy
begin

subsection \<open>CSPA1\<close>

(* Paper definition 33. *)
definition CSPA1 :: "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
[pred]: "CSPA1 P = (P \<or> RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x))"

lemma CSPA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA1 P \<sqsubseteq> CSPA1 Q"
  by (simp add: CSPA1_def, pred_auto)

lemma CSPA1_Monotonic [closure]:
  "Monotonic CSPA1"
  by (rule MonotonicI, rule CSPA1_mono)

(* Thesis Theorem T.G.5.1. *)
lemma CSPA1_idem:
  "CSPA1 (CSPA1 P) = CSPA1 P"
  by (simp add: CSPA1_def fun_eq_iff; pred_auto)

lemma CSPA1_Idempotent [closure]:
  "Idempotent CSPA1"
  by (simp add: Idempotent_def CSPA1_idem)

(* Thesis Theorem T.5.2.19. *)
lemma PBMH_ades_CSPA1:
  assumes "PBMH_ades P = P"
  shows "PBMH_ades (CSPA1 P) = CSPA1 P"
  by (simp add: CSPA1_def PBMH_ades_disj assms)

(* Paper Theorem 10. *)
lemma RA1_CSPA1:
  "(RA1 \<circ> CSPA1) P = (RA1 \<circ> H1) P"
  apply (simp add: CSPA1_def H1_def RA1_def Let_def)
  apply pred_auto
  done

(* Thesis Theorem T.5.2.18. *)
lemma CSPA1_RA1:
  "(CSPA1 \<circ> RA1) P = (RA1 \<circ> H1) P"
proof -
  have "(CSPA1 \<circ> RA1) P = (RA1 \<circ> CSPA1) P"
    by (simp add: CSPA1_def RA1_disj RA1_idem)
  also have "... = (RA1 \<circ> H1) P"
    by (rule RA1_CSPA1)
  finally show ?thesis .
qed

(* Thesis Theorem T.G.5.4. *)
lemma RA1_CSPA1_commute:
  "(RA1 \<circ> CSPA1) P = (CSPA1 \<circ> RA1) P"
  by (simp add: RA1_CSPA1[simplified comp_apply]
      CSPA1_RA1[simplified comp_apply])

lemma RA_CSPA1:
  "(RA \<circ> CSPA1) P = (RA \<circ> H1) P"
  by (simp add: RA_def RA1_RA2_commute[simplified comp_apply]
      RA1_RA3_commute[simplified comp_apply]
      RA2_RA3_commute[simplified comp_apply]
      RA1_CSPA1[simplified comp_apply])

subsection \<open>CSPA2\<close>

(* Paper Definition 34. *)
definition CSPA2 :: "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where [pred]: "CSPA2 P = H2 P"

lemma CSPA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA2 P \<sqsubseteq> CSPA2 Q"
  using Continuous_Monotonic[OF H2_Continuous]
  by (simp add: CSPA2_def Monotonic_refine; blast)

lemma CSPA2_Monotonic [closure]:
  "Monotonic CSPA2"
  unfolding CSPA2_def
  by (rule Continuous_Monotonic[OF H2_Continuous])

lemma CSPA2_idem:
  "CSPA2 (CSPA2 P) = CSPA2 P"
  by (simp add: CSPA2_def H2_idem)

lemma CSPA2_Idempotent [closure]:
  "Idempotent CSPA2"
  by (simp add: Idempotent_def CSPA2_idem)

lemma PBMH_ades_CSPA2:
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
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
[pred]: "RAD = RA \<circ> CSPA1 \<circ> CSPA2 \<circ> PBMH_ades"

lemma RAD_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RAD P \<sqsubseteq> RAD Q"
  by (simp add: RAD_def RA_mono CSPA1_mono CSPA2_mono PBMH_ades_mono)

lemma RAD_Monotonic [closure]:
  "Monotonic RAD"
  unfolding RAD_def
  by (intro Monotonic_comp RA_Monotonic CSPA1_Monotonic
      CSPA2_Monotonic PBMH_ades_Monotonic)

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
        RA_A[OF design_healthy, simplified comp_apply]
        PBMH_ades_H1_H2[simplified comp_apply])
  also have "... = RA (A (H1 (H2 (P \<^sub>wf))))"
    unfolding RA_def comp_apply
    by (simp only: RA3_wait_false[simplified comp_apply,
          of "A (H1 (H2 P))"]
        rad_wait_false_A[simplified comp_apply]
        rad_wait_false_H1_H2[simplified comp_apply])
  finally show ?thesis
    by (simp add: H1_H2_eq_design)
qed

lemma RAD_idem:
  "RAD (RAD P) = RAD P"
  by (simp only: RAD_design_form RA_design_form_idem)

lemma RAD_Idempotent [closure]:
  "Idempotent RAD"
  by (simp add: Idempotent_def RAD_idem)

lemma RAD_healthy [closure]:
  "RAD P is RAD"
  by (simp add: Healthy_def' RAD_idem)

end
