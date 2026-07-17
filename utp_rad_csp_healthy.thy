section \<open>Reactive Angelic Designs\<close>

theory utp_rad_csp_healthy
  imports utp_rad_healthy
begin

subsection \<open>CSPA1\<close>

(* Paper definition 33. *)
definition CSPA1 :: "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
"CSPA1 P = (P \<or> RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x))"

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

(* Thesis Theorem T.5.2.18. *)
lemma CSPA1_RA1:
  "CSPA1 (RA1 P) = RA1 (H1 P)"
  apply (simp add: CSPA1_def H1_def RA1_def Let_def)
  apply pred_auto
  done

(* Paper Theorem 10. *)
lemma RA1_CSPA1:
  "RA1 (CSPA1 P) = RA1 (H1 P)"
  apply (simp add: CSPA1_def H1_def RA1_def Let_def)
  apply pred_auto
  done

(* Thesis Theorem T.G.5.4. *)
lemma RA1_CSPA1_commute:
  "RA1 (CSPA1 P) = CSPA1 (RA1 P)"
  by (simp add: RA1_CSPA1 CSPA1_RA1)

subsection \<open>CSPA2\<close>

(* Paper Definition 34. *)
definition CSPA2 :: "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where "CSPA2 P = H2 P"

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
  using assms
  by (simp add: CSPA2_def PBMH_ades_def H2_split fun_eq_iff;
      pred_auto; blast)

subsection \<open>RAD\<close>

(* Paper Definition 35. *)
definition RAD ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
"RAD = RA \<circ> CSPA1 \<circ> CSPA2 \<circ> PBMH_ades"

lemma RAD_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RAD P \<sqsubseteq> RAD Q"
  by (simp add: RAD_def RA_mono CSPA1_mono CSPA2_mono PBMH_ades_mono)

lemma RAD_Monotonic [closure]:
  "Monotonic RAD"
  unfolding RAD_def
  by (intro Monotonic_comp RA_Monotonic CSPA1_Monotonic
      CSPA2_Monotonic PBMH_ades_Monotonic)

end
