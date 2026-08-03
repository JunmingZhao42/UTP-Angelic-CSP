section \<open>Non-Divergent Reactive Angelic Designs\<close>

theory utp_rad_nd
  imports utp_rad_ops
begin

(* Paper Definition 45: the angelic choice with the most nondeterministic
   non-divergent process. *)
definition NDRAD ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
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
  shows "NDRAD P = (RA \<circ> A) (true \<turnstile> (P \<^sub>wf)\<^sup>t)"
  using Choice_RAD_angelic_choice[OF assms]
  by (simp add: NDRAD_def inf_commute)

(* Paper Example 20: divergence is avoided at the bottom of the lattice. *)
lemma NDRAD_Chaos:
  "NDRAD Chaos\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  unfolding NDRAD_def
  by (rule Chaos_RAD_angelic_choice[OF Choice_RAD_is_RAD])

lemma NDRAD_Choice:
  "NDRAD Choice\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  by (simp add: NDRAD_def)

end
