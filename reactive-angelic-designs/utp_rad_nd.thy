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
  shows "NDRAD P = (RA \<circ> A) (true \<turnstile> (P \<^sub>wf)\<^sup>t)"
  using Choice_RAD_angelic_choice[OF assms]
  by (simp add: NDRAD_def inf_commute)

(* Paper Theorem 35 / thesis T.5.5.3. The quantifier closes over all
   observations; the (\<not> ok\<^sup><) disjunct makes the not-started case vacuous,
   mirroring the thesis' case analysis on initial ok. *)
theorem NDRAD_fixed_point:
  assumes "P is RAD"
  shows "NDRAD P = P \<longleftrightarrow>
    (\<forall>s0 ac'. ((\<not> ok\<^sup><) \<or> (\<not> (P \<^sub>wf)\<^sup>f)) (s0, ac'))"
proof
  assume fixed: "NDRAD P = P"
  have "((NDRAD P) \<^sub>wf)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> =
      ((P \<^sub>wf)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> \<and>
       (Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>wf)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    unfolding NDRAD_def RAD_angelic_choice
    by (simp only: rad_wait_false_conj usubst)
  also have "... = false"
    by (simp only: Choice_RAD_wf_ok_false_subst; pred_auto)
  finally have failure_false:
      "(P \<^sub>wf)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: fixed)
  show "\<forall>s0 ac'.
      ((\<not> ok\<^sup><) \<or> (\<not> (P \<^sub>wf)\<^sup>f)) (s0, ac')"
    using failure_false
    by (simp add: fun_eq_iff usubst usubst_eval; pred_auto)
next
  assume nondiv:
    "\<forall>s0 ac'.
      ((\<not> ok\<^sup><) \<or> (\<not> (P \<^sub>wf)\<^sup>f)) (s0, ac')"
  have guard_true:
      "(\<not> (P \<^sub>wf)\<^sup>f)\<lbrakk>True/ok\<^sup><\<rbrakk> = true"
    using nondiv
    by (simp add: fun_eq_iff usubst usubst_eval; pred_auto)
  have design_eq:
      "((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t) =
       (true \<turnstile> (P \<^sub>wf)\<^sup>t)"
    by (metis design_subst_ok guard_true pred_true_ok_in_subst)
  show "NDRAD P = P"
    by (simp only: NDRAD_design_form[OF assms] design_eq[symmetric]
        RAD_design_form'[OF assms, symmetric])
qed

(* Paper Example 20: divergence is avoided at the bottom of the lattice. *)
lemma NDRAD_Chaos:
  "NDRAD Chaos\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  unfolding NDRAD_def
  by (rule Chaos_RAD_angelic_choice[OF Choice_RAD_is_RAD])

lemma NDRAD_Choice:
  "NDRAD Choice\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  by (simp add: NDRAD_def)

end
