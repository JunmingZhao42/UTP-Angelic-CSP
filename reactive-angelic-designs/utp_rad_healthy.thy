section \<open>Reactive Angelic Design Healthiness Conditions\<close>

theory utp_rad_healthy
  imports utp_rad_trace
begin

subsection \<open>Wait-false substitution\<close>

abbreviation rad_wait_lens where
"rad_wait_lens \<equiv>
  rad_wait ;\<^sub>L astate.s ;\<^sub>L des_vars.more\<^sub>L"

(* P_f \<equiv> P[s\<oplus>(wait \<mapsto> false)/s] *)
definition rad_wait_false ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "rad_wait_false P \<equiv> P\<lbrakk>False/rad_wait_lens\<^sup><\<rbrakk>"

no_notation wait_f ("_\<^sub>f" [1000] 1000)

notation rad_wait_false ("_\<^sub>f" [1000] 1000)

lemma A2_wait_cond:
  "A2 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (A2 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> A2 Q)"
  by (simp add: A2_def expr_if_def fun_eq_iff)

lemma rad_wait_cond_not:
  "(\<not> (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       (Q :: ('t::trace, 'e) reactive_angelic_design))) =
   ((\<not> P) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> Q))"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_impl:
  "((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (Q :: ('t::trace, 'e) reactive_angelic_design)) \<longrightarrow>
    (R \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> S)) =
   ((P \<longrightarrow> R) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (Q \<longrightarrow> S))"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_false:
  "(false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    (Q :: ('t::trace, 'e) reactive_angelic_design)) =
   ((\<not> rad_wait_lens\<^sup><) \<and> Q)"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_conj_distrib:
  fixes C A B :: "('t::trace, 'e) reactive_angelic_design"
  shows "(C \<and> (A \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> B)) =
    ((C \<and> A) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (C \<and> B))"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_unrest_ok_out [unrest]:
  "\<lbrakk> $ok\<^sup>> \<sharp> P; $ok\<^sup>> \<sharp> Q \<rbrakk> \<Longrightarrow>
   $ok\<^sup>> \<sharp> (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q)"
  by (simp add: unrest_lens expr_if_def)

lemma rad_wait_cond_unrest_ok_in [unrest]:
  "\<lbrakk> $ok\<^sup>< \<sharp> P; $ok\<^sup>< \<sharp> Q \<rbrakk> \<Longrightarrow>
   $ok\<^sup>< \<sharp> (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q)"
  apply (simp add: unrest_lens expr_if_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma rad_wait_atom_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> ((rad_wait_lens\<^sup><) :: ('t::trace, 'e) reactive_angelic_design)"
  apply (simp add: unrest_lens)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      subst_ext_def SEXP_def lens_defs alpha_defs)
  done

lemma rad_wait_cond_ok_in_subst:
  "((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> =
   (P\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    Q\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: expr_if_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_atom_ok_in_subst [usubst]:
  "((rad_wait_lens\<^sup><) ::
    ('t::trace, 'e) reactive_angelic_design)\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> =
   (rad_wait_lens\<^sup><)"
  by (simp add: fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_as_state_subst:
  "rad_wait_false P =
   ades_state_subst
     (subst_upd subst_id (rad_wait ;\<^sub>L astate.s) (\<lambda>_. False)) P"
  by (simp add: rad_wait_false_def subst_app_def subst_upd_def
      subst_id_def subst_aext_def fun_eq_iff lens_defs)

lemma rad_wait_false_A_commute:
  "(rad_wait_false \<circ> A) P = (A \<circ> rad_wait_false) P"
  by (simp add: rad_wait_false_as_state_subst A_state_subst)

text \<open>
  Distribution kit for @{const rad_wait_false}: the substitution passes
  through the propositional connectives, the design turnstile, and the
  @{term "ok\<^sup>>"} substitutions, and is idempotent.  Together these discharge
  the \<open>(?D \<^sub>f) = ?D\<close> obligations of operator closure proofs by @{method simp}.
\<close>

lemma rad_wait_false_idem: "((P \<^sub>f) \<^sub>f) = P \<^sub>f"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_not: "((\<not> P) \<^sub>f) = (\<not> P \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_conj: "((P \<and> Q) \<^sub>f) = (P \<^sub>f \<and> Q \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_disj: "((P \<or> Q) \<^sub>f) = (P \<^sub>f \<or> Q \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_impl: "((P \<longrightarrow> Q) \<^sub>f) = (P \<^sub>f \<longrightarrow> Q \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_ok_false: "((P\<^sup>f) \<^sub>f) = ((P \<^sub>f)\<^sup>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_ok_true: "((P\<^sup>t) \<^sub>f) = ((P \<^sub>f)\<^sup>t)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_ok_out: "((ok\<^sup>> :: ('t::trace, 'e) reactive_angelic_design) \<^sub>f) = ok\<^sup>>"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def; pred_auto)

lemma rad_wait_false_design: "((P \<turnstile> Q) \<^sub>f) = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by (simp add: rad_wait_false_def design_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_true: "(true \<^sub>f) = true"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_false: "(false \<^sub>f) = false"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_ac_non_empty: "(ac_non_empty \<^sub>f) = ac_non_empty"
  by (simp add: rad_wait_false_def ac_non_empty_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_RA1_commute: "((RA1 P) \<^sub>f) = RA1 (P \<^sub>f)"
  by (simp add: rad_wait_false_def RA1_def fun_eq_iff Let_def
      rad_trace_extensions_def subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs;
      pred_auto)

(* Wait-false substitution affects the initial observation of the left
   operand.  The intermediate state supplied to the right operand is chosen
   afresh by full-alphabet angelic composition. *)
lemma rad_wait_false_aseq_ades: "((P ;;\<^sub>A\<^sub>R Q) \<^sub>f) = ((P \<^sub>f) ;;\<^sub>A\<^sub>R Q)"
  by (simp add: rad_wait_false_def aseq_ades_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemmas rad_wait_false_distrib =
  rad_wait_false_design rad_wait_false_not rad_wait_false_conj
  rad_wait_false_disj rad_wait_false_impl rad_wait_false_ok_false
  rad_wait_false_ok_true rad_wait_false_idem rad_wait_false_true
  rad_wait_false_false rad_wait_false_ac_non_empty
  rad_wait_false_RA1_commute rad_wait_false_aseq_ades

lemma PBMH_ades_wait_cond:
  "PBMH_ades (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (PBMH_ades P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    PBMH_ades Q)"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def expr_if_def
      fun_eq_iff lens_defs; pred_auto; blast)

lemma rad_wait_cond_PBMH_ades_closure [closure]:
  "\<lbrakk> P is PBMH_ades; Q is PBMH_ades \<rbrakk> \<Longrightarrow>
   (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) is PBMH_ades"
  by (simp add: Healthy_def' PBMH_ades_wait_cond)

lemma RA1_wait_cond:
  "RA1 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (RA1 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 Q)"
  by (simp add: RA1_def expr_if_def fun_eq_iff Let_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA2_wait_cond:
  "RA2 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (RA2 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 Q)"
  by (simp add: RA2_def expr_if_def fun_eq_iff Let_def lens_defs
      rad_zero_trace_def rad_wait_def astate.s_def
      des_vars.more\<^sub>L_def)

lemma RA2_not_wait_conj:
  "RA2 ((\<not> rad_wait_lens\<^sup><) \<and> X) =
   ((\<not> rad_wait_lens\<^sup><) \<and> RA2 X)"
proof -
  have "RA2 ((\<not> rad_wait_lens\<^sup><) \<and> X) =
      RA2 (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> X)"
    by (simp only: rad_wait_cond_false)
  also have "... = (RA2 false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 X)"
    by (simp only: RA2_wait_cond)
  also have "... = (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 X)"
    by (simp only: RA2_false)
  also have "... = ((\<not> rad_wait_lens\<^sup><) \<and> RA2 X)"
    by (simp only: rad_wait_cond_false)
  finally show ?thesis .
qed

subsection \<open>RA3: Waiting\<close>

(* Paper Definition 31. *)
definition RA3 ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA3 P \<equiv> (II_Rac \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)"

lemma RA3_eval:
  "RA3 P (x, z) \<longleftrightarrow>
   (if rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
    then II_Rac (x, z) else P (x, z))"
  by (simp add: RA3_def expr_if_def SEXP_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA3_idem: "RA3 (RA3 P) = RA3 P"
  by (simp add: RA3_def)

lemma RA3_Idempotent [closure]: "Idempotent RA3"
  by (simp add: Idempotent_def RA3_idem)

lemma RA3_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA3 P \<sqsubseteq> RA3 Q"
  by (simp add: RA3_def, pred_auto)

lemma RA3_Monotonic [closure]: "Monotonic RA3"
  by (rule MonotonicI, rule RA3_mono)

(* Thesis Theorem T.G.3.3. *)
lemma RA3_II_Rac: "RA3 II_Rac = II_Rac"
  by (simp add: RA3_def)

lemma II_Rac_is_RA3 [closure]: "II_Rac is RA3"
  by (rule Healthy_intro, rule RA3_II_Rac)

(* Thesis Theorem T.5.2.12. *)
lemma RA3_conj: "RA3 (P \<and> Q) = (RA3 P \<and> RA3 Q)"
  by (simp add: RA3_def expr_if_def fun_eq_iff; pred_auto)

(* Thesis Theorem T.5.2.13. *)
lemma RA3_disj: "RA3 (P \<or> Q) = (RA3 P \<or> RA3 Q)"
  by (simp add: RA3_def expr_if_def fun_eq_iff; pred_auto)

lemma RA3_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "RA3 P is PBMH_ades"
  using assms
  by (simp add: Healthy_def' RA3_def PBMH_ades_wait_cond)

(* Thesis Theorem T.5.2.15. *)
lemma PBMH_ades_RA3_absorb:
  "(PBMH_ades \<circ> RA3 \<circ> PBMH_ades) P = (RA3 \<circ> PBMH_ades) P"
  using RA3_PBMH_ades_closure[of "PBMH_ades P"]
  by (simp add: Healthy_def' PBMH_ades_idem)

(* Paper Theorem 68.  The paper's theorem statement repeats
   RA3 \<circ> RA1 on both sides, but its proof establishes this commutation law. *)
theorem RA1_RA3_commute: "(RA1 \<circ> RA3) P = (RA3 \<circ> RA1) P"
  by (simp add: RA3_def RA1_wait_cond RA1_II_Rac)

(* Paper Theorem 69 *)
theorem RA2_RA3_commute: "(RA2 \<circ> RA3) P = (RA3 \<circ> RA2) P"
  by (simp add: RA3_def RA2_wait_cond RA2_II_Rac)

lemmas RA1_RA3_commute' = RA1_RA3_commute[simplified comp_apply]
lemmas RA2_RA3_commute' = RA2_RA3_commute[simplified comp_apply]

(* The three components of RA pairwise commute; cite this bundle when a
   proof only reassociates them. *)
lemmas RA_comms = RA1_RA2_commute' RA1_RA3_commute' RA2_RA3_commute'

(* Paper Lemma 19 *)
lemma RA3_wait_false_absorb: "RA3 P = (RA3 \<circ> rad_wait_false) P"
  apply (simp add: RA3_def rad_wait_false_def expr_if_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def)
  apply clarify
  subgoal for x z
    by (cases "astate.s\<^sub>v (des_vars.more x)";
        cases "des_vars.more x"; cases x;
        simp add: lens_defs rad_wait_def astate.s_def
          des_vars.more\<^sub>L_def)
  done

subsection \<open>RA\<close>

(* Paper Definition 32. *)
definition RA ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA \<equiv> RA1 \<circ> RA2 \<circ> RA3"

lemma RA_idem: "RA (RA P) = RA P"
  by (simp add: RA_def RA_comms RA1_idem RA2_idem RA3_idem)

lemma RA_Idempotent [closure]: "Idempotent RA"
  by (simp add: Idempotent_def RA_idem)

lemma RA_healthy [closure]: "RA P is RA"
  by (simp add: Healthy_def' RA_idem)

lemma RA_mono: "P \<sqsubseteq> Q \<Longrightarrow> RA P \<sqsubseteq> RA Q"
  by (simp add: RA_def RA1_mono RA2_mono RA3_mono)

lemma RA_Monotonic [closure]: "Monotonic RA"
  unfolding RA_def
  by (intro Monotonic_comp RA1_Monotonic RA2_Monotonic RA3_Monotonic)

lemma RA_is_RA2:
  assumes "P is RA"
  shows "P is RA2"
proof -
  have h: "RA1 (RA2 (RA3 P)) = P"
    using assms by (simp add: Healthy_def' RA_def)
  have "RA2 (RA1 (RA3 P)) = RA1 (RA2 (RA3 P))"
    by (rule RA1_RA2_commute'[symmetric])
  also have "... = P" by (rule h)
  finally have "RA2 (RA1 (RA3 P)) = P" .
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[where F = RA2, OF RA2_idem])
qed

lemma RA_is_RA3:
  assumes "P is RA"
  shows "P is RA3"
proof -
  have h: "RA1 (RA2 (RA3 P)) = P"
    using assms by (simp add: Healthy_def' RA_def)
  have "RA3 (RA1 (RA2 P)) = RA1 (RA3 (RA2 P))"
    by (simp only: RA1_RA3_commute'[symmetric])
  also have "... = RA1 (RA2 (RA3 P))"
    by (simp only: RA2_RA3_commute'[symmetric])
  also have "... = P" by (rule h)
  finally have "RA3 (RA1 (RA2 P)) = P" .
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[where F = RA3, OF RA3_idem])
qed

lemma RA_as_RA1_RA3_RA2: "RA P = RA1 (RA3 (RA2 P))"
  by (simp add: RA_def RA2_RA3_commute'[symmetric])

lemma RA_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "RA P is PBMH_ades"
  unfolding RA_def comp_apply
  by (intro RA1_PBMH_ades_closure RA2_PBMH_ades_closure
      RA3_PBMH_ades_closure assms)

lemma PBMH_ades_RA_absorb:
  "(PBMH_ades \<circ> RA \<circ> PBMH_ades) P = (RA \<circ> PBMH_ades) P"
  using RA_PBMH_ades_closure[of "PBMH_ades P"]
  by (simp add: Healthy_def' PBMH_ades_idem)

lemma RA_conj: "RA (P \<and> Q) = (RA P \<and> RA Q)"
  by (simp add: RA_def RA1_conj RA2_conj RA3_conj)

lemma RA_disj: "RA (P \<or> Q) = (RA P \<or> RA Q)"
  by (simp add: RA_def RA1_disj RA2_disj RA3_disj)

(* The components of RA commute, so RA may be recomposed in any order. *)
lemma RA_def': "RA P = RA3 (RA2 (RA1 P))"
  by (simp add: RA_def RA_comms)

lemma RA_RA2_RA1_absorb: "RA (RA2 (RA1 P)) = RA P"
  by (simp add: RA_def RA_comms RA1_idem RA2_idem)

lemma RA_cong_ac_non_empty:
  assumes "(ac_non_empty \<and> P) = (ac_non_empty \<and> Q)"
  shows "RA P = RA Q"
  using arg_cong[where f=RA1, OF assms]
  by (simp only: RA1_ac_non_empty_absorb RA_def')

lemma RA_ac_non_empty_absorb: "(ac_non_empty \<and> RA P) = RA P"
  by (simp add: RA_def comp_apply RA1_def ac_non_empty_def
      fun_eq_iff Let_def; pred_auto)

lemma RA_A1: "(RA \<circ> A) P = (RA \<circ> A1) P"
  by (simp add: RA_def A_def RA_comms RA1_A0_absorb)

(* Paper Theorem 67 *)
theorem RA_A:
  assumes "P is \<^bold>H"
  shows "(RA \<circ> A) P = (RA \<circ> PBMH_ades) P"
  by (simp add: RA_A1[simplified comp_apply]
      A1_eq_PBMH_ades[OF assms])

lemmas RA_A' = RA_A[simplified comp_apply]

lemma RA_A_absorb:
  assumes "P is PBMH_ades" "P is \<^bold>H"
  shows "(RA \<circ> A) P = RA P"
  by (simp only: comp_apply RA_A'[OF assms(2)] Healthy_if[OF assms(1)])

subsection \<open>CSPA1\<close>

(* Paper definition 33. *)
definition CSPA1 :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "CSPA1 P \<equiv> (P \<or> RA1 (\<not> ok\<^sup><))"

lemma CSPA1_obs:
  "CSPA1 P (ades_obs ok0 s0 ok' X) =
    (P (ades_obs ok0 s0 ok' X) \<or>
      (\<not> ok0 \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}))"
  by (simp add: CSPA1_def RA1_not_ok_eval; pred_auto)

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

lemma CSPA1_RA2_commute: "CSPA1 (RA2 P) = RA2 (CSPA1 P)"
  by (rule ades_obs_ext;
      simp add: CSPA1_obs RA2_obs' rad_normalise_choices_nonempty
        rad_zero_trace_extensions)

lemma CSPA1_RA3_commute: "CSPA1 (RA3 P) = RA3 (CSPA1 P)"
  by (rule ades_obs_ext;
      simp add: CSPA1_obs RA3_eval II_Rac_eval rad_trace_extensions_def;
      blast)

lemma RA_CSPA1: "(RA \<circ> CSPA1) P = (RA \<circ> H1) P"
  by (simp add: RA_def RA_comms RA1_CSPA1[simplified comp_apply])

subsection \<open>CSPA2\<close>

(* Paper Definition 34. *)
definition CSPA2 :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
where [pred]: "CSPA2 P \<equiv> H2 P"

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
  by (simp only: CSPA2_def H2_split PBMH_ades_disj PBMH_ades_conj_ok
      PBMH_ades_ok_false PBMH_ades_ok_true assms)

lemma rad_wait_false_H1_CSPA2_commute:
  "(rad_wait_false \<circ> H1 \<circ> CSPA2) P =
   (H1 \<circ> CSPA2 \<circ> rad_wait_false) P"
  by (simp add: CSPA2_def rad_wait_false_def H1_def H2_split fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemma CSPA2_not_ok:
  "CSPA2 ((\<not> ok\<^sup><) :: ('t::trace, 'e) reactive_angelic_design) = (\<not> ok\<^sup><)"
  by (simp add: CSPA2_def H2_split fun_eq_iff; pred_auto)

lemma CSPA2_RA1_commute: "CSPA2 (RA1 P) = RA1 (CSPA2 P)"
  by (simp add: CSPA2_def H2_split RA1_def fun_eq_iff Let_def; pred_auto; blast)

lemma CSPA2_RA2_commute: "CSPA2 (RA2 P) = RA2 (CSPA2 P)"
  by (rule ades_obs_ext; simp add: CSPA2_def H2_obs RA2_obs')

lemma CSPA2_RA3_commute: "CSPA2 (RA3 P) = RA3 (CSPA2 P)"
  by (simp add: CSPA2_def H2_split RA3_def II_Rac_def RA1_def expr_if_def
      fun_eq_iff Let_def; pred_auto; blast)

lemma CSPA2_CSPA1_commute: "CSPA2 (CSPA1 P) = CSPA1 (CSPA2 P)"
  by (simp only: CSPA1_def CSPA2_def H2_disj
      CSPA2_RA1_commute[unfolded CSPA2_def] CSPA2_not_ok[unfolded CSPA2_def])

end
