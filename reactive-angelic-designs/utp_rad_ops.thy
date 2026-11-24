section \<open>Reactive Angelic Design Operators\<close>

theory utp_rad_ops
  imports utp_rad_choice
begin

subsection \<open>Stop\<close>

(* Paper Definition 41: \<in>\<^sub>a\<^sub>c y \<bullet> y.tr = s.tr \<and> y.wait *)
definition stop_post :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "stop_post = (\<in>\<^sub>a\<^sub>c y. (\<lambda> (s0, ac1).
  rad_tr\<^sub>v y = rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
  rad_wait\<^sub>v y))"

(* Paper Definition 41. *)
definition Stop_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Stop\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Stop_RAD = (RA \<circ> A) (true \<turnstile> stop_post)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma stop_post_p2ac:
  "stop_post = p2ac \<lceil>(\<lambda> (s, y).
    rad_tr\<^sub>v y = rad_tr\<^sub>v s \<and> rad_wait\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: stop_post_def ades_singleton_choice_def p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma stop_post_PBMH [simp]: "PBMH_ades stop_post = stop_post"
  by (simp only: stop_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_stop_post: "(stop_post \<^sub>f) = stop_post"
  by (simp add: stop_post_def ades_singleton_choice_def rad_wait_false_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def)

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
  apply (simp add: RA2_def stop_post_def ades_singleton_choice_def rad_normalise_choices_def
      rad_trace_difference_def rad_zero_trace_def fun_eq_iff Let_def;
      pred_auto)
  subgoal for t ac w r ta
    by (frule (1) minus_zero_eq[rotated],
        rule_tac x="rea_vars_ext True ta r" in bexI; simp)
  subgoal for ac y
    apply (cases y)
    by force
  done

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
lemma stop_design_wf_norm: "((stop_post \<and> ok\<^sup>>) \<^sub>f) = (stop_post \<and> ok\<^sup>>)"
  by (simp only: rad_wait_false_conj rad_wait_false_stop_post
      rad_wait_false_ok_out)

lemma stop_design_ok_false: "(stop_post \<and> ok\<^sup>>)\<^sup>f = false"
  by (simp add: usubst usubst_eval; pred_auto)

lemma stop_design_ok_true: "(stop_post \<and> ok\<^sup>>)\<^sup>t = stop_post"
  by (simp add: usubst usubst_eval; pred_auto)

(* Stop can only fail to stabilise when it has not started. *)
lemma Stop_RAD_wf_ok_false: "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f = RA2 (RA1 (\<not> ok\<^sup><))"
proof -
  have design_norm:
      "((\<not> ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>f) \<turnstile>
        ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>t) =
       (true \<turnstile> stop_post)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        stop_design_ok_true pred_ba.compl_bot_eq)
  have disj_norm: "((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>f) = (\<not> ok\<^sup><)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        pred_ba.sup_bot_right)
  have "((rad_wait_false \<circ> RA \<circ> A) (true \<turnstile> stop_post))\<^sup>f =
      (RA2 \<circ> RA1 \<circ> PBMH_ades)
        ((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>f)"
    using RA_design_wf_ok_false[of "stop_post \<and> ok\<^sup>>"]
    by (simp only: design_norm)
  then show ?thesis
    by (simp only: Stop_RAD_def comp_apply disj_norm
        PBMH_ades_not_ok_expr)
qed

lemma Stop_RAD_wf_ok_false_subst:
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
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
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>t = RA2 (RA1 ((\<not> ok\<^sup><) \<or> stop_post))"
proof -
  have design_norm:
      "((\<not> ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>f) \<turnstile>
        ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>t) =
       (true \<turnstile> stop_post)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        stop_design_ok_true pred_ba.compl_bot_eq)
  have disj_norm:
      "((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>f \<or>
        ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>t) =
       ((\<not> ok\<^sup><) \<or> stop_post)"
    by (simp only: stop_design_wf_norm stop_design_ok_false
        stop_design_ok_true pred_ba.sup_bot_left)
  have PBMH_norm:
      "PBMH_ades ((\<not> ok\<^sup><) \<or> stop_post) = ((\<not> ok\<^sup><) \<or> stop_post)"
    by (simp add: PBMH_ades_disj)
  have "((rad_wait_false \<circ> RA \<circ> A) (true \<turnstile> stop_post))\<^sup>t =
      (RA2 \<circ> RA1 \<circ> PBMH_ades)
        ((\<not> ok\<^sup><) \<or> ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>f \<or>
         ((stop_post \<and> ok\<^sup>>) \<^sub>f)\<^sup>t)"
    using RA_design_wf_ok_true[of "stop_post \<and> ok\<^sup>>"]
    by (simp only: design_norm)
  then show ?thesis
    by (simp only: Stop_RAD_def comp_apply disj_norm PBMH_norm)
qed

lemma Stop_RAD_wf_ok_true_subst:
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>t\<lbrakk>True/ok\<^sup><\<rbrakk> = RA2 (RA1 stop_post)"
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

lemma Stop_RAD_is_A2 [closure]: "Stop\<^sub>R\<^sub>A\<^sub>D is A2"
proof -
  have body:
    "(true \<turnstile>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> stop_post))
     is A2"
    by (simp only: Healthy_def' A2_true_design A2_wait_cond
        A2_state_choice stop_post_p2ac A2_p2ac)
  show ?thesis
    by (simp only: Stop_RAD_design; rule RA1_A2_closure[OF body])
qed

(* Paper Theorem 28. *)
theorem Stop_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile> (((\<not> (P \<^sub>f)\<^sup>f) \<longrightarrow> (P \<^sub>f)\<^sup>t) \<and> stop_post))"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
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
  \<not> rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0))))"

(* Paper Definition 42. *)
definition Skip_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Skip\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Skip_RAD = (RA \<circ> A) (true \<turnstile> skip_post)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma skip_post_p2ac:
  "skip_post = p2ac \<lceil>(\<lambda> (s, y).
    \<not> rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s)\<rceil>\<^sub>D"
  by (simp add: skip_post_def ades_singleton_choice_def p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma skip_post_PBMH [simp]: "PBMH_ades skip_post = skip_post"
  by (simp only: skip_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_skip_post: "(skip_post \<^sub>f) = skip_post"
  by (simp add: skip_post_def ades_singleton_choice_def rad_wait_false_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA1_skip_post: "RA1 skip_post = skip_post"
  apply (simp add: RA1_def skip_post_def ades_singleton_choice_def
      rad_trace_extensions_def fun_eq_iff Let_def)
  apply (auto intro: order_refl)
  subgoal for a b y
    apply (drule arg_cong[where f="\<lambda>S. y \<in> S"])
    by simp
  done

lemma RA2_skip_post: "RA2 skip_post = skip_post"
  apply (simp add: RA2_def skip_post_def ades_singleton_choice_def rad_normalise_choices_def
      rad_trace_difference_def rad_zero_trace_def fun_eq_iff Let_def;
      pred_auto)
  subgoal for t ac w r ta
    by (frule (1) minus_zero_eq[rotated],
        rule_tac x="rea_vars_ext False ta r" in bexI; simp)
  subgoal for ac y
    apply (cases y)
    by force
  done

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

lemma Skip_RAD_is_A2 [closure]: "Skip\<^sub>R\<^sub>A\<^sub>D is A2"
proof -
  have body:
    "(true \<turnstile>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> skip_post))
     is A2"
    by (simp only: Healthy_def' A2_true_design A2_wait_cond
        A2_state_choice skip_post_p2ac A2_p2ac)
  show ?thesis
    by (simp only: Skip_RAD_design; rule RA1_A2_closure[OF body])
qed

(* Paper Theorem 29. *)
theorem Skip_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Skip\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile> (skip_post \<and> ((\<not> (P \<^sub>f)\<^sup>f) \<longrightarrow> (P \<^sub>f)\<^sup>t)))"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
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
  is exactly \<open>;;\<^sub>A\<^sub>D\<close> from the theory of angelic designs.  The notation
  remains here because the compound prefix operator below uses it.  Its
  laws, CSP correspondence, paper Theorem 30 normal form, and RAD closure
  law are proved in \<open>utp_rad_seq\<close>.
\<close>

abbreviation seq_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design" (infixl ";;\<^sub>R\<^sub>A\<^sub>D" 75)
where "P ;;\<^sub>R\<^sub>A\<^sub>D Q \<equiv> P ;;\<^sub>A\<^sub>D Q"

end
