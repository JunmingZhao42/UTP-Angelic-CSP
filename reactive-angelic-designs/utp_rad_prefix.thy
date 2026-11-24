section \<open>Reactive Angelic Design Prefixing and External Choice\<close>

theory utp_rad_prefix
  imports utp_rad_ops
begin

subsection \<open>Prefixing\<close>

(* \<exists> y \<in> ac' \<bullet> (y.tr = s.tr \<and> a \<notin> y.ref) \<triangleleft> y.wait \<triangleright> y.tr = s.tr @ [a] *)
definition prefix_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design" where
[pred]: "prefix_post a = (\<in>\<^sub>a\<^sub>c y. (\<lambda> (s0, ac1).
  ((\<lambda> z. rad_tr\<^sub>v z =
          rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
        a \<notin> rad_ref\<^sub>v z)
      \<triangleleft> $rad_wait \<triangleright>
      (\<lambda> z. rad_tr\<^sub>v z =
        rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a])) y))"

(* Paper Definition 43 / Thesis Definition 124. *)
definition PrefixSkip_RAD :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design" where
[pred]: "PrefixSkip_RAD a = (RA \<circ> A) (true \<turnstile> prefix_post a)"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma prefix_post_p2ac:
  "prefix_post a = p2ac \<lceil>(\<lambda> (s, y).
    if rad_wait\<^sub>v y
    then rad_tr\<^sub>v y = rad_tr\<^sub>v s \<and>
      a \<notin> rad_ref\<^sub>v y
    else rad_tr\<^sub>v y = rad_tr\<^sub>v s @ [a])\<rceil>\<^sub>D"
  by (simp add: prefix_post_def expr_if_def rad_wait_def
      p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma prefix_post_PBMH [simp]:
  "PBMH_ades (prefix_post a) = prefix_post a"
  by (simp only: prefix_post_p2ac PBMH_ades_p2ac)

lemma rad_wait_false_prefix_post: "((prefix_post a) \<^sub>f) = prefix_post a"
  by (simp add: prefix_post_def ades_singleton_choice_def
      expr_if_def rad_wait_def
      rad_wait_false_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def)

(* The prefix postcondition only relates the traces of the initial
   and final states, so trace normalisation leaves it fixed. *)
lemma RA2_prefix_post: "RA2 (prefix_post a) = prefix_post a"
proof -
  have disj_form:
    "prefix_post a = (\<lambda> (s0, ac').
      \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
        rad_wait\<^sub>v y \<and>
        rad_tr\<^sub>v y =
          rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
        a \<notin> rad_ref\<^sub>v y \<or>
        \<not> rad_wait\<^sub>v y \<and>
        rad_tr\<^sub>v y =
          rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a])"
    by (simp add: prefix_post_def expr_if_def rad_wait_def
        fun_eq_iff; pred_auto)
  have nil: "xs \<le> ys \<Longrightarrow> ys - xs = [] \<Longrightarrow> ys = xs" for xs ys
    using minus_zero_eq by (auto simp add: zero_list_def)
  have snoc: "xs \<le> ys \<Longrightarrow> ys - xs = [a] \<Longrightarrow> ys = xs @ [a]"
      for xs ys
    using diff_add_cancel_left'[of xs ys] by (simp add: plus_list_def)
  show ?thesis
    apply (simp only: disj_form)
    apply (simp add: RA2_def rad_normalise_choices_def
        rad_trace_difference_def rad_zero_trace_def fun_eq_iff Let_def)
    apply pred_auto
    subgoal for t ac w r tb
      by (frule (1) nil,
          rule_tac x="rea_vars_ext True tb r" in bexI; simp)
    subgoal for t ac w r tb
      by (frule (1) snoc,
          rule_tac x="rea_vars_ext False tb r" in bexI; simp)
    subgoal for ac y
      by (cases y) (fastforce simp add: diff_cancel zero_list_def)
    subgoal for t ac y
      by (cases y) (fastforce intro: prefixI
          simp add: plus_list_def[symmetric] add_diff_cancel_left)
    done
qed

lemma prefix_post_unrest_ok [unrest]: "$ok\<^sup>> \<sharp> prefix_post a"
  apply (simp add: unrest_lens prefix_post_def
      ades_singleton_choice_def expr_if_def rad_wait_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma prefix_post_ok_out_subst [usubst]:
  "(prefix_post a)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk> = prefix_post a"
  by (simp add: unrest usubst)

lemma prefix_design_is_H [closure]:
  "(true \<turnstile> prefix_post a) is \<^bold>H"
  by (rule design_is_H1_H2; simp add: unrest)

lemma PrefixSkip_RAD_is_RAD [closure]: "PrefixSkip_RAD a is RAD"
  unfolding PrefixSkip_RAD_def
  apply (rule RAD_design_closure)
   apply (rule prefix_design_is_H)
  by (simp add: rad_wait_false_distrib rad_wait_false_prefix_post)

(* Prefixing with the A absorbed into RA. *)
lemma PrefixSkip_RAD_RA:
  "PrefixSkip_RAD a = RA (true \<turnstile> prefix_post a)"
  unfolding PrefixSkip_RAD_def
  by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)

lemma PrefixSkip_RAD_design:
  "PrefixSkip_RAD a =
   RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         prefix_post a))"
  by (simp only: PrefixSkip_RAD_RA RA_true_design RA2_prefix_post)

lemma PrefixSkip_RAD_is_A2 [closure]: "PrefixSkip_RAD a is A2"
proof -
  have body:
    "(true \<turnstile>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> prefix_post a))
     is A2"
    by (simp only: Healthy_def' A2_true_design A2_wait_cond
        A2_state_choice prefix_post_p2ac A2_p2ac)
  show ?thesis
    by (simp only: PrefixSkip_RAD_design; rule RA1_A2_closure[OF body])
qed

(* Paper Theorem 31 / Thesis Theorem T.5.4.26. *)
theorem PrefixSkip_RAD_angelic_choice:
  assumes "P is RAD"
  shows "PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) (true \<turnstile> (((\<not> (P \<^sub>f)\<^sup>f) \<longrightarrow> (P \<^sub>f)\<^sup>t) \<and> prefix_post a))"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  have "PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> prefix_post a) \<squnion> (RA \<circ> A) ?DP"
    by (simp only: PrefixSkip_RAD_def
        RAD_design_form'[OF assms, symmetric])
  also have "... = (RA \<circ> A) ((true \<turnstile> prefix_post a) \<squnion> ?DP)"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (rule RAD_design_PBMH[OF assms])
     apply (rule prefix_design_is_H)
    by (rule rad_wait_false_design_is_H)
  also have "... = (RA \<circ> A)
      (true \<turnstile> (((\<not> ?F) \<longrightarrow> ?T) \<and> prefix_post a))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed

(* Thesis Section 5.4.8: the compound process a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P
   abbreviates (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) ;;\<^sub>R\<^sub>A\<^sub>D P.  Its
   Theorem T.5.4.29 normal form is future work; RAD closure is proved
   in \<open>utp_rad_seq\<close>. *)
definition Prefix_RAD ::
  "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
   ('e list, 'e) reactive_angelic_design"
  (infixr "\<rightarrow>\<^sub>R\<^sub>A\<^sub>D" 80) where
[pred]: "Prefix_RAD a P = (PrefixSkip_RAD a ;;\<^sub>R\<^sub>A\<^sub>D P)"

subsection \<open>External Choice\<close>

(*  \<exists> y \<in> ac' \<bullet>
    (P \<and> Q)[{y}/ac'] \<triangleleft> y.tr = s.tr \<and> y.wait \<triangleright>
    (P \<or> Q)[{y}/ac'] *)
definition extchoice_post ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design" where
[pred]: "extchoice_post P Q = (\<in>\<^sub>a\<^sub>c y. (\<lambda> (s0, ac1).
  (((\<lambda> z. P (s0, ac1) \<and> Q (s0, ac1))
    \<triangleleft> $rad_tr = \<guillemotleft>rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0))\<guillemotright> \<and>
       $rad_wait \<triangleright>
    (\<lambda> z. P (s0, ac1) \<or> Q (s0, ac1))) y)))"

lemma rad_wait_false_extchoice_post:
  "((extchoice_post P Q) \<^sub>f) = extchoice_post (P \<^sub>f) (Q \<^sub>f)"
  by (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_wait_def
      rad_tr_def SEXP_def rad_wait_false_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def Let_def)

lemma extchoice_post_ok_in_subst:
  "(extchoice_post P Q)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> =
   extchoice_post (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>) (Q\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_wait_def
      rad_tr_def SEXP_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs des_vars.ok_def
      astate.s_def des_vars.more\<^sub>L_def des_more_ok_update_commute
      Let_def; pred_auto)

(* Paper Definition 44 / Thesis Definition 125. *)
definition extchoice_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design" (infixl "\<box>\<^sub>R\<^sub>A\<^sub>D" 68) where
[pred]: "P \<box>\<^sub>R\<^sub>A\<^sub>D Q = (RA \<circ> A)
  (((\<not> (P \<^sub>f)\<^sup>f) \<and> (\<not> (Q \<^sub>f)\<^sup>f)) \<turnstile>
   extchoice_post ((P \<^sub>f)\<^sup>t) ((Q \<^sub>f)\<^sup>t))"

lemma extchoice_post_unrest_ok [unrest]:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "$ok\<^sup>> \<sharp> extchoice_post P Q"
proof -
  have put_P:
      "\<forall> s0 ac1 v. P (s0, ac1\<lparr>des_vars.ok\<^sub>v := v\<rparr>) = P (s0, ac1)"
    using assms(1)
    apply (subst (asm) unrest_lens)
     apply simp
    by (simp add: lens_defs des_vars.ok_def case_prod_beta
        split_paired_All)
  have put_Q:
      "\<forall> s0 ac1 v. Q (s0, ac1\<lparr>des_vars.ok\<^sub>v := v\<rparr>) = Q (s0, ac1)"
    using assms(2)
    apply (subst (asm) unrest_lens)
     apply simp
    by (simp add: lens_defs des_vars.ok_def case_prod_beta
        split_paired_All)
  show ?thesis
    apply (subst unrest_lens)
     apply simp
    apply (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_wait_def
      rad_tr_def SEXP_def Let_def lens_defs
        des_vars.ok_def case_prod_beta)
    using put_P put_Q
    by (simp add: des_more_ok_update_commute)
qed

lemma extchoice_RAD_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Q is RAD"
  unfolding extchoice_RAD_def
  apply (rule RAD_design_closure)
   apply (rule design_is_H1_H2; simp add: unrest)
  by (simp add: rad_wait_false_distrib rad_wait_false_extchoice_post)

lemma extchoice_RAD_mono:
  assumes "P \<sqsubseteq> P'" "Q \<sqsubseteq> Q'"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Q \<sqsubseteq>
         P' \<box>\<^sub>R\<^sub>A\<^sub>D Q'"
  unfolding extchoice_RAD_def comp_apply
  apply (rule RA_mono, rule A_mono)
  using assms
  apply (auto simp add: pred_refine_iff extchoice_post_def ades_singleton_choice_def
      expr_if_def rad_wait_def rad_tr_def rad_wait_false_def design_def
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs comp_def
      astate.s_def des_vars.more\<^sub>L_def des_vars.ok_def
      conj_pred_def disj_pred_def not_pred_def impl_pred_def
      split: prod.splits)
  by (erule bexI[rotated]; auto)+

(* Composition with the Stop postcondition reduces both branches to
   the bare singleton choice: the waiting branch of Stop holds exactly
   on the states admitted by the conditional's guard. *)
lemma extchoice_post_stop:
  "extchoice_post X (RA2 (RA1 stop_post)) = \<in>\<^sub>a\<^sub>c(X)"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_stop_post)
  apply (simp add: extchoice_post_def ades_singleton_choice_def expr_if_def rad_wait_def
      rad_tr_def SEXP_def ades_singleton_choice_def
      RA1_def stop_post_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_wait_def astate.s_def
      des_vars.more\<^sub>L_def)
  by (pred_auto; blast)

(* Paper Theorem 32 / Thesis Theorem T.5.4.30:
   Stop is not a unit of external choice in RAD (without A2). *)
(* RA \<circ> A (\<not> P_f^f \<turnstile> \<exists> y \<in> ac'. P_f^t[{y}/ac'])*)
theorem extchoice_RAD_Stop:
  assumes "P is RAD"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D =
    (RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile>
      (\<lambda> (s0, ac'). \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
          ((P \<^sub>f)\<^sup>t) (s0, des_vars.more_update
              (achoices.ac\<^sub>v_update (\<lambda>_. {y})) ac')))"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  let ?SF = "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f" and ?ST = "(Stop\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>t"
  have pre_push:
      "((\<not> ?F) \<and> (\<not> ?SF))\<lbrakk>True/ok\<^sup><\<rbrakk> =
       (\<not> ?F)\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: subst_pred(3,4) Stop_RAD_wf_ok_false_subst
        pred_ba.compl_bot_eq pred_ba.inf_top_right)
  have post_push:
      "(extchoice_post ?T ?ST)\<lbrakk>True/ok\<^sup><\<rbrakk> =
       (\<in>\<^sub>a\<^sub>c(?T))\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: extchoice_post_ok_in_subst
        ades_singleton_choice_ok_in_subst
        Stop_RAD_wf_ok_true_subst extchoice_post_stop)
  have "(((\<not> ?F) \<and> (\<not> ?SF)) \<turnstile> extchoice_post ?T ?ST) =
        ((\<not> ?F) \<turnstile> \<in>\<^sub>a\<^sub>c(?T))"
    using arg_cong2[where f=design, OF pre_push post_push]
    by (simp only: design_subst_ok)
  then show ?thesis
    by (simp only: extchoice_RAD_def ades_singleton_choice_def)
qed

(* Paper Theorem 33 / Thesis Theorem T.5.4.31 *)
theorem extchoice_RAD_Stop_unit:
  assumes "P is RAD" "P is A2"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D = P"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  have not_F_PBMH: "(\<not> (\<not> ?F)) is PBMH_ades"
    by (simp only: pred_ba.double_compl RAD_wf_ok_false_PBMH[OF assms(1)])
  have unrests: "$ok\<^sup>> \<sharp> (\<not> ?F)" "$ok\<^sup>> \<sharp> ?T"
    by (simp_all add: unrest)
  have singleton: "\<in>\<^sub>a\<^sub>c(?T) = (?T \<and> ac_non_empty)"
  proof -
    have "\<in>\<^sub>a\<^sub>c(((A2 P) \<^sub>f)\<^sup>t) =
        ((((A2 P) \<^sub>f)\<^sup>t) \<and> ac_non_empty)"
      by (simp add: A2_def ades_singleton_choice_def ac_non_empty_def
          rad_wait_false_def fun_eq_iff usubst usubst_eval Let_def;
          pred_auto; blast)
    then show ?thesis by (simp only: Healthy_if[OF assms(2)])
  qed
  have "P \<box>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D =
      (RA \<circ> A) ((\<not> ?F) \<turnstile> \<in>\<^sub>a\<^sub>c(?T))"
    using extchoice_RAD_Stop[OF assms(1)]
    by (simp only: ades_singleton_choice_def)
  also have "... = RA ((\<not> ?F) \<turnstile> \<in>\<^sub>a\<^sub>c(?T))"
    by (rule RA_A_absorb_design[OF not_F_PBMH _ unrests(1)])
      (simp_all add: Healthy_def' unrest unrests)
  also have "... = RA ((\<not> ?F) \<turnstile> ?T)"
    apply (rule RA_cong_ac_non_empty)
    by (simp only: singleton; pred_auto)
  also have "... = P"
    by (rule RAD_RA_design_form[OF assms(1), symmetric])
  finally show ?thesis .
qed

end
