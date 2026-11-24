section \<open>Reactive Angelic Design Prefixing Laws\<close>

theory utp_rad_prefix_laws
  imports utp_rad_seq
begin

subsection \<open>Prefixing laws\<close>

(* An RA1-guarded left operand vanishes on the empty continuation. *)
lemma RA1_aseq_false: "(RA1 P ;;\<^sub>A\<^sub>R false) = false"
  by (simp add: RA1_def aseq_ades_def fun_eq_iff Let_def; pred_auto)

(* A nonempty choice set is subsumed by an inhabited choice over it. *)
lemma bex_nonempty_absorb:
  "((\<exists> y \<in> X. P y) \<and> \<not> X = {}) = (\<exists> y \<in> X. P y)"
  by auto

lemma trace_le_append [simp]: "(xs :: 'e list) \<le> xs @ ys"
  by (simp add: plus_list_def[symmetric])

(* General prefixing: the handover state follows the event, while the
   continuation also includes observations that still offer it. *)
lemma RA1_prefix_post:
  "RA1 (prefix_post a) = prefix_post a"
  by (simp add: RA1_def prefix_post_def ades_singleton_choice_def
      expr_if_def rad_wait_def rad_trace_extensions_def
      fun_eq_iff Let_def bex_nonempty_absorb;
      auto intro: trace_le_append)

(* The state reached after performing the prefix event. *)
definition prefix_handover ::
  "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
   ('e list, 'e) reactive_angelic_design" where
[pred]: "prefix_handover a P = (\<lambda> (s0, ac').
  \<exists> y. \<not> rad_wait\<^sub>v y \<and>
    rad_tr\<^sub>v y = rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<and>
    P (des_vars.more_update (astate.s\<^sub>v_update (\<lambda>_. y)) s0, ac'))"

(* The prefix is either still offering the event or has handed over. *)
definition prefix_continuation ::
  "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
   ('e list, 'e) reactive_angelic_design" where
[pred]: "prefix_continuation a P = (\<lambda> (s0, ac').
  \<exists> y. if rad_wait\<^sub>v y
    then y \<in> achoices.ac\<^sub>v (des_vars.more ac') \<and>
      rad_tr\<^sub>v y = rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
      a \<notin> rad_ref\<^sub>v y
    else rad_tr\<^sub>v y = rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<and>
      P (des_vars.more_update (astate.s\<^sub>v_update (\<lambda>_. y)) s0, ac'))"

lemma prefix_handover_aseq:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    ((\<not> rad_wait_lens\<^sup><) \<and> P)) = prefix_handover a P"
  by (simp only: RA1_prefix_post;
      simp add: aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def prefix_handover_def fun_eq_iff
      lens_defs rad_wait_def astate.s_def des_vars.more\<^sub>L_def
      SEXP_def subst_app_def subst_ext_def conj_pred_def not_pred_def;
      auto simp add: if_bool_eq_disj split: prod.splits)

lemma prefix_continuation_aseq:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)) =
   prefix_continuation a P"
  by (simp only: RA1_prefix_post;
      simp add: aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def prefix_continuation_def
      ades_state_choice_def fun_eq_iff lens_defs rad_wait_def
      astate.s_def des_vars.more\<^sub>L_def
      SEXP_def subst_app_def subst_ext_def;
      auto simp add: if_bool_eq_disj split: prod.splits)

lemma prefix_design_failure_absorb:
  "((\<not> prefix_handover a F) \<turnstile> prefix_continuation a (F \<or> T)) =
   ((\<not> prefix_handover a F) \<turnstile> prefix_continuation a T)"
  by (simp add: prefix_handover_def prefix_continuation_def
      design_def fun_eq_iff conj_pred_def disj_pred_def not_pred_def impl_pred_def
      SEXP_def subst_app_def subst_ext_def lens_defs;
      auto simp add: if_bool_eq_disj split: prod.splits)

lemma Prefix_RA_design:
  assumes "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(PrefixSkip_RAD a ;;\<^sub>A\<^sub>D RA (R \<turnstile> S)) =
    RA ((\<not> prefix_handover a (RA2 (RA1 (\<not> R)))) \<turnstile>
      prefix_continuation a (RA2 (RA1 S)))"
proof -
  have components:
      "$ok\<^sup>> \<sharp> (true :: ('e list, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    by (simp_all add: unrest assms)
  have failure_PBMH:
      "(\<not> (true :: ('e list, 'e) reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have prefix_PBMH: "prefix_post a is PBMH_ades"
    by (simp only: Healthy_def' prefix_post_PBMH)
  show ?thesis
    using RA_design_seq[where P=true and Q="prefix_post a" and R=R and S=S,
      OF components failure_PBMH prefix_PBMH]
    by (simp only: PrefixSkip_RAD_RA pred_ba.compl_top_eq RA1_false
        aseq_ades_false_left pred_ba.compl_bot_eq pred_ba.inf_top_left
        impl_neg_disj RA1_disj RA2_disj
        prefix_handover_aseq prefix_continuation_aseq prefix_design_failure_absorb)
qed

(* Thesis Theorem T.5.4.29. *)
lemma Prefix_RAD_design:
  assumes "P is RAD"
  shows "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P) =
    (RA \<circ> A)
      ((\<not> prefix_handover a ((RA2 \<circ> RA1) ((P \<^sub>f)\<^sup>f))) \<turnstile>
       prefix_continuation a ((RA2 \<circ> RA1) ((P \<^sub>f)\<^sup>t)))"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  let ?F' = "?F\<lbrakk>True/ok\<^sup><\<rbrakk>" and ?T' = "?T\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?D = "(\<not> prefix_handover a (RA2 (RA1 ?F))) \<turnstile>
    prefix_continuation a (RA2 (RA1 ?T))"
  let ?D' = "(\<not> prefix_handover a (RA2 (RA1 ?F'))) \<turnstile>
    prefix_continuation a (RA2 (RA1 ?T'))"
  have P_form: "P = RA ((\<not> ?F') \<turnstile> ?T')"
    using RAD_RA_design_form[OF assms]
    by (simp only: design_subst_ok[of "\<not> ?F" ?T, symmetric])
      (simp add: usubst)
  have components: "$ok\<^sup>< \<sharp> (\<not> ?F')" "$ok\<^sup>< \<sharp> ?T'"
    by (simp_all add: unrest)
  have desubst: "?D' = ?D"
    apply (rule design_ok_in_cong)
    by (simp_all add: usubst prefix_handover_aseq[symmetric]
        prefix_continuation_aseq[symmetric] RA1_ok_in_subst RA2_ok_in_subst
        aseq_ades_ok_in_subst rad_wait_cond_ok_in_subst)
  have failure_PBMH: "prefix_handover a (RA2 (RA1 ?F)) is PBMH_ades"
    unfolding prefix_handover_aseq[symmetric] rad_wait_cond_false[symmetric]
    by (intro aseq_ades_PBMH_ades_closure RA1_PBMH_ades_closure
        rad_wait_cond_PBMH_ades_closure false_PBMH_ades
        RA2_PBMH_ades_closure RAD_wf_ok_false_PBMH[OF assms];
        simp add: Healthy_def')
  have post_PBMH: "prefix_continuation a (RA2 (RA1 ?T)) is PBMH_ades"
    unfolding prefix_continuation_aseq[symmetric]
    by (intro aseq_ades_PBMH_ades_closure RA1_PBMH_ades_closure
        rad_wait_cond_PBMH_ades_closure ades_state_choice_is_PBMH_ades
        RA2_PBMH_ades_closure RAD_wf_ok_true_PBMH[OF assms];
        simp add: Healthy_def')
  have prefix_unrest: "$ok\<^sup>> \<sharp> RA1 (prefix_post a)"
    by unrest
  have continuation_unrest: "$ok\<^sup>> \<sharp>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (RA1 ?T))"
    by unrest
  have unrests:
      "$ok\<^sup>> \<sharp> (\<not> prefix_handover a (RA2 (RA1 ?F)))"
      "$ok\<^sup>> \<sharp> prefix_continuation a (RA2 (RA1 ?T))"
    apply (simp only: prefix_handover_aseq[symmetric]; simp add: unrest)
    using aseq_ades_unrest_ok_out[OF prefix_unrest continuation_unrest]
    by (simp only: prefix_continuation_aseq)
  have absorb: "(RA \<circ> A) ?D = RA ?D"
    apply (rule RA_A_absorb_design)
       apply (simp only: pred_ba.double_compl failure_PBMH)
      apply (rule post_PBMH)
     apply (rule unrests(1))
    by (rule unrests(2))
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P) =
      (PrefixSkip_RAD a ;;\<^sub>A\<^sub>D RA ((\<not> ?F') \<turnstile> ?T'))"
    by (simp only: Prefix_RAD_def P_form[symmetric])
  also have "... = RA ?D'"
    by (simp only: Prefix_RA_design[OF components] pred_ba.double_compl)
  also have "... = (RA \<circ> A) ?D"
    by (simp only: desubst absorb)
  finally show ?thesis
    by (simp only: comp_apply)
qed

(* The continuation of prefixing into Skip leaves the prefix
   postcondition unchanged: Skip is a right unit of the primitive. *)
lemma prefix_continuation_skip:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 skip_post))) = prefix_post a"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_skip_post)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def skip_post_def ades_singleton_choice_def
      ades_state_choice_def expr_if_def rad_trace_extensions_def
      fun_eq_iff Let_def lens_defs rad_wait_def astate.s_def
      des_vars.more\<^sub>L_def bex_nonempty_absorb)
  apply clarify
  subgoal for x0 y0
    apply (rule iffI)
     apply fastforce
    apply (elim bexE conjE)
    subgoal for y
      by (cases "rad_wait\<^sub>v y";
          rule_tac x=y in bexI; fastforce)
    done
  done

(* Thesis Theorem T.5.4.29 instantiated to Skip: the compound
   a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D coincides with the
   primitive of Definition 43. *)
lemma Prefix_Skip_RAD_RA:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) = RA (true \<turnstile> prefix_post a)"
proof -
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> skip_post"
    by (simp_all add: unrest)
  have not_true_PBMH:
      "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have prefix_PBMH: "prefix_post a is PBMH_ades"
    by (simp add: Healthy_def')
  have skip_absorb:
      "(RA \<circ> A) (true \<turnstile> skip_post) = RA (true \<turnstile> skip_post)"
    by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) =
      (RA (true \<turnstile> prefix_post a) ;;\<^sub>A\<^sub>D
       RA (true \<turnstile> skip_post))"
    by (simp only: Prefix_RAD_def PrefixSkip_RAD_RA Skip_RAD_def
        skip_absorb)
  also have "... = RA (true \<turnstile> prefix_post a)"
    using RA_design_seq[
      where P=true and Q="prefix_post a" and R=true and S=skip_post,
      OF component_unrests not_true_PBMH prefix_PBMH]
    by (simp only: pred_ba.compl_top_eq pred_ba.compl_bot_eq
        RA1_false RA2_false aseq_ades_false_left
        pred_ba.inf_bot_right RA1_aseq_false pred_ba.inf_idem
        pred_impl_laws prefix_continuation_skip)
  finally show ?thesis .
qed


subsection \<open>Prefix observations and continuations\<close>

(* The failure observation of a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D
   Chaos\<^sub>R\<^sub>A\<^sub>D: the event has occurred. *)
definition prefix_diverge_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design"
where
[pred]: "prefix_diverge_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<le>
    rad_tr\<^sub>v y)"

(* The event is offered and has not yet occurred. *)
definition prefix_offer_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design"
where
[pred]: "prefix_offer_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_wait\<^sub>v y \<and>
    rad_tr\<^sub>v y =
      rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
    a \<notin> rad_ref\<^sub>v y)"

lemma prefix_diverge_post_p2ac:
  "prefix_diverge_post a = p2ac \<lceil>(\<lambda> (s, y).
    rad_tr\<^sub>v s @ [a] \<le> rad_tr\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: prefix_diverge_post_def p2ac_def fun_eq_iff
      subst_app_def subst_ext_def SEXP_def lens_defs
      des_vars.more\<^sub>L_def; pred_auto; blast)

lemma prefix_offer_post_p2ac:
  "prefix_offer_post a = p2ac \<lceil>(\<lambda> (s, y).
    rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s \<and>
    a \<notin> rad_ref\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: prefix_offer_post_def p2ac_def fun_eq_iff
      subst_app_def subst_ext_def SEXP_def lens_defs
      des_vars.more\<^sub>L_def; pred_auto; blast)

lemma prefix_diverge_post_PBMH [simp]:
  "PBMH_ades (prefix_diverge_post a) = prefix_diverge_post a"
  by (simp only: prefix_diverge_post_p2ac PBMH_ades_p2ac)

lemma prefix_offer_post_PBMH [simp]:
  "PBMH_ades (prefix_offer_post a) = prefix_offer_post a"
  by (simp only: prefix_offer_post_p2ac PBMH_ades_p2ac)

lemma prefix_diverge_post_unrest_ok [unrest]:
  "$ok\<^sup>> \<sharp> prefix_diverge_post a"
  apply (simp add: unrest_lens prefix_diverge_post_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma prefix_offer_post_unrest_ok [unrest]:
  "$ok\<^sup>> \<sharp> prefix_offer_post a"
  apply (simp add: unrest_lens prefix_offer_post_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

(* Handing the prefix over to an arbitrary continuation records
   exactly that the event has occurred. *)
lemma prefix_handover_diverge:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 true))) =
   prefix_diverge_post a"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def
      rad_wait_def
      prefix_diverge_post_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_wait_def astate.s_def
      des_vars.more\<^sub>L_def true_pred_def conj_pred_def
      not_pred_def SEXP_def subst_ext_def
      subst_app_def ex_in_conv[symmetric])
  apply clarify
  subgoal for x0 y0
    apply (rule iffI)
     apply (fastforce intro: order_trans)
    apply (elim bexE)
    subgoal for y
      apply (rule conjI)
       apply (rule_tac x="rea_vars_ext False
           (rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a]) {}" in bexI; fastforce)
      by (rule_tac x="rea_vars_ext False
           (rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a]) {}" in exI; fastforce)
    done
  done

(* The continuation of the prefix into Chaos: either the event is
   still offered, or it has occurred and anything may follow. *)
lemma prefix_continuation_chaos:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 true))) =
   (prefix_offer_post a \<or> prefix_diverge_post a)"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      ades_singleton_choice_def prefix_offer_post_def prefix_diverge_post_def
      ades_state_choice_def expr_if_def rad_trace_extensions_def
      fun_eq_iff Let_def lens_defs rad_wait_def astate.s_def
      des_vars.more\<^sub>L_def true_pred_def disj_pred_def
      conj_pred_def not_pred_def SEXP_def
      subst_ext_def subst_app_def ex_in_conv[symmetric])
  apply clarify
  subgoal for x0 y0
    apply (rule iffI)
     apply (fastforce intro: order_trans)
    apply (elim disjE bexE)
     subgoal for y
       apply (rule conjI)
        apply (rule_tac x=y in bexI; fastforce)
       by (rule_tac x=y in exI; fastforce)
    subgoal for y
      apply (rule conjI)
       apply (rule_tac x="rea_vars_ext False
           (rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a]) {}" in bexI; fastforce)
      by (rule_tac x="rea_vars_ext False
           (rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a]) {}" in exI; fastforce)
    done
  done

(* Trace normalisation fixes the failure observation of the prefixed
   Chaos: both sides state that the event has occurred. *)
lemma RA2_prefix_diverge_post:
  "RA2 (prefix_diverge_post a) = prefix_diverge_post a"
proof -
  have append_le:
    "xs \<le> ys \<Longrightarrow> zs \<le> ys - xs \<Longrightarrow>
     xs @ zs \<le> ys" for xs ys zs :: "'e list"
  proof -
    assume xy: "xs \<le> ys" and zd: "zs \<le> ys - xs"
    have "xs + zs \<le> xs + (ys - xs)"
      by (rule add_left_mono[OF zd])
    also have "... = ys"
      by (rule diff_add_cancel_left'[OF xy])
    finally show "xs @ zs \<le> ys"
      by (simp only: plus_list_def)
  qed
  have diff_le:
    "xs @ zs \<le> ys \<Longrightarrow> zs \<le> ys - xs"
    for xs ys zs :: "'e list"
  proof -
    assume xyz: "xs @ zs \<le> ys"
    have xy: "xs \<le> ys"
      by (rule list_append_prefixD[OF xyz])
    have "xs + zs \<le> xs + (ys - xs)"
      using xyz diff_add_cancel_left'[OF xy]
      by (simp only: plus_list_def)
    then show "zs \<le> ys - xs"
      by (rule add_le_imp_le_left)
  qed
  show ?thesis
    apply (simp add: RA2_def prefix_diverge_post_def
        rad_normalise_choices_def rad_trace_difference_def
        rad_zero_trace_def fun_eq_iff Let_def)
    apply pred_auto
    subgoal for t ac w r tb
      by (frule (1) append_le,
          rule_tac x="rea_vars_ext w tb r" in bexI; simp)
    subgoal for t ac y
      apply (cases y)
      apply simp
      using diff_le by blast
    done
qed

lemma RA2_prefix_offer_post:
  "RA2 (prefix_offer_post a) = prefix_offer_post a"
proof -
  \<comment> \<open>List instance of \<open>minus_zero_eq\<close>, shaped for the trace
      difference the normalisation exposes.\<close>
  have nil: "xs \<le> ys \<Longrightarrow> ys - xs = [] \<Longrightarrow> ys = xs"
      for xs ys :: "'e list"
    using minus_zero_eq by (auto simp add: zero_list_def)
  show ?thesis
  apply (simp add: RA2_def prefix_offer_post_def
      rad_normalise_choices_def rad_trace_difference_def
      rad_zero_trace_def fun_eq_iff Let_def)
  apply pred_auto
  subgoal for t ac w r ta
    by (drule sym, frule (1) nil,
        rule_tac x="rea_vars_ext True ta r" in bexI; simp)
  subgoal for ac y
    apply (cases y)
    apply (simp add: zero_list_def)
    by force
  done
qed

(* Handing the prefix over to any non-waiting continuation is always
   possible: performing the event reaches a non-waiting state. *)
lemma prefix_handover_nonwait:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>R (\<not> rad_wait_lens\<^sup><)) = true"
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def
      rad_wait_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_wait_def astate.s_def
      des_vars.more\<^sub>L_def true_pred_def conj_pred_def
      not_pred_def SEXP_def subst_ext_def
      subst_app_def ex_in_conv[symmetric])
  apply (rule allI, rule conjI)
  subgoal for aa
    by (rule_tac x="(rea_vars_ext (False) (rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more aa)) @ [a]) ({}))" in bexI;
        simp add: trace_le_append)
  subgoal for aa
    by (rule_tac x="(rea_vars_ext (False) (rad_tr\<^sub>v (astate.s\<^sub>v (des_vars.more aa)) @ [a]) ({}))" in exI;
        simp add: trace_le_append)
  done

end
