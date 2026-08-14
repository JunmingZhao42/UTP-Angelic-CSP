section \<open>Angelic Process Examples\<close>

text \<open>
  The worked examples of the paper's Section 7, collected apart from
  the healthiness, correspondence, and operator theories.
\<close>

theory utp_ap_examples
  imports utp_ap_ops
begin

(* Paper Example 22: Theorem 39 applied to Chaos_RAD = RAD true. *)
lemma H1_Chaos_RAD_example:
  "H1 (Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) =
   ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
     (($rad_wait_lens\<^sup><)\<^sub>e \<and> ades_state_choice))"
  by (simp only: Chaos_RAD_RAD H1_RAD_design[simplified comp_apply]
      rad_wait_false_true subst_pred(1) PBMH_ades_true RA2_true
      RA2_RA1_true RA3AP_design_post;
      pred_auto add: rad_trace_extensions_def)

(* Paper Example 23. *)
lemma H1_Skip_RAD_example:
  "H1 (Skip\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) =
   (true \<turnstile> RA3AP skip_post)"
  by (simp only: Skip_RAD_def comp_apply
      H1_RA_A_true_design[where P=skip_post,
        simplified rad_wait_false_skip_post skip_post_ok_out_subst comp_apply]
      skip_post_PBMH RA1_skip_post RA2_skip_post)

(* Paper Example 24 *)
lemma RA1_H1_Chaos_RAD_example:
  "RA1 ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
      (($rad_wait_lens\<^sup><)\<^sub>e \<and> ades_state_choice)) =
   (Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design)"
  by (simp only: H1_Chaos_RAD_example[symmetric] Chaos_RAD_RAD
      RA1_H1_RAD[simplified comp_apply])

(* Paper Example 25: H1 after mapping the bottom AP through RA1. *)
lemma H1_RA1_bottom_AP_example:
  "(H1 \<circ> RA1) (\<^bold>\<bottom>\<^sub>A\<^sub>P ::
      ('t::trace, 'e) reactive_angelic_design) =
   ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
    (($rad_wait_lens\<^sup><)\<^sub>e \<and> ades_state_choice))"
  by (simp only: comp_apply RA1_AP_RAD[simplified comp_apply]
      bottom_RAD_is_Chaos H1_Chaos_RAD_example)

(* Paper Example 26 / Thesis Example 44: the angel avoids the
   divergence of Chaos_AP by resolving the choice in favour of
   deadlock. *)
lemma Stop_Skip_seq_Chaos_AP:
  "(Stop\<^sub>A\<^sub>P \<squnion>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) ;;\<^sub>D\<^sub>A Chaos\<^sub>A\<^sub>P =
   Stop\<^sub>A\<^sub>P"
proof -
  let ?J = "stop_post \<and> skip_post"
  have J_wf: "(?J \<^sub>f) = ?J"
    by (simp only: rad_wait_false_conj rad_wait_false_stop_post
        rad_wait_false_skip_post)
  have J_PBMH: "PBMH_ades ?J = ?J"
    by (rule Healthy_if, rule PBMH_ades_conj_closure;
        simp add: Healthy_def')
  have J_ok: "?J\<lbrakk>True/ok\<^sup>>\<rbrakk> = ?J"
    by (simp add: usubst)
  have choice_AP:
    "Stop\<^sub>A\<^sub>P \<squnion>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P = AP (true \<turnstile> ?J)"
    apply (simp only: AP_angelic_choice Stop_AP_design Skip_AP_design
        AP_true_design[OF J_wf J_PBMH J_ok] RA2_conj
        RA2_stop_post RA2_skip_post RA1_conj)
    apply (simp add: design_inf expr_if_def fun_eq_iff)
    by pred_auto
  \<comment> \<open>A non-waiting handover is impossible: the deadlocked branch
      has no non-waiting final state.\<close>
  have handover_false:
    "(RA1 ?J ;;\<^sub>A\<^sub>D (\<not> rad_wait_lens\<^sup><)) = false"
    by (simp add: RA1_def aseq_ades_def stop_post_def skip_post_def
        ades_singleton_choice_def fun_eq_iff Let_def; pred_auto; auto)
  \<comment> \<open>The angel keeps only the waiting branch, which is deadlock.\<close>
  have continuation_stop:
    "(RA1 ?J ;;\<^sub>A\<^sub>D
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> true)) =
     stop_post"
    apply (simp add: RA1_def aseq_ades_def stop_post_def
        skip_post_def ades_singleton_choice_def ades_state_choice_def
        expr_if_def rad_trace_extensions_def true_pred_def
        fun_eq_iff Let_def)
    apply clarify
    subgoal for a b
      by (cases "astate.s\<^sub>v (des_vars.more a)";
          cases "des_vars.more a"; cases a;
          cases "des_vars.more b"; cases b;
          auto simp add: lens_defs des_vars.ok_def rad_state.wait_def
            astate.s_def des_vars.more\<^sub>L_def conj_pred_def
            true_pred_def intro: order_trans;
          rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False) y"
            in bexI;
          auto)
    done
  show ?thesis
    apply (simp only: choice_AP)
    by (simp only: AP_true_design_seq_Chaos[OF J_wf J_PBMH J_ok]
        handover_false continuation_stop pred_ba.compl_bot_eq Stop_AP_def)
qed

subsection \<open>Prefixing into divergence (Example 27, Lemma 14)\<close>

(* Support laws kept in this session instead of the reactive angelic
   design layer so the parent session heaps stay valid. *)

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
    subgoal for ok tr ref wait more morea okv ac moreb refv waitv trv
      by (frule (1) append_le,
          rule_tac x="\<lparr>rad_state.tr\<^sub>v = trv, ref\<^sub>v = refv,
            wait\<^sub>v = waitv\<rparr>" in bexI; simp)
    subgoal for trv acv trv2 refv waitv
      by (frule list_append_prefixD, frule diff_le,
          rule_tac x="trv2 - trv" in exI, rule conjI,
          rule_tac x=refv in exI, rule_tac x=waitv in exI,
          rule_tac x=trv2 in exI; simp)
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
  subgoal for ok tr ref wait more morea okv ac moreb refv waitv trv
    by (drule sym, frule (1) nil,
        rule_tac x="\<lparr>rad_state.tr\<^sub>v = trv, ref\<^sub>v = refv,
          wait\<^sub>v = True\<rparr>" in bexI; simp)
  subgoal for tr ac ref wait
    by (rule_tac x=ref in exI, rule_tac x=True in exI, rule conjI,
        rule_tac x=tr in exI,
        simp_all add: diff_cancel zero_list_def)
  done
qed

(* The ok-in counterpart of RA1_unrest_ok_out, for the RA1-true
   failure condition of ChaosCSP_AP. *)
lemma RA1_unrest_ok_in [unrest]:
  "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> RA1 P"
  apply (simp add: unrest_lens RA1_def Let_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

(* Handing the prefix over to any non-waiting continuation is always
   possible: performing the event reaches a non-waiting state. *)
lemma prefix_handover_nonwait:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D (\<not> rad_wait_lens\<^sup><)) = true"
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def
      rad_state.wait_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_state.wait_def astate.s_def
      des_vars.more\<^sub>L_def true_pred_def conj_pred_def
      not_pred_def SEXP_def subst_ext_def
      subst_app_def ex_in_conv[symmetric])
  apply (rule allI, rule conjI)
  subgoal for aa
    by (rule_tac x="\<lparr>rad_state.tr\<^sub>v =
        rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more aa)) @ [a],
        ref\<^sub>v = {}, wait\<^sub>v = False\<rparr>" in bexI;
        simp add: trace_le_append)
  subgoal for aa
    by (rule_tac x="\<lparr>rad_state.tr\<^sub>v =
        rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more aa)) @ [a],
        ref\<^sub>v = {}, wait\<^sub>v = False\<rparr>" in exI;
        simp add: trace_le_append)
  done

(* Paper Example 27 / Thesis Example 45: the potential for divergence
   after the event leads to immediate divergence. *)
lemma Prefix_Chaos_AP:
  "(a \<rightarrow>\<^sub>A\<^sub>P Chaos\<^sub>A\<^sub>P) = Chaos\<^sub>A\<^sub>P"
  unfolding Prefix_AP_def PrefixSkip_AP_def
  apply (subst AP_true_design_seq_Chaos[OF PrefixSkip_AP_facts])
  by (simp only: prefix_handover_nonwait pred_ba.compl_top_eq
      design_false_pre Chaos_AP_def)

(* Thesis Section 6.4.8: the compound a \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P
   coincides with the Definition 57 primitive, as at the RAD layer
   (Prefix_Skip_RAD_RA). *)
lemma Prefix_Skip_AP:
  "(a \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) = PrefixSkip_AP a"
  unfolding Prefix_AP_def PrefixSkip_AP_def Skip_AP_def
  apply (subst AP_true_design_seq[OF PrefixSkip_AP_facts Skip_AP_facts])
  by (simp only: prefix_continuation_skip)

(* Paper Lemma 14 / Thesis Lemma L.6.4.6: prefixing into ChaosCSP_AP
   cannot backtrack the event to avoid the divergence that follows,
   mirroring a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D
   (Prefix_Chaos_RAD_RA). *)
lemma Prefix_ChaosCSP_AP:
  "(a \<rightarrow>\<^sub>A\<^sub>P ChaosCSP\<^sub>A\<^sub>P) =
   AP ((\<not> prefix_diverge_post a) \<turnstile> prefix_offer_post a)"
proof -
  let ?pdp = "prefix_diverge_post a"
  let ?pop = "prefix_offer_post a"
  have prefix_PBMH: "RA1 (prefix_post a) is PBMH_ades"
    by (rule RA1_PBMH_ades_closure) (simp add: Healthy_def')
  have prefix_shape:
    "PrefixSkip_AP a =
     ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> false)) \<turnstile>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA1 (prefix_post a)))"
    by (simp only: PrefixSkip_AP_design pred_ba.compl_bot_eq
        expr_if_idem)
  have chaoscsp_shape:
    "(ChaosCSP\<^sub>A\<^sub>P :: ('e list, 'e) reactive_angelic_design) =
     ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA1 true)) \<turnstile>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> false))"
    apply (simp only: ChaosCSP_AP_design)
    by (simp add: expr_if_def fun_eq_iff; pred_auto)
  have seq_form:
    "(a \<rightarrow>\<^sub>A\<^sub>P ChaosCSP\<^sub>A\<^sub>P) =
     RA3AP ((\<not> ?pdp) \<turnstile> (?pop \<or> ?pdp))"
    unfolding Prefix_AP_def
    apply (subst prefix_shape, subst chaoscsp_shape)
    apply (subst AP_wait_design_seq[
        where F=false and T="RA1 (prefix_post a)"
          and G="RA1 true" and U=false])
          apply (simp_all add: unrest false_PBMH_ades prefix_PBMH)
    by (simp only: aseq_ades_false_left pred_ba.compl_bot_eq
        pred_ba.inf_top_left pred_impl_laws pred_ba.double_compl
        prefix_handover_diverge[unfolded RA2_RA1_true]
        prefix_continuation_chaos[unfolded RA2_RA1_true])
  have design_eq:
    "((\<not> ?pdp) \<turnstile> ?pop) =
     ((\<not> ?pdp) \<turnstile> (?pop \<or> ?pdp))"
    by pred_auto
  have N_PBMH:
    "((\<not> ?pdp) \<turnstile> (?pop \<or> ?pdp)) is PBMH_ades"
    by (rule PBMH_ades_design_closure;
        simp add: Healthy_def' PBMH_ades_disj)
  have absorb:
    "(ac_non_empty \<and> ((\<not> ?pdp) \<and> (?pop \<or> ?pdp))) =
     ((\<not> ?pdp) \<and> (?pop \<or> ?pdp))"
    by pred_auto
  have RA2_N:
    "RA2 ((\<not> ?pdp) \<turnstile> (?pop \<or> ?pdp)) =
     ((\<not> ?pdp) \<turnstile> (?pop \<or> ?pdp))"
    by (simp only: RA2_design_distrib RA2_not RA2_disj
        RA2_prefix_diverge_post RA2_prefix_offer_post)
  have recognised:
    "AP ((\<not> ?pdp) \<turnstile> (?pop \<or> ?pdp)) =
     RA3AP ((\<not> ?pdp) \<turnstile> (?pop \<or> ?pdp))"
    apply (subst AP_design_RA3AP_RA2[
        OF _ _ N_PBMH RA1_true_absorb_lift[OF absorb]])
    by (simp_all add: unrest RA2_N)
  show ?thesis
    by (simp only: seq_form design_eq recognised)
qed

subsection \<open>Avoiding divergence altogether (Example 28)\<close>

(* Paper Example 28 / Thesis Example 46: the angel avoids the
   divergence following the event a altogether by choosing the
   prefixing on b, a property not available in the theory of
   reactive angelic designs (Prefix_Skip_Chaos_different_events). *)
lemma Prefix_Chaos_Skip_angelic_choice:
  "(a \<rightarrow>\<^sub>A\<^sub>P Chaos\<^sub>A\<^sub>P) \<squnion>\<^sub>A\<^sub>P (b \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) = (b \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P)"
  apply (simp only: Prefix_Chaos_AP)
  apply (subst inf.commute)
  by (rule Chaos_AP_angelic_choice_unit[
        OF Prefix_AP_closure[OF Skip_AP_is_AP]])

end
