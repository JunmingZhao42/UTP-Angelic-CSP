section \<open>Reactive Angelic Design Examples\<close>

text \<open>
  The worked examples of the paper's Section 6.4 (Examples 15--17 and
  Lemmas 8--9), collected apart from the operator theories.
\<close>

theory utp_rad_examples
  imports utp_rad_seq
begin

subsection \<open>Angelic choice of Stop and Skip (Example 15, Lemma 8)\<close>

(* Paper Example 15 / Thesis Example 32: the angelic choice between
   deadlock and termination is not resolved in favour of either. *)
lemma Stop_Skip_angelic_choice:
  "Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D =
   (RA \<circ> A) (true \<turnstile> (stop_post \<and> skip_post))"
proof -
  have "Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D =
      (RA \<circ> A) ((true \<turnstile> stop_post) \<squnion> (true \<turnstile> skip_post))"
    unfolding Stop_RAD_def Skip_RAD_def
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
     apply (rule stop_design_is_H)
    by (rule skip_design_is_H)
  also have "... = (RA \<circ> A) (true \<turnstile> (stop_post \<and> skip_post))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed

(* Example 15 with the A absorbed into RA. *)
lemma Stop_Skip_angelic_choice_RA:
  "Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D =
   RA (true \<turnstile> (stop_post \<and> skip_post))"
  unfolding Stop_Skip_angelic_choice
  by (rule RA_A_absorb_design_true;
      (rule PBMH_ades_conj_closure)?;
      simp add: Healthy_def' unrest)

(* Under the singleton angelic choice imposed by ac2p, a final state
   cannot both wait and terminate. *)
lemma rad_ac2p_stop_skip_design:
  "rad_ac2p (true \<turnstile> (stop_post \<and> skip_post)) = (true \<turnstile> false)"
  by (simp add: rad_ac2p_def; pred_auto; blast)

abbreviation top_R ("\<top>\<^sub>R") where "\<top>\<^sub>R \<equiv> \<^bold>R (true \<turnstile> false)"

(* Paper Lemma 8 / Thesis Lemma L.5.4.2: mapping the choice between
   deadlock and termination into CSP yields the top of the reactive
   design lattice. *)
lemma rad_ac2p_Stop_Skip:
  "rad_ac2p (Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) = \<top>\<^sub>R"
proof -
  have SS_PBMH: "(stop_post \<and> skip_post) is PBMH_ades"
    by (rule PBMH_ades_conj_closure; simp add: Healthy_def')
  have D_PBMH: "(true \<turnstile> (stop_post \<and> skip_post)) is PBMH_ades"
    unfolding Healthy_def'
    by (simp add: design_as_disj PBMH_ades_disj PBMH_ades_conj_ok
        SS_PBMH[unfolded Healthy_def'])
  have D_H: "(true \<turnstile> (stop_post \<and> skip_post)) is \<^bold>H"
    by (rule design_is_H1_H2; simp add: unrest)
  have "rad_ac2p (Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) =
      rad_ac2p (RA (true \<turnstile> (stop_post \<and> skip_post)))"
    by (simp only: Stop_Skip_angelic_choice
        RA_A_absorb[OF D_PBMH D_H])
  also have "... = \<^bold>R (rad_ac2p (true \<turnstile> (stop_post \<and> skip_post)))"
    by (rule rad_ac2p_RA[OF D_PBMH, simplified comp_apply])
  also have "... = \<^bold>R (true \<turnstile> false)"
    by (simp only: rad_ac2p_stop_skip_design)
  finally show ?thesis .
qed

subsection \<open>Avoiding divergence after termination (Lemma 9)\<close>

(* Paper Lemma 9 / Thesis Lemma L.5.4.3: the angel avoids the
   terminating branch, since its handover to Chaos would diverge. *)
lemma Stop_Skip_seq_Chaos:
  "(Stop\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) ;;\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D = Stop\<^sub>R\<^sub>A\<^sub>D"
proof -
  let ?J = "stop_post \<and> skip_post"
  have J_PBMH: "?J is PBMH_ades"
    by (rule PBMH_ades_conj_closure; simp add: Healthy_def')
  have not_true_PBMH:
      "(\<not> (true :: 'e reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: 'e reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> ?J"
      "$ok\<^sup>< \<sharp> (false :: 'e reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> (true :: 'e reactive_angelic_design)"
    by (simp_all add: unrest)
  have handover_false:
      "(RA1 ?J ;;\<^sub>A\<^sub>D
        ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 true))) = false"
    by (simp add: RA1_def aseq_ades_def stop_post_def skip_post_def ades_singleton_choice_def
        fun_eq_iff Let_def; pred_auto; auto)
  have continuation_stop:
      "(RA1 ?J ;;\<^sub>A\<^sub>D
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          RA2 (RA1 true))) = stop_post"
    apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
    apply (simp add: RA1_def aseq_ades_def stop_post_def
        skip_post_def ades_singleton_choice_def ades_state_choice_def expr_if_def
        rad_trace_extensions_def fun_eq_iff Let_def)
    apply clarify
    subgoal for a b
      by (cases "astate.s\<^sub>v (des_vars.more a)";
          cases "des_vars.more a"; cases a;
          cases "des_vars.more b"; cases b;
          auto simp add: lens_defs des_vars.ok_def rad_state.wait_def
            astate.s_def des_vars.more\<^sub>L_def conj_pred_def true_pred_def
            intro: order_trans;
          rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False) y"
            in bexI;
          auto)
    done
  have seq_form:
      "(RA (true \<turnstile> ?J) ;;\<^sub>D\<^sub>A RA true) =
       RA (true \<turnstile> stop_post)"
    using RA_design_seq[
      where P=true and Q="?J" and R=false and S=true,
      OF component_unrests not_true_PBMH J_PBMH]
    by (simp only: design_false_pre pred_ba.compl_top_eq
        pred_ba.compl_bot_eq pred_impl_laws pred_ba.inf_idem
        RA1_false aseq_ades_false_left handover_false
        continuation_stop)
  show ?thesis
    by (subst Stop_Skip_angelic_choice_RA;
        simp only: Chaos_RAD_RA seq_form Stop_RAD_RA)
qed

subsection \<open>Prefixed deadlock avoids divergence (Example 16)\<close>

(* Postcondition of a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D: either the
   event has not yet happened and is offered, or it has happened and
   the process deadlocks. *)
definition prefix_stop_post :: "'e \<Rightarrow> 'e reactive_angelic_design" where
[pred]: "prefix_stop_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_state.wait\<^sub>v y \<and>
    (rad_state.tr\<^sub>v y =
       rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
     a \<notin> rad_state.ref\<^sub>v y \<or>
     rad_state.tr\<^sub>v y =
       rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a]))"

(* The paper's final-state quantifier is the predicate mapping p2ac. *)
lemma prefix_stop_post_p2ac:
  "prefix_stop_post a = p2ac \<lceil>(\<lambda> (s, y).
    rad_state.wait\<^sub>v y \<and>
    (rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s \<and>
       a \<notin> rad_state.ref\<^sub>v y \<or>
     rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s @ [a]))\<rceil>\<^sub>D"
  by (simp add: prefix_stop_post_def p2ac_def fun_eq_iff subst_app_def
      subst_ext_def SEXP_def lens_defs des_vars.more\<^sub>L_def;
      pred_auto; blast)

lemma prefix_stop_post_PBMH [simp]:
  "PBMH_ades (prefix_stop_post a) = prefix_stop_post a"
  by (simp only: prefix_stop_post_p2ac PBMH_ades_p2ac)

lemma prefix_stop_post_unrest_ok [unrest]:
  "$ok\<^sup>> \<sharp> prefix_stop_post a"
  apply (simp add: unrest_lens prefix_stop_post_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

(* The continuation of prefixing into Stop: before the event the
   process waits offering a; after it the handover state is a
   deadlocked state whose trace records the event. *)
lemma prefix_continuation_stop:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 stop_post))) = prefix_stop_post a"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_stop_post)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def stop_post_def
      prefix_stop_post_def ades_state_choice_def expr_if_def
      rad_trace_extensions_def fun_eq_iff Let_def
      lens_defs rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def
      bex_nonempty_absorb)
  apply clarify
  subgoal for x0 y0
    apply (rule iffI)
     apply fastforce
    apply (elim bexE conjE disjE)
     apply (rule_tac x=y in bexI; fastforce)
    apply (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False) y"
        in bexI; fastforce)
    done
  done

(* Thesis Theorem T.5.4.29 instantiated to Stop: the design form of
   a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D. *)
lemma Prefix_Stop_RAD_RA:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) = RA (true \<turnstile> prefix_stop_post a)"
proof -
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: 'e reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> (true :: 'e reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> stop_post"
    by (simp_all add: unrest)
  have not_true_PBMH:
      "(\<not> (true :: 'e reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have prefix_PBMH: "prefix_post a is PBMH_ades"
    by (simp add: Healthy_def')
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) =
      (RA (true \<turnstile> prefix_post a) ;;\<^sub>D\<^sub>A
       RA (true \<turnstile> stop_post))"
    by (simp only: Prefix_RAD_def PrefixSkip_RAD_RA Stop_RAD_RA)
  also have "... = RA (true \<turnstile> prefix_stop_post a)"
    using RA_design_seq[
      where P=true and Q="prefix_post a" and R=true and S=stop_post,
      OF component_unrests not_true_PBMH prefix_PBMH]
    by (simp only: pred_ba.compl_top_eq pred_ba.compl_bot_eq
        RA1_false RA2_false aseq_ades_false_left
        pred_ba.inf_bot_right RA1_aseq_false pred_ba.inf_idem
        pred_impl_laws prefix_continuation_stop)
  finally show ?thesis .
qed

(* The angelic choice of a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D and
   Skip\<^sub>R\<^sub>A\<^sub>D, with the A absorbed into RA. *)
lemma Prefix_Stop_Skip_angelic_choice_RA:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D =
   RA (true \<turnstile> (prefix_stop_post a \<and> skip_post))"
proof -
  have psp_absorb:
      "(RA \<circ> A) (true \<turnstile> prefix_stop_post a) =
       RA (true \<turnstile> prefix_stop_post a)"
    by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)
  have conj_absorb:
      "(RA \<circ> A) (true \<turnstile> (prefix_stop_post a \<and> skip_post)) =
       RA (true \<turnstile> (prefix_stop_post a \<and> skip_post))"
    by (rule RA_A_absorb_design_true;
        (rule PBMH_ades_conj_closure)?;
        simp add: Healthy_def' unrest)
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D =
      (RA \<circ> A) (true \<turnstile> prefix_stop_post a) \<squnion>
      (RA \<circ> A) (true \<turnstile> skip_post)"
    by (simp only: Prefix_Stop_RAD_RA psp_absorb Skip_RAD_def)
  also have "... = (RA \<circ> A)
      ((true \<turnstile> prefix_stop_post a) \<squnion> (true \<turnstile> skip_post))"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
     apply (rule design_is_H1_H2; simp add: unrest)
    by (rule design_is_H1_H2; simp add: unrest)
  also have "... = (RA \<circ> A)
      (true \<turnstile> (prefix_stop_post a \<and> skip_post))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis
    by (simp only: conj_absorb)
qed

(* Paper Example 16 / Thesis Example 33: the angel avoids the
   divergence following termination by choosing to perform a and
   deadlock. *)
lemma Prefix_Stop_Skip_seq_Chaos:
  "((a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) ;;\<^sub>R\<^sub>A\<^sub>D
   Chaos\<^sub>R\<^sub>A\<^sub>D = (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D)"
proof -
  let ?J = "prefix_stop_post a \<and> skip_post"
  have J_PBMH: "?J is PBMH_ades"
    by (rule PBMH_ades_conj_closure; simp add: Healthy_def')
  have not_true_PBMH:
      "(\<not> (true :: 'e reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: 'e reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> ?J"
      "$ok\<^sup>< \<sharp> (false :: 'e reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> (true :: 'e reactive_angelic_design)"
    by (simp_all add: unrest)
  have handover_false:
      "(RA1 ?J ;;\<^sub>A\<^sub>D
        ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 true))) = false"
    by (simp add: RA1_def aseq_ades_def prefix_stop_post_def
        skip_post_def ades_singleton_choice_def fun_eq_iff Let_def; pred_auto; auto)
  have continuation_prefix_stop:
      "(RA1 ?J ;;\<^sub>A\<^sub>D
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          RA2 (RA1 true))) = prefix_stop_post a"
    apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
    apply (simp add: RA1_def aseq_ades_def prefix_stop_post_def
        skip_post_def ades_singleton_choice_def ades_state_choice_def expr_if_def
        rad_trace_extensions_def fun_eq_iff Let_def
        lens_defs rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def
        conj_pred_def true_pred_def ex_in_conv[symmetric])
    apply clarify
    subgoal for x0 y0
      apply (rule iffI)
       apply fastforce
      apply (elim bexE conjE)
      apply (rule conjI)
       apply (rule_tac x=y in bexI; fastforce)
      apply (rule conjI)
       apply (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
           (rad_state.tr\<^sub>v_update
             (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)))
             y)" in bexI)
        apply fastforce
       apply (rule IntI)
        apply fastforce
       apply (simp only: mem_Collect_eq)
       apply (rule conjI)
        apply fastforce
       apply (rule impI)
       apply (rule_tac x=y in exI)
       apply fastforce
      apply (rule_tac x=y in exI)
      apply fastforce
      done
    done
  have seq_form:
      "(RA (true \<turnstile> ?J) ;;\<^sub>D\<^sub>A RA true) =
       RA (true \<turnstile> prefix_stop_post a)"
    using RA_design_seq[
      where P=true and Q="?J" and R=false and S=true,
      OF component_unrests not_true_PBMH J_PBMH]
    by (simp only: design_false_pre pred_ba.compl_top_eq
        pred_ba.compl_bot_eq pred_impl_laws pred_ba.inf_idem
        RA1_false aseq_ades_false_left handover_false
        continuation_prefix_stop)
  show ?thesis
    by (subst Prefix_Stop_Skip_angelic_choice_RA;
        simp only: Chaos_RAD_RA seq_form Prefix_Stop_RAD_RA[symmetric])
qed

subsection \<open>Prefixed termination avoids divergence (Example 17)\<close>

(* The failure observation of a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D
   Chaos\<^sub>R\<^sub>A\<^sub>D: the event has occurred. *)
definition prefix_diverge_post :: "'e \<Rightarrow> 'e reactive_angelic_design"
where
[pred]: "prefix_diverge_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<le>
    rad_state.tr\<^sub>v y)"

(* The event is offered and has not yet occurred. *)
definition prefix_offer_post :: "'e \<Rightarrow> 'e reactive_angelic_design"
where
[pred]: "prefix_offer_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_state.wait\<^sub>v y \<and>
    rad_state.tr\<^sub>v y =
      rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
    a \<notin> rad_state.ref\<^sub>v y)"

lemma prefix_diverge_post_p2ac:
  "prefix_diverge_post a = p2ac \<lceil>(\<lambda> (s, y).
    rad_state.tr\<^sub>v s @ [a] \<le> rad_state.tr\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: prefix_diverge_post_def p2ac_def fun_eq_iff
      subst_app_def subst_ext_def SEXP_def lens_defs
      des_vars.more\<^sub>L_def; pred_auto; blast)

lemma prefix_offer_post_p2ac:
  "prefix_offer_post a = p2ac \<lceil>(\<lambda> (s, y).
    rad_state.wait\<^sub>v y \<and> rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s \<and>
    a \<notin> rad_state.ref\<^sub>v y)\<rceil>\<^sub>D"
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
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 true))) =
   prefix_diverge_post a"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def expr_if_def
      rad_state.wait_def
      prefix_diverge_post_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_state.wait_def astate.s_def
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
       apply (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
           (rad_state.tr\<^sub>v_update
             (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
             y)" in bexI; fastforce)
      by (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
          (rad_state.tr\<^sub>v_update
            (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
            y)" in exI; fastforce)
    done
  done

(* The continuation of the prefix into Chaos: either the event is
   still offered, or it has occurred and anything may follow. *)
lemma prefix_continuation_chaos:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 true))) =
   (prefix_offer_post a \<or> prefix_diverge_post a)"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      prefix_offer_post_def prefix_diverge_post_def
      ades_state_choice_def expr_if_def rad_trace_extensions_def
      fun_eq_iff Let_def lens_defs rad_state.wait_def astate.s_def
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
       apply (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
           (rad_state.tr\<^sub>v_update
             (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
             y)" in bexI; fastforce)
      by (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
          (rad_state.tr\<^sub>v_update
            (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
            y)" in exI; fastforce)
    done
  done

(* Thesis Theorem T.5.4.29 instantiated to Chaos. *)
lemma Prefix_Chaos_RAD_RA:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D) =
   RA ((\<not> prefix_diverge_post a) \<turnstile>
       (prefix_offer_post a \<or> prefix_diverge_post a))"
proof -
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: 'e reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> (false :: 'e reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> (true :: 'e reactive_angelic_design)"
    by (simp_all add: unrest)
  have not_true_PBMH:
      "(\<not> (true :: 'e reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have prefix_PBMH: "prefix_post a is PBMH_ades"
    by (simp add: Healthy_def')
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D) =
      (RA (true \<turnstile> prefix_post a) ;;\<^sub>D\<^sub>A RA true)"
    by (simp only: Prefix_RAD_def PrefixSkip_RAD_RA Chaos_RAD_RA)
  also have "... =
      RA ((\<not> prefix_diverge_post a) \<turnstile>
          (prefix_offer_post a \<or> prefix_diverge_post a))"
    using RA_design_seq[
      where P=true and Q="prefix_post a" and R=false and S=true,
      OF component_unrests not_true_PBMH prefix_PBMH]
    by (simp only: design_false_pre pred_ba.compl_top_eq
        pred_ba.compl_bot_eq pred_impl_laws RA1_false
        aseq_ades_false_left prefix_handover_diverge
        prefix_continuation_chaos pred_ba.inf_top_left)
  finally show ?thesis .
qed

(* Paper Example 17 / Thesis Example 34: the angel avoids the
   divergence following the event by choosing termination. *)
lemma Prefix_Skip_Chaos_angelic_choice:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D
   (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D) =
   (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D)"
proof -
  have skip_absorb:
      "(RA \<circ> A) (true \<turnstile> prefix_post a) =
       RA (true \<turnstile> prefix_post a)"
    by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)
  have chaos_PBMH:
      "(\<not> (\<not> prefix_diverge_post a)) is PBMH_ades"
    by (simp add: pred_ba.double_compl Healthy_def')
  have chaos_absorb:
      "(RA \<circ> A) ((\<not> prefix_diverge_post a) \<turnstile>
          (prefix_offer_post a \<or> prefix_diverge_post a)) =
       RA ((\<not> prefix_diverge_post a) \<turnstile>
          (prefix_offer_post a \<or> prefix_diverge_post a))"
    by (rule RA_A_absorb_design[OF chaos_PBMH])
      (simp_all add: Healthy_def' PBMH_ades_disj unrest)
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D
      (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D) =
      (RA \<circ> A) (true \<turnstile> prefix_post a) \<squnion>
      (RA \<circ> A) ((\<not> prefix_diverge_post a) \<turnstile>
        (prefix_offer_post a \<or> prefix_diverge_post a))"
    by (simp only: Prefix_Skip_RAD_RA Prefix_Chaos_RAD_RA
        skip_absorb chaos_absorb)
  also have "... = (RA \<circ> A)
      ((true \<turnstile> prefix_post a) \<squnion>
       ((\<not> prefix_diverge_post a) \<turnstile>
        (prefix_offer_post a \<or> prefix_diverge_post a)))"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok pred_ba.double_compl)
     apply (rule design_is_H1_H2; simp add: unrest)
    by (rule design_is_H1_H2; simp add: unrest)
  also have "... = (RA \<circ> A) (true \<turnstile> prefix_post a)"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by (simp add: prefix_post_def expr_if_def rad_state.wait_def
        SEXP_def lens_defs prefix_offer_post_def
        prefix_diverge_post_def design_def fun_eq_iff Let_def;
        pred_auto)
  also have "... = (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D)"
    by (simp only: Prefix_Skip_RAD_RA skip_absorb[symmetric])
  finally show ?thesis .
qed

end
