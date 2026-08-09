section \<open>Reactive Angelic Design Examples\<close>

text \<open>
  The worked examples of the paper's Section 6 (Examples 11--21 and
  Lemmas 5, 8, and 9), collected apart from the operator theories.
\<close>

theory utp_rad_examples
  imports utp_rad_nd
begin

subsection \<open>RA1 and PBMH do not commute (Example 11)\<close>

(* Paper Example 11: the two compositions disagree on ac = {}. *)
lemma RA1_PBMH_ades_ac_empty_example:
  "RA1 (PBMH_ades rad_ac_empty) = RA1 true \<and>
   PBMH_ades (RA1 rad_ac_empty) = false"
  by (simp only: RA1_PBMH_ades_ac_empty PBMH_ades_RA1_ac_empty)

subsection \<open>Angelic choice of Stop and Skip (Example 15, Lemma 8)\<close>

(* Paper Example 15 / Thesis Example 32: stop \<squnion> skip *)
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
      "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> ?J"
      "$ok\<^sup>< \<sharp> (false :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
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
definition prefix_stop_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design" where
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
      prefix_stop_post_def ades_singleton_choice_def
      ades_state_choice_def expr_if_def
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
      "$ok\<^sup>> \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> stop_post"
    by (simp_all add: unrest)
  have not_true_PBMH:
      "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) is PBMH_ades"
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
      "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> ?J"
      "$ok\<^sup>< \<sharp> (false :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
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
definition prefix_diverge_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design"
where
[pred]: "prefix_diverge_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<le>
    rad_state.tr\<^sub>v y)"

(* The event is offered and has not yet occurred. *)
definition prefix_offer_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design"
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
      "$ok\<^sup>> \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> (false :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
    by (simp_all add: unrest)
  have not_true_PBMH:
      "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) is PBMH_ades"
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


subsection \<open>Different prefixed deadlocks (Example 12)\<close>

(* Paper Example 12: both prefixed deadlocks must agree on a final state. *)
lemma Prefix_Stop_Stop_angelic_choice:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D (b \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) =
   (RA \<circ> A) (true \<turnstile> (prefix_stop_post a \<and> prefix_stop_post b))"
proof -
  have absorb_a:
      "(RA \<circ> A) (true \<turnstile> prefix_stop_post a) =
       RA (true \<turnstile> prefix_stop_post a)"
    by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)
  have absorb_b:
      "(RA \<circ> A) (true \<turnstile> prefix_stop_post b) =
       RA (true \<turnstile> prefix_stop_post b)"
    by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D
        (b \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D) =
        (RA \<circ> A) (true \<turnstile> prefix_stop_post a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
        (RA \<circ> A) (true \<turnstile> prefix_stop_post b)"
    by (simp only: Prefix_Stop_RAD_RA absorb_a absorb_b)
  also have "... = (RA \<circ> A)
      ((true \<turnstile> prefix_stop_post a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
       (true \<turnstile> prefix_stop_post b))"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
      apply (simp add: Healthy_def' design_as_disj PBMH_ades_disj
          PBMH_ades_conj_ok)
     apply (rule design_is_H1_H2; simp add: unrest)
    by (rule design_is_H1_H2; simp add: unrest)
  also have "... = (RA \<circ> A)
      (true \<turnstile> (prefix_stop_post a \<and> prefix_stop_post b))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed


subsection \<open>CSP agreement of different prefixed deadlocks (Lemma 5)\<close>

(* Thesis Lemma L.A.3.3 normal form of CSP prefix followed by Stop. *)
definition Prefix_Stop_R :: "'e \<Rightarrow> ('e list, 'e set) rp_hrel"
  ("_ \<rightarrow>\<^sub>R Stop\<^sub>R" [81] 80) where
[pred]: "a \<rightarrow>\<^sub>R Stop\<^sub>R = \<^bold>R (true \<turnstile> (\<lambda> (s, y).
  rea_vars.wait\<^sub>v y \<and>
  (rea_vars.tr\<^sub>v y = rea_vars.tr\<^sub>v s \<and>
     a \<notin> rea_vars.more y \<or>
   rea_vars.tr\<^sub>v y = rea_vars.tr\<^sub>v s @ [a])))"

definition csp_prefix_stop_pair_post ::
  "'e \<Rightarrow> 'e \<Rightarrow> ('e list, 'e set) rp_hrel" where
[pred]: "csp_prefix_stop_pair_post a b = (\<lambda> (s, y).
  rea_vars.tr\<^sub>v y = rea_vars.tr\<^sub>v s \<and>
  a \<notin> rea_vars.more y \<and> b \<notin> rea_vars.more y \<and>
  rea_vars.wait\<^sub>v y)"

(* Paper Lemma 5. The distinctness premise rules out agreement after an event. *)
lemma Prefix_Stop_Stop_R:
  fixes a b :: 'e
  assumes "a \<noteq> b"
  shows "(a \<rightarrow>\<^sub>R Stop\<^sub>R) \<squnion>
      (b \<rightarrow>\<^sub>R Stop\<^sub>R) =
    \<^bold>R (true \<turnstile> csp_prefix_stop_pair_post a b)"
proof -
  have R3c_conj:
      "R3c (P \<and> Q) = (R3c P \<and> R3c Q)"
      for P Q :: "('e list, 'e set) rp_hrel"
    by pred_auto
  have R2c_conj:
      "R2c (P \<and> Q) = (R2c P \<and> R2c Q)"
      for P Q :: "('e list, 'e set) rp_hrel"
    by pred_auto
  have RH_choice:
      "\<^bold>R P \<squnion> \<^bold>R Q = \<^bold>R (P \<squnion> Q)"
      for P Q :: "('e list, 'e set) rp_hrel"
    by (simp only: conj_pred_def[symmetric];
        simp add: RH_def R1_conj R2c_conj R3c_conj)
  show ?thesis
    apply (simp only: Prefix_Stop_R_def RH_choice)
    apply (rule arg_cong[where f=RH])
    apply (simp only: design_inf)
    apply (simp add: csp_prefix_stop_pair_post_def fun_eq_iff)
    using assms
    by (pred_auto; auto)
qed


subsection \<open>Removing divergence (Examples 20-21)\<close>

(* Paper Example 20. *)
lemma NDRAD_Chaos_example:
  "NDRAD Chaos\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>R\<^sub>A\<^sub>D"
  by (rule NDRAD_Chaos)

(* Paper Example 21. *)
lemma NDRAD_Prefix_Skip:
  "NDRAD (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) =
   (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D)"
proof -
  have choice_absorb:
      "(RA \<circ> A) (true \<turnstile> true) = RA (true \<turnstile> true)"
    by (rule RA_A_absorb_design_true[OF true_PBMH_ades];
        simp add: unrest)
  have design_absorb:
      "((true \<turnstile> prefix_post a) \<and> (true \<turnstile> true)) =
       (true \<turnstile> prefix_post a)"
    by (simp add: design_def fun_eq_iff; pred_auto)
  have "NDRAD (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) =
      (RA (true \<turnstile> prefix_post a) \<and>
       RA (true \<turnstile> true))"
    by (simp only: NDRAD_def RAD_angelic_choice Prefix_Skip_RAD_RA
        Choice_RAD_alt choice_absorb)
  also have "... = RA
      ((true \<turnstile> prefix_post a) \<and> (true \<turnstile> true))"
    by (simp only: RA_conj)
  also have "... = RA (true \<turnstile> prefix_post a)"
    by (simp only: design_absorb)
  finally show ?thesis
    by (simp only: Prefix_Skip_RAD_RA)
qed


subsection \<open>Different prefixed events (Example 18)\<close>

lemma Prefix_Choice_RAD_RA:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Choice\<^sub>R\<^sub>A\<^sub>D) =
   RA (true \<turnstile>
       (prefix_offer_post a \<or> prefix_diverge_post a))"
proof -
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: ('e list, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> (true :: ('e list, 'e) reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> (true :: ('e list, 'e) reactive_angelic_design)"
    by (simp_all add: unrest)
  have not_true_PBMH:
      "(\<not> (true :: ('e list, 'e) reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have prefix_PBMH: "prefix_post a is PBMH_ades"
    by (simp add: Healthy_def')
  have choice_absorb:
      "(RA \<circ> A) (true \<turnstile> true) = RA (true \<turnstile> true)"
    by (rule RA_A_absorb_design_true[OF true_PBMH_ades]; simp add: unrest)
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Choice\<^sub>R\<^sub>A\<^sub>D) =
      (RA (true \<turnstile> prefix_post a) ;;\<^sub>D\<^sub>A
       RA (true \<turnstile> true))"
    by (simp only: Prefix_RAD_def PrefixSkip_RAD_RA Choice_RAD_alt
        choice_absorb)
  also have "... = RA (true \<turnstile>
      (prefix_offer_post a \<or> prefix_diverge_post a))"
    using RA_design_seq[
      where P=true and Q="prefix_post a" and R=true and S=true,
      OF component_unrests not_true_PBMH prefix_PBMH]
    by (simp only: pred_ba.compl_top_eq pred_ba.compl_bot_eq
        pred_impl_laws RA1_false RA2_false aseq_ades_false_left
        pred_ba.inf_bot_right RA1_aseq_false prefix_continuation_chaos
        pred_ba.inf_top_left)
  finally show ?thesis .
qed


(* Paper Example 18: divergence after b is replaced by non-divergent choice. *)
lemma Prefix_Skip_Chaos_different_events:
  assumes "a \<noteq> b"
  shows "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D
    (b \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D) =
    (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) \<squnion>\<^sub>R\<^sub>A\<^sub>D
    (b \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Choice\<^sub>R\<^sub>A\<^sub>D)"
proof -
  have design_eq:
      "((true \<turnstile> prefix_post a) \<and>
        ((\<not> prefix_diverge_post b) \<turnstile>
          (prefix_offer_post b \<or> prefix_diverge_post b))) =
       ((true \<turnstile> prefix_post a) \<and>
        (true \<turnstile>
          (prefix_offer_post b \<or> prefix_diverge_post b)))"
    apply (simp add: prefix_post_def prefix_offer_post_def
        prefix_diverge_post_def design_def expr_if_def rad_state.wait_def
        SEXP_def lens_defs fun_eq_iff Let_def)
    using assms
    by (pred_auto; auto)
  show ?thesis
    apply (simp only: RAD_angelic_choice Prefix_Skip_RAD_RA
        Prefix_Chaos_RAD_RA Prefix_Choice_RAD_RA RA_conj[symmetric])
    by (simp only: design_eq)
qed


subsection \<open>Mapping examples (Examples 13-14)\<close>

(* Paper Example 13: CSP Skip maps to the reactive angelic identity. *)
lemma rad_p2ac_Skip_R:
  "rad_p2ac (II\<^sub>C :: ('t::trace, 'e set) rp_hrel) = II_Rac"
  by (rule rad_p2ac_II_C)

definition prefix_offer_pair_post ::
  "'e \<Rightarrow> 'e \<Rightarrow> ('e list, 'e) reactive_angelic_design" where
[pred]: "prefix_offer_pair_post a b = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_state.wait\<^sub>v y \<and>
    rad_state.tr\<^sub>v y =
      rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
    a \<notin> rad_state.ref\<^sub>v y \<and> b \<notin> rad_state.ref\<^sub>v y)"

(* The singleton round trip in Paper Example 14. *)
lemma rad_p2ac_ac2p_prefix_stop_pair:
  assumes "a \<noteq> b"
  shows "(rad_p2ac \<circ> rad_ac2p)
      (prefix_stop_post a \<and> prefix_stop_post b) =
    prefix_offer_pair_post a b"
  apply (simp only: rad_p2ac_ac2p)
  apply (simp add: prefix_stop_post_def prefix_offer_pair_post_def
      fun_eq_iff lens_defs des_vars.more\<^sub>L_def conj_pred_def)  using assms
  apply (intro allI)
  apply (rule iffI)
   apply (elim exE conjE bexE)
   subgoal premises assms for aa ba ac0 y ya yb
   proof -
     have ya_eq: "ya = y"
       using assms(2,4) by auto
     have yb_eq: "yb = y"
       using assms(2,7) by auto
     show ?thesis
       using assms ya_eq yb_eq
       by (rule_tac x=y in bexI; auto)
   qed
  apply (elim bexE conjE)
  subgoal for aa ba y
    apply (rule_tac x="{y}" in exI)
    apply (rule conjI)
     apply (rule_tac x=y in bexI; auto)
    apply (rule conjI)
     apply (rule_tac x=y in bexI; auto)
    apply (rule_tac x=y in exI)
    by auto
  done


subsection \<open>External choice with Stop (Example 19)\<close>

(* Paper Example 19. *)
(* Todo: this proof is very lengthy by chatgpt *)
lemma Prefix_Chaos_Chaos_extchoice_Stop:
  fixes a b :: 'e
  shows
  "((a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D)
      \<squnion>\<^sub>R\<^sub>A\<^sub>D
      (b \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Chaos\<^sub>R\<^sub>A\<^sub>D))
      \<box>\<^sub>R\<^sub>A\<^sub>D Stop\<^sub>R\<^sub>A\<^sub>D =
    (RA \<circ> A)
      ((\<not> (prefix_diverge_post a \<and> prefix_diverge_post b)) \<turnstile>
        prefix_offer_pair_post a b)"
proof -
  have prefix_diverge_wf:
      "((prefix_diverge_post x :: ('e list, 'e) reactive_angelic_design)
        \<^sub>wf) = prefix_diverge_post x" for x :: 'e
    by (simp add: prefix_diverge_post_def rad_wait_false_def fun_eq_iff
        subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs
        alpha_defs)
  have prefix_offer_wf:
      "((prefix_offer_post x :: ('e list, 'e) reactive_angelic_design)
        \<^sub>wf) = prefix_offer_post x" for x :: 'e
    by (simp add: prefix_offer_post_def rad_wait_false_def fun_eq_iff
        subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs
        alpha_defs)
  have prefix_diverge_ok_out_subst:
      "(prefix_diverge_post x)\<lbrakk>\<guillemotleft>c\<guillemotright>/ok\<^sup>>\<rbrakk> =
        prefix_diverge_post x" for x :: 'e and c :: bool
    by (simp add: prefix_diverge_post_def fun_eq_iff subst_app_def
        subst_upd_def subst_id_def SEXP_def lens_defs des_vars.ok_def
        astate.s_def des_vars.more\<^sub>L_def)
  have prefix_offer_ok_out_subst:
      "(prefix_offer_post x)\<lbrakk>\<guillemotleft>c\<guillemotright>/ok\<^sup>>\<rbrakk> =
        prefix_offer_post x" for x :: 'e and c :: bool
    by (simp add: prefix_offer_post_def fun_eq_iff subst_app_def
        subst_upd_def subst_id_def SEXP_def lens_defs des_vars.ok_def
        astate.s_def des_vars.more\<^sub>L_def)
  note prefix_diverge_ok_out_subst[usubst]
  note prefix_offer_ok_out_subst[usubst]
  have chaos_absorb:
      "(RA \<circ> A) ((\<not> prefix_diverge_post x) \<turnstile>
          (prefix_offer_post x \<or> prefix_diverge_post x)) =
       RA ((\<not> prefix_diverge_post x) \<turnstile>
          (prefix_offer_post x \<or> prefix_diverge_post x))" for x :: 'e
    by (rule RA_A_absorb_design)
      (simp_all add: Healthy_def' PBMH_ades_disj unrest)
  have branch_components:
      "(((RA ((\<not> prefix_diverge_post x) \<turnstile>
          (prefix_offer_post x \<or> prefix_diverge_post x)))
          \<^sub>wf)\<^sup>f) =
          RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post x)) \<and>
       (((RA ((\<not> prefix_diverge_post x) \<turnstile>
          (prefix_offer_post x \<or> prefix_diverge_post x)))
          \<^sub>wf)\<^sup>t) =
          RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post x \<or>
            (prefix_offer_post x \<or> prefix_diverge_post x)))" for x :: 'e
  proof -
    let ?D = "prefix_diverge_post x"
    let ?T = "prefix_offer_post x \<or> ?D"
    let ?B = "?D \<or> (?T \<and> ok\<^sup>>)"
    have B_wf: "(?B \<^sub>wf) = ?B"
      by (simp only: rad_wait_false_disj rad_wait_false_conj
          prefix_diverge_wf prefix_offer_wf rad_wait_false_ok_out)
    have B_false: "?B\<^sup>f = ?D"
      by (simp add: usubst usubst_eval; pred_auto)
    have B_true: "?B\<^sup>t = ?T"
      by (simp add: usubst usubst_eval; pred_auto)
    have design_norm:
        "((\<not> (?B \<^sub>wf)\<^sup>f) \<turnstile> (?B \<^sub>wf)\<^sup>t) =
         ((\<not> ?D) \<turnstile> ?T)"
      by (simp only: B_wf B_false B_true)
    have false_component:
        "((rad_wait_false \<circ> RA \<circ> A)
          ((\<not> ?D) \<turnstile> ?T))\<^sup>f =
         (RA2 \<circ> RA1 \<circ> PBMH_ades)
          ((\<not> ok\<^sup><) \<or> (?B \<^sub>wf)\<^sup>f)"
      using RA_design_wf_ok_false[of ?B]
      by (simp only: design_norm)
    have true_component:
        "((rad_wait_false \<circ> RA \<circ> A)
          ((\<not> ?D) \<turnstile> ?T))\<^sup>t =
         (RA2 \<circ> RA1 \<circ> PBMH_ades)
          ((\<not> ok\<^sup><) \<or> (?B \<^sub>wf)\<^sup>f \<or>
            (?B \<^sub>wf)\<^sup>t)"
      using RA_design_wf_ok_true[of ?B]
      by (simp only: design_norm)
    have absorb:
        "RA (A ((\<not> ?D) \<turnstile> ?T)) = RA ((\<not> ?D) \<turnstile> ?T)"
      using chaos_absorb[of x]
      by (simp only: comp_apply)
    show ?thesis
      using false_component true_component
      by (simp only: comp_apply absorb B_wf B_false B_true
          PBMH_ades_disj PBMH_ades_not_ok_expr
          prefix_diverge_post_PBMH prefix_offer_post_PBMH)
  qed
  have branch_false:
      "(((RA ((\<not> prefix_diverge_post x) \<turnstile>
          (prefix_offer_post x \<or> prefix_diverge_post x)))
          \<^sub>wf)\<^sup>f) =
        RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post x))" for x :: 'e
    using branch_components[of x] by (rule conjunct1)
  have branch_true:
      "(((RA ((\<not> prefix_diverge_post x) \<turnstile>
          (prefix_offer_post x \<or> prefix_diverge_post x)))
          \<^sub>wf)\<^sup>t) =
        RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post x \<or>
          (prefix_offer_post x \<or> prefix_diverge_post x)))" for x :: 'e
    using branch_components[of x] by (rule conjunct2)
  have failure_conj:
      "(RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post a)) \<and>
        RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post b))) =
       RA2 (RA1 ((\<not> ok\<^sup><) \<or>
        (prefix_diverge_post a \<and> prefix_diverge_post b)))"
    apply (simp only: RA2_conj[symmetric] RA1_conj[symmetric])
    apply (rule arg_cong[where f=RA2])
    apply (rule arg_cong[where f=RA1])
    by pred_auto
  have post_conj:
      "(RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post a \<or>
          (prefix_offer_post a \<or> prefix_diverge_post a))) \<and>
        RA2 (RA1 ((\<not> ok\<^sup><) \<or> prefix_diverge_post b \<or>
          (prefix_offer_post b \<or> prefix_diverge_post b)))) =
       RA2 (RA1 ((\<not> ok\<^sup><) \<or>
        (prefix_diverge_post a \<and> prefix_diverge_post b) \<or>
        ((prefix_offer_post a \<or> prefix_diverge_post a) \<and>
         (prefix_offer_post b \<or> prefix_diverge_post b))))"
    apply (simp only: RA2_conj[symmetric] RA1_conj[symmetric])
    apply (rule arg_cong[where f=RA2])
    apply (rule arg_cong[where f=RA1])
    by pred_auto
  have prepend_inj:
      "inj (rad_state.tr\<^sub>v_update ((+) (xs :: 'e list)) ::
        ('e list, 'e) rad_state \<Rightarrow> ('e list, 'e) rad_state)" for xs
    apply (rule injI)
    subgoal for x y
      by (cases x; cases y; simp;
          rule left_cancel_monoid_class.add_left_imp_eq)
    done
  have prepend_eq:
      "rad_state.tr\<^sub>v_update ((+) (xs :: 'e list)) x =
       rad_state.tr\<^sub>v_update ((+) xs) y \<longleftrightarrow> x = y"
      for xs and x y :: "('e list, 'e) rad_state"
    by (rule inj_eq[OF prepend_inj])
  note prepend_eq[simp]
  have singleton_normalise:
      "(\<lambda>x. RA2 (RA1
          ((\<not> ok\<^sup><) \<or>
           (prefix_diverge_post a \<and> prefix_diverge_post b))) x \<or>
        (\<in>\<^sub>a\<^sub>c(RA2 (RA1
          ((\<not> ok\<^sup><) \<or>
           (prefix_diverge_post a \<and> prefix_diverge_post b) \<or>
           ((prefix_offer_post a \<or> prefix_diverge_post a) \<and>
            (prefix_offer_post b \<or> prefix_diverge_post b)))))) x) =
       RA2 (RA1
        ((\<not> ok\<^sup><) \<or>
         (prefix_diverge_post a \<and> prefix_diverge_post b) \<or>
         prefix_offer_pair_post a b))"
    apply (simp add: ades_singleton_choice_def RA2_def RA1_def
        prefix_diverge_post_def prefix_offer_post_def
        prefix_offer_pair_post_def fun_eq_iff Let_def
        rad_normalise_choices_as_prepend rad_zero_trace_def
        rad_trace_extensions_def lens_defs des_vars.ok_def astate.s_def
        des_vars.more\<^sub>L_def SEXP_def conj_pred_def disj_pred_def
        not_pred_def)
    apply (intro allI)
    subgoal for aa ba
      apply (cases "astate.s\<^sub>v (des_vars.more aa)")
      apply (cases "des_vars.more aa")
      apply (cases aa)
      apply (cases "des_vars.more ba")
      apply (cases ba)
      apply (simp add: subst_app_def subst_ext_def ns_alpha_def
          lens_comp_def fst_lens_def des_vars.ok_def SEXP_def)
      apply auto
      done
    done
  have pair_p2ac:
      "prefix_offer_pair_post a b = p2ac \<lceil>(\<lambda> (s, y).
        rad_state.wait\<^sub>v y \<and>
        rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s \<and>
        a \<notin> rad_state.ref\<^sub>v y \<and>
        b \<notin> rad_state.ref\<^sub>v y)\<rceil>\<^sub>D"
    by (simp add: prefix_offer_pair_post_def p2ac_def fun_eq_iff
        subst_app_def subst_ext_def SEXP_def lens_defs
        des_vars.more\<^sub>L_def; pred_auto; blast)
  have pair_PBMH:
      "PBMH_ades (prefix_offer_pair_post a b) =
        prefix_offer_pair_post a b"
    by (simp only: pair_p2ac PBMH_ades_p2ac)
  have pair_unrest: "$ok\<^sup>> \<sharp> prefix_offer_pair_post a b"
    apply (simp add: unrest_lens prefix_offer_pair_post_def)
    apply (simp add: subst_app_def subst_upd_def subst_id_def
        SEXP_def lens_defs alpha_defs)
    done
  let ?F = "prefix_diverge_post a \<and> prefix_diverge_post b"
  let ?T = "(prefix_offer_post a \<or> prefix_diverge_post a) \<and>
      (prefix_offer_post b \<or> prefix_diverge_post b)"
  let ?R = "prefix_offer_pair_post a b"
  let ?U = "RA2 (RA1 ((\<not> ok\<^sup><) \<or> ?F))"
  let ?V = "RA2 (RA1 ((\<not> ok\<^sup><) \<or> ?F \<or> ?T))"
  let ?S = "\<in>\<^sub>a\<^sub>c(?V)"
  let ?W = "RA2 (RA1 ((\<not> ok\<^sup><) \<or> ?F \<or> ?R))"
  have singleton_normalise': "(\<lambda>x. ?U x \<or> ?S x) = ?W"
    using singleton_normalise .
  have post_absorb:
      "(?U \<or> (?S \<and> ok\<^sup>>)) = (?U \<or> (?W \<and> ok\<^sup>>))"
  proof (rule ext)
    fix x
    have pointwise: "(?U x \<or> ?S x) = ?W x"
      by (rule fun_cong[OF singleton_normalise'])
    show "(?U \<or> (?S \<and> ok\<^sup>>)) x =
        (?U \<or> (?W \<and> ok\<^sup>>)) x"
      using pointwise
      by (simp only: conj_pred_def disj_pred_def; blast)
  qed
  have design_eq: "((\<not> ?U) \<turnstile> ?S) = ((\<not> ?U) \<turnstile> ?W)"
    by (simp only: design_as_disj pred_ba.double_compl
        pred_ba.sup_assoc post_absorb)
  have left_H: "((\<not> ?U) \<turnstile> ?S) is \<^bold>H"
    by (rule design_is_H1_H2; simp add: unrest)
  have right_H: "((\<not> ?F) \<turnstile> ?R) is \<^bold>H"
    by (rule design_is_H1_H2; simp add: unrest pair_unrest)
  have F_PBMH: "?F is PBMH_ades"
    by (rule PBMH_ades_conj_closure; simp add: Healthy_def')
  have X_PBMH: "PBMH_ades ((\<not> ok\<^sup><) \<or> ?F) =
      ((\<not> ok\<^sup><) \<or> ?F)"
    using F_PBMH by (simp add: PBMH_ades_disj Healthy_def')
  have Z_PBMH: "PBMH_ades ((\<not> ok\<^sup><) \<or> ?F \<or> ?R) =
      ((\<not> ok\<^sup><) \<or> ?F \<or> ?R)"
    using F_PBMH pair_PBMH
    by (simp add: PBMH_ades_disj Healthy_def')
  have outer_normalise:
      "(RA \<circ> A) ((\<not> ?U) \<turnstile> ?S) =
       (RA \<circ> A) ((\<not> ?F) \<turnstile> ?R)"
  proof -
    have "(RA \<circ> A) ((\<not> ?U) \<turnstile> ?S) =
        RA (PBMH_ades ((\<not> ?U) \<turnstile> ?S))"
      by (simp only: comp_apply RA_A'[OF left_H])
    also have "... = RA (PBMH_ades ((\<not> ?U) \<turnstile> ?W))"
      by (simp only: design_eq)
    also have "... = RA (PBMH_ades ((\<not> ?F) \<turnstile> ?R))"
      using RA_design_PBMH_normalise[of ?F ?R]
      by (simp only: X_PBMH Z_PBMH)
    also have "... = (RA \<circ> A) ((\<not> ?F) \<turnstile> ?R)"
      by (simp only: comp_apply RA_A'[OF right_H])
    finally show ?thesis .
  qed
  show ?thesis
    apply (subst extchoice_RAD_Stop)
     apply (rule RAD_angelic_closure;
         rule Prefix_RAD_closure;
         rule Chaos_RAD_is_RAD)
    apply (simp only: RAD_angelic_choice rad_wait_false_conj subst_pred
        Prefix_Chaos_RAD_RA branch_false branch_true)
    apply (simp only: failure_conj post_conj)
    apply (subst ades_singleton_choice_def[symmetric])
    by (rule outer_normalise)
qed

end
