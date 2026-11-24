section \<open>Angelic Process Sequential Composition and Prefixing\<close>

theory utp_ap_seq
  imports utp_ap_ops
begin

subsection \<open>Sequential Composition\<close>

(* ok-in substitution commutes with every operator appearing in the
   sequential composition normal form; collected so the push proofs
   cite one name.  Extend here when a new operator joins the form. *)
lemmas ok_in_subst_laws =
  RA1_ok_in_subst RA2_ok_in_subst aseq_ades_ok_in_subst
  rad_wait_cond_ok_in_subst

(* Thesis Theorem T.H.3.2. *)
lemma AP_wait_design_seq:
  assumes "$ok\<^sup>> \<sharp> F" "$ok\<^sup>> \<sharp> T"
    "$ok\<^sup>< \<sharp> G" "$ok\<^sup>< \<sharp> U"
    and "F is PBMH_ades" "T is PBMH_ades"
  shows
    "(((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> F)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T)) ;;\<^sub>A\<^sub>D
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> U))) =
     RA3AP (((\<not> (F ;;\<^sub>A\<^sub>R true)) \<and>
              (\<not> (T ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> G)))) \<turnstile>
             (T ;;\<^sub>A\<^sub>R
               (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                ((\<not> G) \<longrightarrow> U))))"
proof -
  have not_true:
      "(\<not> (true :: ('t::trace, 'e) angelic_process)) = false"
    by pred_auto
  have not_false:
      "(\<not> (false :: ('t::trace, 'e) angelic_process)) = true"
    by pred_auto
  have wait_conj: "\<And>A B C D.
      ((A \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> B) \<and>
       (C \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> D)) =
      ((A \<and> C) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (B \<and> D))"
    by (simp add: expr_if_def fun_eq_iff; pred_auto)
  have seq_form:
    "(((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> F)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T)) ;;\<^sub>A\<^sub>D
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> U))) =
     (((\<not> ((\<not> (true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> F))) ;;\<^sub>A\<^sub>R true)) \<and>
       (\<not> ((ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T) ;;\<^sub>A\<^sub>R
          (\<not> (true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)))))) \<turnstile>
      ((ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T) ;;\<^sub>A\<^sub>R
       ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)) \<longrightarrow>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> U))))"
    apply (rule ades_design_seq)
         apply (simp_all add: unrest assms(1-4))
     apply (simp only: rad_wait_cond_not not_true pred_ba.double_compl)
     apply (rule rad_wait_cond_PBMH_ades_closure[OF false_PBMH_ades assms(5)])
    apply (rule rad_wait_cond_PBMH_ades_closure
        [OF ades_state_choice_is_PBMH_ades assms(6)])
    done
  show ?thesis
    unfolding seq_form
    apply (simp only: rad_wait_cond_not not_true not_false
        pred_ba.double_compl
        aseq_ades_wait_cond_distrib aseq_ades_false_left
        aseq_ades_state_choice_left rad_wait_cond_left_absorb
        rad_wait_cond_impl pred_impl_laws(1)
        wait_conj pred_ba.inf_top_left RA3AP_design)
    apply (simp only: rad_wait_cond_false)
    done
qed

(* Normalise the right operand's initial ok observation once. *)
lemma AP_wait_design_seq_gen:
  assumes "$ok\<^sup>> \<sharp> F" "$ok\<^sup>> \<sharp> T"
    and "F is PBMH_ades" "T is PBMH_ades"
  shows
    "(((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> F)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T)) ;;\<^sub>A\<^sub>D
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> U))) =
     RA3AP (((\<not> (F ;;\<^sub>A\<^sub>R true)) \<and>
              (\<not> (T ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> G)))) \<turnstile>
             (T ;;\<^sub>A\<^sub>R
               (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                ((\<not> G) \<longrightarrow> U))))"
proof -
  let ?G = "G\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?U = "U\<lbrakk>True/ok\<^sup><\<rbrakk>"
  have right_normal:
    "((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> U)) =
     ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> ?G)) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> ?U))"
    by (rule design_ok_in_cong)
      (simp_all add: usubst rad_wait_cond_ok_in_subst)
  have result_normal:
    "(((\<not> (F ;;\<^sub>A\<^sub>R true)) \<and>
        (\<not> (T ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> ?G)))) \<turnstile>
       (T ;;\<^sub>A\<^sub>R
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          ((\<not> ?G) \<longrightarrow> ?U)))) =
     (((\<not> (F ;;\<^sub>A\<^sub>R true)) \<and>
        (\<not> (T ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> G)))) \<turnstile>
       (T ;;\<^sub>A\<^sub>R
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          ((\<not> G) \<longrightarrow> U))))"
    by (rule design_ok_in_cong)
      (simp_all add: usubst ok_in_subst_laws)
  show ?thesis
    unfolding right_normal
    by (subst AP_wait_design_seq[OF assms(1,2) _ _ assms(3,4)];
        simp add: unrest result_normal)
qed

(* Thesis Theorem T.H.3.3. *)
lemma AP_seq_design_PBMH:
  "(AP P ;;\<^sub>A\<^sub>D AP Q) =
   AP (((\<not> (PBMH_ades ((P \<^sub>f)\<^sup>f) ;;\<^sub>A\<^sub>R true)) \<and>
        (\<not> ((RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>R
          ((\<not> rad_wait_lens\<^sup><) \<and>
           (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f))))) \<turnstile>
       ((RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>R
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         RA2 ((\<not> PBMH_ades ((Q \<^sub>f)\<^sup>f)) \<longrightarrow>
              (RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t)))))"
proof -
  let ?Pf = "PBMH_ades ((P \<^sub>f)\<^sup>f)"
  let ?Pt = "RA1 (PBMH_ades ((P \<^sub>f)\<^sup>t))"
  let ?Qf = "PBMH_ades ((Q \<^sub>f)\<^sup>f)"
  let ?Qt = "RA1 (PBMH_ades ((Q \<^sub>f)\<^sup>t))"
  let ?pre = "((\<not> (?Pf ;;\<^sub>A\<^sub>R true)) \<and>
    (\<not> (?Pt ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf))))"
  let ?post = "(?Pt ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 ((\<not> ?Qf) \<longrightarrow> ?Qt)))"
  let ?N = "(?pre \<turnstile> ?post)"
  have seq_raw:
    "(AP P ;;\<^sub>A\<^sub>D AP Q) =
     RA3AP (((\<not> (RA2 ?Pf ;;\<^sub>A\<^sub>R true)) \<and>
              (\<not> (RA2 ?Pt ;;\<^sub>A\<^sub>R
                ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf)))) \<turnstile>
             (RA2 ?Pt ;;\<^sub>A\<^sub>R
               (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                ((\<not> RA2 ?Qf) \<longrightarrow> RA2 ?Qt))))"
    unfolding AP_wait_cond_design comp_apply
    apply (rule AP_wait_design_seq_gen)
       apply (simp_all add: unrest)
     apply (intro RA2_PBMH_ades_closure
        Healthy_Idempotent[OF PBMH_ades_Idempotent])
    apply (intro RA2_PBMH_ades_closure RA1_PBMH_ades_closure
        Healthy_Idempotent[OF PBMH_ades_Idempotent])
    done
  have wait_fixed:
    "RA2 ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf) =
     ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf)"
    by (simp only: RA2_not_wait_conj RA2_idem)
  have seq_RA3AP_RA2:
    "(AP P ;;\<^sub>A\<^sub>D AP Q) = RA3AP (RA2 ?N)"
    unfolding seq_raw
    by (simp only: RA2_design_distrib RA2_conj RA2_not
        RA2_aseq_fixed RA2_aseq_fixed[OF wait_fixed]
        RA2_true RA2_idem RA2_wait_cond RA2_state_choice RA2_impl)
  have Pf_PBMH: "?Pf is PBMH_ades"
    and Pt_PBMH: "?Pt is PBMH_ades"
    and Qf_PBMH: "?Qf is PBMH_ades"
    and Qt_PBMH: "?Qt is PBMH_ades"
    by (simp_all add: Healthy_def' PBMH_ades_ok_in_subst
        PBMH_ades_idem
        PBMH_ades_RA1_absorb[simplified comp_apply])
  have N_PBMH: "?N is PBMH_ades"
  proof -
    have bad_PBMH:
      "((?Pf ;;\<^sub>A\<^sub>R true) \<or>
        (?Pt ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf)))
       is PBMH_ades"
      unfolding rad_wait_cond_false[symmetric]
      by (intro PBMH_ades_disj_closure aseq_ades_PBMH_ades_closure
          rad_wait_cond_PBMH_ades_closure RA2_PBMH_ades_closure
          false_PBMH_ades true_PBMH_ades Pf_PBMH Pt_PBMH Qf_PBMH)
    have post_PBMH: "?post is PBMH_ades"
      unfolding impl_neg_disj
      apply (simp only: pred_ba.double_compl)
      by (intro aseq_ades_PBMH_ades_closure
          rad_wait_cond_PBMH_ades_closure PBMH_ades_disj_closure
          RA2_PBMH_ades_closure ades_state_choice_is_PBMH_ades
          Pt_PBMH Qf_PBMH Qt_PBMH)
    have pre_as_neg: "?pre =
        (\<not> ((?Pf ;;\<^sub>A\<^sub>R true) \<or>
          (?Pt ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf))))"
      by (simp only: pred_ba.compl_sup)
    show ?thesis
      unfolding pre_as_neg
      by (rule PBMH_ades_design_closure[OF bad_PBMH post_PBMH])
  qed
  have seq_nonempty:
    "(ac_non_empty \<and>
      ((\<not> (T ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> G))) \<and>
       (T ;;\<^sub>A\<^sub>R
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (G \<or> RA1 U))))) =
     ((\<not> (T ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> G))) \<and>
      (T ;;\<^sub>A\<^sub>R
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (G \<or> RA1 U))))"
    for T G U
  proof -
    \<comment> \<open>On an empty choice set the state choice and the RA1 branch
        vanish, so the postcondition's continuation collapses to the
        negated continuation of the precondition.\<close>
    have cont_agree:
      "((\<not> ac_non_empty) \<and>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         (G \<or> RA1 U))) =
       ((\<not> ac_non_empty) \<and> ((\<not> rad_wait_lens\<^sup><) \<and> G))"
      by (simp only: rad_wait_cond_conj_distrib
          neg_conj_absorb_false[OF ades_state_choice_ac_non_empty_absorb]
          pred_ba.inf_sup_distrib1
          neg_conj_absorb_false[OF RA1_ac_non_empty_conj_absorb]
          pred_ba.sup_bot_right rad_wait_cond_false
          pred_ba.inf_left_commute)
    show ?thesis
      by (rule conj_absorb_by_agree[OF
            aseq_ades_ac_empty_cong[OF cont_agree]])
  qed
  have Qt_RA1_form:
    "RA2 ?Qt = RA1 (RA2 (PBMH_ades ((Q \<^sub>f)\<^sup>t)))"
    by (simp only: RA1_RA2_commute'[symmetric])
  have absorb0:
    "(ac_non_empty \<and> (?pre \<and> ?post)) = (?pre \<and> ?post)"
    apply (simp only: impl_neg_disj pred_ba.double_compl RA2_disj
        Qt_RA1_form)
    by (rule conj_extra_absorb[OF seq_nonempty])
  have AP_N: "AP ?N = RA3AP (RA2 ?N)"
    by (rule AP_design_RA3AP_RA2[OF _ _ N_PBMH
        RA1_true_absorb_lift[OF absorb0]]; simp add: unrest)
  have "(AP P ;;\<^sub>A\<^sub>D AP Q) = RA3AP (RA2 ?N)"
    by (rule seq_RA3AP_RA2)
  also have "... = AP ?N"
    by (rule AP_N[symmetric])
  finally show ?thesis
    by (simp only: comp_apply)
qed

(* ok-in substitution of the lifted components of a true-precondition
   design: the failure component collapses to false and the success
   component to the postcondition.  Shared by the two operands in
   AP_true_design_seq. *)
lemma true_design_components_ok_in_subst:
  assumes "(P \<^sub>f) = P" "PBMH_ades P = P"
    and "P\<lbrakk>True/ok\<^sup>>\<rbrakk> = P"
  shows "(PBMH_ades (((true \<turnstile> P) \<^sub>f)\<^sup>f))
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    and "((RA1 \<circ> PBMH_ades) (((true \<turnstile> P) \<^sub>f)\<^sup>t))
      \<lbrakk>True/ok\<^sup><\<rbrakk> =
      (RA1 P)\<lbrakk>True/ok\<^sup><\<rbrakk>"
proof -
  have wf: "((true \<turnstile> P) \<^sub>f) = (true \<turnstile> P)"
    by (simp only: rad_wait_false_design rad_wait_false_true assms(1))
  have raw_components:
    "(true \<turnstile> P)\<^sup>f = (\<not> ok\<^sup><)"
    "(true \<turnstile> P)\<^sup>t = ((\<not> ok\<^sup><) \<or> P\<lbrakk>True/ok\<^sup>>\<rbrakk>)"
    by pred_auto+
  have failure:
    "((true \<turnstile> P)\<^sup>f)\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: raw_components(1) subst_pred; pred_auto)
  have success:
    "((true \<turnstile> P)\<^sup>t)\<lbrakk>True/ok\<^sup><\<rbrakk> =
      P\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: raw_components(2) subst_pred assms(3); pred_auto)
  show "(PBMH_ades (((true \<turnstile> P) \<^sub>f)\<^sup>f))
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: wf PBMH_ades_ok_in_subst[THEN sym] failure
        PBMH_ades_false)
  show "((RA1 \<circ> PBMH_ades) (((true \<turnstile> P) \<^sub>f)\<^sup>t))
      \<lbrakk>True/ok\<^sup><\<rbrakk> =
      (RA1 P)\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: wf comp_apply RA1_ok_in_subst
        PBMH_ades_ok_in_subst[THEN sym] success
        PBMH_ades_ok_in_subst assms(2))
qed

(* Non-divergent true-precondition instance of the generic sequential
   composition normal form. *)
lemma AP_true_design_seq:
  assumes "(P \<^sub>f) = P" "PBMH_ades P = P"
      "P\<lbrakk>True/ok\<^sup>>\<rbrakk> = P"
    and "(Q \<^sub>f) = Q" "PBMH_ades Q = Q"
      "Q\<lbrakk>True/ok\<^sup>>\<rbrakk> = Q"
  shows "(AP (true \<turnstile> P) ;;\<^sub>A\<^sub>D AP (true \<turnstile> Q)) =
    AP (true \<turnstile>
      (RA1 P ;;\<^sub>A\<^sub>R
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        RA2 (RA1 Q))))"
proof -
  let ?DP = "(true \<turnstile> P)" and ?DQ = "(true \<turnstile> Q)"
  let ?PF = "PBMH_ades ((?DP \<^sub>f)\<^sup>f)"
  let ?PT = "(RA1 \<circ> PBMH_ades) ((?DP \<^sub>f)\<^sup>t)"
  let ?QF = "PBMH_ades ((?DQ \<^sub>f)\<^sup>f)"
  let ?QT = "(RA1 \<circ> PBMH_ades) ((?DQ \<^sub>f)\<^sup>t)"
  let ?pre = "((\<not> (?PF ;;\<^sub>A\<^sub>R true)) \<and>
    (\<not> (?PT ;;\<^sub>A\<^sub>R
      ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?QF))))"
  let ?post = "(?PT ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 ((\<not> ?QF) \<longrightarrow> ?QT)))"
  let ?postND = "(RA1 P ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 Q)))"
  note P_push = true_design_components_ok_in_subst[OF assms(1-3)]
  note Q_push = true_design_components_ok_in_subst[OF assms(4-6)]
  have initial_failure_false:
    "(?PF ;;\<^sub>A\<^sub>R true)\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: ok_in_subst_laws P_push(1)
        aseq_ades_false_left)
  have Qguard_false:
    "(((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?QF))
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: subst_pred ok_in_subst_laws Q_push(1)
        RA2_false pred_ba.inf_bot_right)
  have handover_failure_false:
    "(?PT ;;\<^sub>A\<^sub>R
      ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?QF))
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: ok_in_subst_laws P_push(2)
        Qguard_false RA1_aseq_false)
  have pre_push:
    "?pre\<lbrakk>True/ok\<^sup><\<rbrakk> =
      true\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: subst_pred initial_failure_false
        handover_failure_false pred_ba.compl_bot_eq
        pred_ba.inf_top_left)
  have continuation_push:
    "(RA2 ((\<not> ?QF) \<longrightarrow> ?QT))
      \<lbrakk>True/ok\<^sup><\<rbrakk> =
     (RA2 (RA1 Q))\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: ok_in_subst_laws subst_pred Q_push
        pred_ba.compl_bot_eq pred_impl_laws(1))
  have post_push:
    "?post\<lbrakk>True/ok\<^sup><\<rbrakk> =
      ?postND\<lbrakk>True/ok\<^sup><\<rbrakk>"
    \<comment> \<open>Not \<open>ok_in_subst_laws\<close>: pushing into RA2 here would
        outrun the \<open>continuation_push\<close> pattern.\<close>
    by (simp only: aseq_ades_ok_in_subst rad_wait_cond_ok_in_subst
        P_push(2) continuation_push)
  have design_eq: "(?pre \<turnstile> ?post) = (true \<turnstile> ?postND)"
    by (rule design_ok_in_cong[OF pre_push post_push])
  have "(AP ?DP ;;\<^sub>A\<^sub>D AP ?DQ) = AP (?pre \<turnstile> ?post)"
    by (simp only: AP_seq_design_PBMH comp_apply)
  also have "... = AP (true \<turnstile> ?postND)"
    by (simp only: design_eq)
  finally show ?thesis .
qed

(* Chaos instance of the sequential composition normal form, cf.
   Thesis Lemma L.H.3.6: the divergent continuation collapses the
   handover guard to the non-waiting condition and the continuation
   to true. *)
lemma AP_true_design_seq_Chaos:
  fixes P :: "('t::trace, 'e) angelic_process"
  assumes "(P \<^sub>f) = P" "PBMH_ades P = P"
    and "P\<lbrakk>True/ok\<^sup>>\<rbrakk> = P"
  shows "(AP (true \<turnstile> P) ;;\<^sub>A\<^sub>D Chaos\<^sub>A\<^sub>P) =
    AP ((\<not> (RA1 P ;;\<^sub>A\<^sub>R (\<not> rad_wait_lens\<^sup><))) \<turnstile>
        (RA1 P ;;\<^sub>A\<^sub>R
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> true)))"
proof -
  note P_push = true_design_components_ok_in_subst[OF assms]
  have Q_comp:
      "((true \<^sub>f)\<^sup>f)\<lbrakk>True/ok\<^sup><\<rbrakk> = true"
      "((true \<^sub>f)\<^sup>t)\<lbrakk>True/ok\<^sup><\<rbrakk> = true"
    by pred_auto+
  have Q_push:
      "(PBMH_ades ((true \<^sub>f)\<^sup>f))\<lbrakk>True/ok\<^sup><\<rbrakk> = true"
      "(RA1 (PBMH_ades ((true \<^sub>f)\<^sup>t)))\<lbrakk>True/ok\<^sup><\<rbrakk> =
        RA1 true"
    by (simp_all only: RA1_ok_in_subst
        PBMH_ades_ok_in_subst[THEN sym] Q_comp PBMH_ades_true)
  show ?thesis
    apply (simp only: Chaos_AP_def design_false_pre
        AP_seq_design_PBMH comp_apply)
    apply (rule arg_cong[where f=AP])
    apply (rule design_ok_in_cong)
    apply (simp_all only: subst_pred aseq_ades_ok_in_subst
        rad_wait_cond_ok_in_subst RA2_ok_in_subst P_push(1)
        P_push(2)[simplified comp_apply] Q_push
        aseq_ades_false_left RA2_true pred_ba.inf_top_right
        pred_ba.compl_bot_eq pred_ba.inf_top_left pred_ba.compl_top_eq
        pred_impl_laws comp_apply)
    done
qed
(* Paper Theorem 59 / Thesis Theorem T.6.4.18. *)
theorem AP_seq_design:
  assumes "P is AP" "Q is AP"
  shows "(P ;;\<^sub>A\<^sub>D Q) = AP (
  \<comment> \<open>P's initial, non-waiting precondition holds\<close>
  ((\<not> (((P \<^sub>f)\<^sup>f) ;;\<^sub>A\<^sub>R true)) \<and>
  \<comment> \<open>a successful non-waiting handover from P satisfies Q's precondition\<close>
  (\<not> (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ((Q \<^sub>f)\<^sup>f))))) \<turnstile>
  \<comment> \<open>wait is true: retain P's waiting state through s \<in> ac'\<close>
  (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>R (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
  \<comment> \<open>wait is false: Q's precondition implies Q's postcondition\<close>
  RA2 ((\<not> (Q \<^sub>f)\<^sup>f) \<longrightarrow> RA1 ((Q \<^sub>f)\<^sup>t)))))"
  using AP_seq_design_PBMH[of P Q]
  by (simp only: comp_apply Healthy_if[OF assms(1)]
      Healthy_if[OF assms(2)]
      Healthy_if[OF AP_wf_ok_false_PBMH_ades[OF assms(1)]]
      Healthy_if[OF AP_wf_ok_true_PBMH_ades[OF assms(1)]]
      Healthy_if[OF AP_wf_ok_false_PBMH_ades[OF assms(2)]]
      Healthy_if[OF AP_wf_ok_true_PBMH_ades[OF assms(2)]])

lemma AP_seq_closure [closure]:
  assumes "P is AP" "Q is AP"
  shows "(P ;;\<^sub>A\<^sub>D Q) is AP"
  by (subst AP_seq_design[OF assms]) (rule AP_healthy)

(* Paper Theorem 60 / Thesis Theorem T.6.4.19. *)
theorem RA1_H1_seq_refine:
  assumes "P is RAD" "Q is RAD"
  shows "RA1 (H1 P ;;\<^sub>A\<^sub>D H1 Q) \<sqsubseteq> (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
proof -
  have HP_refine: "H1 P \<sqsubseteq> P"
    and HQ_refine: "H1 Q \<sqsubseteq> Q"
    using RA1_refine[OF H1_RAD_is_PBMH_ades[OF assms(1)]]
      RA1_refine[OF H1_RAD_is_PBMH_ades[OF assms(2)]]
    by (simp_all only:
        RA1_H1_RAD_healthy[OF assms(1), simplified comp_apply]
        RA1_H1_RAD_healthy[OF assms(2), simplified comp_apply])
  have seq_refine:
    "(H1 P ;;\<^sub>A\<^sub>D H1 Q) \<sqsubseteq> (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
    by (rule angelic_design_seq_mono[
          OF H1_RAD_is_PBMH_ades[OF assms(1)] HP_refine HQ_refine])
  have seq_RA1:
    "RA1 (P ;;\<^sub>R\<^sub>A\<^sub>D Q) = (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
    by (simp only: RAD_seq_design[OF assms] comp_apply
        RA_as_RA1_RA3_RA2 RA1_idem)
  show ?thesis
    using RA1_mono[OF seq_refine]
    by (simp only: seq_RA1)
qed

(* Paper Theorem 61 / Thesis Theorem T.6.4.20. *)
theorem H1_RA1_seq_refine:
  assumes "P is AP" "Q is AP"
  shows "(P ;;\<^sub>A\<^sub>D Q) \<sqsubseteq> H1 (RA1 P ;;\<^sub>R\<^sub>A\<^sub>D RA1 Q)"
proof -
  have P_refine: "P \<sqsubseteq> H1 (RA1 P)"
    and Q_refine: "Q \<sqsubseteq> H1 (RA1 Q)"
    using H1_RA1_AP_refine[of P] H1_RA1_AP_refine[of Q]
    by (simp_all only: comp_apply Healthy_if[OF assms(1)]
        Healthy_if[OF assms(2)])
  have linked_seq_refine:
    "(P ;;\<^sub>A\<^sub>D Q) \<sqsubseteq>
      (H1 (RA1 P) ;;\<^sub>A\<^sub>D H1 (RA1 Q))"
    by (rule angelic_design_seq_mono[
          OF AP_is_PBMH_ades[OF assms(1)] P_refine Q_refine])
  have RA1_P_RAD: "RA1 P is RAD"
    and RA1_Q_RAD: "RA1 Q is RAD"
    using RA1_AP_RAD[of P] RA1_AP_RAD[of Q]
    by (simp_all only: comp_apply Healthy_if[OF assms(1)]
        Healthy_if[OF assms(2)] RAD_healthy)
  have seq_RA1_refine:
    "RA1 (P ;;\<^sub>A\<^sub>D Q) \<sqsubseteq>
      (RA1 P ;;\<^sub>R\<^sub>A\<^sub>D RA1 Q)"
    by (rule ref_by_trans[
          OF RA1_mono[OF linked_seq_refine]
          RA1_H1_seq_refine[OF RA1_P_RAD RA1_Q_RAD]])
  have seq_refine:
    "(P ;;\<^sub>A\<^sub>D Q) \<sqsubseteq>
      H1 (RA1 (P ;;\<^sub>A\<^sub>D Q))"
    using H1_RA1_AP_refine[of "P ;;\<^sub>A\<^sub>D Q"]
    by (simp only: comp_apply Healthy_if[OF AP_seq_closure[OF assms]])
  show ?thesis
    by (rule ref_by_trans[
          OF seq_refine H1_monotone[OF seq_RA1_refine]])
qed

(* Shared successful-continuation facts for the RAD and AP sequence laws. *)
lemma AP_true_seq_post_facts:
  assumes "(P \<^sub>f)\<^sup>t is PBMH_ades"
    "(Q \<^sub>f)\<^sup>t is PBMH_ades"
  defines "C \<equiv> (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 ((Q \<^sub>f)\<^sup>t))))"
  shows "(C \<^sub>f) = C"
    and "C is PBMH_ades"
    and "$ok\<^sup>> \<sharp> C"
    and "C\<lbrakk>True/ok\<^sup>>\<rbrakk> = C"
proof -
  show "(C \<^sub>f) = C"
    by (simp only: C_def rad_wait_false_aseq_ades
        rad_wait_false_RA1_commute rad_wait_false_ok_true rad_wait_false_idem)
  show "C is PBMH_ades"
    unfolding C_def
    by (intro aseq_ades_PBMH_ades_closure
        RA1_PBMH_ades_closure rad_wait_cond_PBMH_ades_closure
        ades_state_choice_is_PBMH_ades RA2_PBMH_ades_closure assms)
  show "$ok\<^sup>> \<sharp> C"
    unfolding C_def by unrest
  then show "C\<lbrakk>True/ok\<^sup>>\<rbrakk> = C"
    by (simp add: unrest usubst)
qed

(* Paper Theorem 62 / Thesis Theorem T.6.4.21. *)
theorem RA1_H1_seq:
  assumes "P is RAD" "Q is RAD" "P is NDRAD" "Q is NDRAD"
  shows "RA1 (H1 P ;;\<^sub>A\<^sub>D H1 Q) = (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
proof -
  let ?Pt = "(P \<^sub>f)\<^sup>t" and ?Qt = "(Q \<^sub>f)\<^sup>t"
  let ?post = "(RA1 ?Pt ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ?Qt)))"
  note Pt_facts = RAD_wf_ok_true_facts[OF assms(1)]
  note Qt_facts = RAD_wf_ok_true_facts[OF assms(2)]
  note post_facts = AP_true_seq_post_facts[OF
    RAD_wf_ok_true_PBMH[OF assms(1)]
    RAD_wf_ok_true_PBMH[OF assms(2)]]
  have linked_seq:
    "(H1 P ;;\<^sub>A\<^sub>D H1 Q) = AP (true \<turnstile> ?post)"
    by (simp only: H1_NDRAD_AP_true_design[OF assms(1,3)]
        H1_NDRAD_AP_true_design[OF assms(2,4)]
        AP_true_design_seq[OF Pt_facts Qt_facts])
  have "RA1 (H1 P ;;\<^sub>A\<^sub>D H1 Q) = RA (true \<turnstile> ?post)"
    by (simp only: linked_seq
        RA1_AP_true_design[OF post_facts(1) Healthy_if[OF post_facts(2)] post_facts(4)])
  also have "... = (RA \<circ> A) (true \<turnstile> ?post)"
    by (rule RA_A_absorb_design_true[OF post_facts(2,3),
          symmetric])
  also have "... = (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
    by (rule NDRAD_seq_design[OF assms, symmetric])
  finally show ?thesis .
qed

subsection \<open>Prefixing\<close>

(* TODO: Generalise prefixing to arbitrary trace algebras equipped with an
   event-to-trace embedding; the current list instance maps a to [a]. *)

(* Paper Definition 57 / Thesis Definition 138. *)
definition PrefixSkip_AP :: "'e \<Rightarrow> ('e list, 'e) angelic_process" where
[pred]: "PrefixSkip_AP a = AP (true \<turnstile> prefix_post a)"

lemma PrefixSkip_AP_is_AP [closure]: "PrefixSkip_AP a is AP"
  by (simp add: PrefixSkip_AP_def AP_healthy)

lemmas PrefixSkip_AP_facts =
  rad_wait_false_prefix_post prefix_post_PBMH prefix_post_ok_out_subst

lemma PrefixSkip_AP_design:
  "PrefixSkip_AP a =
   (true \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 (prefix_post a)))"
  by (simp only: PrefixSkip_AP_def
      AP_true_design[OF PrefixSkip_AP_facts] RA2_prefix_post)

(* Paper Lemma 12 / Thesis Lemma L.6.4.4. *)
lemma H1_PrefixSkip_RAD:
  "H1 (PrefixSkip_RAD a) = PrefixSkip_AP a"
  by (simp only: PrefixSkip_RAD_RA PrefixSkip_AP_def
      H1_RA_true_design[OF PrefixSkip_AP_facts])

(* Paper Lemma 13 / Thesis Lemma L.6.4.5. *)
lemma RA1_PrefixSkip_AP:
  "RA1 (PrefixSkip_AP a) = PrefixSkip_RAD a"
  by (simp only: PrefixSkip_AP_def PrefixSkip_RAD_RA
      RA1_AP_true_design[OF PrefixSkip_AP_facts])

(* Thesis Section 6.4.8: the compound process a \<rightarrow>\<^sub>A\<^sub>P P
   abbreviates (a \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) ;;\<^sub>A\<^sub>D P; its
   general normal form is stated below. *)
definition Prefix_AP ::
  "'e \<Rightarrow> ('e list, 'e) angelic_process \<Rightarrow>
   ('e list, 'e) angelic_process"
  (infixr "\<rightarrow>\<^sub>A\<^sub>P" 80) where
[pred]: "Prefix_AP a P = (PrefixSkip_AP a ;;\<^sub>A\<^sub>D P)"

lemma Prefix_AP_closure [closure]:
  assumes "P is AP"
  shows "(a \<rightarrow>\<^sub>A\<^sub>P P) is AP"
  unfolding Prefix_AP_def
  by (rule AP_seq_closure[OF PrefixSkip_AP_is_AP assms])

(* Compound prefixing of Skip is the primitive prefix. *)
lemma Prefix_Skip_AP:
  "(a \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) = PrefixSkip_AP a"
  unfolding Prefix_AP_def PrefixSkip_AP_def Skip_AP_def
  apply (subst AP_true_design_seq[OF PrefixSkip_AP_facts Skip_AP_facts])
  by (simp only: prefix_continuation_skip)

(* Thesis Theorem T.6.4.23. *)
lemma Prefix_AP_design:
  assumes "P is AP"
  shows "(a \<rightarrow>\<^sub>A\<^sub>P P) =
    AP ((\<not> prefix_handover a ((RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f))) \<turnstile>
      prefix_continuation a ((RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)))"
proof -
  let ?D = "true \<turnstile> prefix_post a"
  let ?DF = "PBMH_ades ((?D \<^sub>f)\<^sup>f)"
  let ?DT = "(RA1 \<circ> PBMH_ades) ((?D \<^sub>f)\<^sup>t)"
  let ?F = "PBMH_ades ((P \<^sub>f)\<^sup>f)"
  let ?T = "RA1 (PBMH_ades ((P \<^sub>f)\<^sup>t))"
  let ?pre = "((\<not> (?DF ;;\<^sub>A\<^sub>R true)) \<and>
    (\<not> (?DT ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?F))))"
  let ?post = "?DT ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 ((\<not> ?F) \<longrightarrow> ?T))"
  let ?pre' = "\<not> (RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?F))"
  let ?post' = "RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 ((\<not> ?F) \<longrightarrow> ?T))"
  note D_push = true_design_components_ok_in_subst[OF PrefixSkip_AP_facts]
  have design_eq: "(?pre \<turnstile> ?post) = (?pre' \<turnstile> ?post')"
    by (rule design_ok_in_cong)
      (simp_all only: subst_pred aseq_ades_ok_in_subst
        rad_wait_cond_ok_in_subst D_push
        aseq_ades_false_left pred_ba.compl_bot_eq pred_ba.inf_top_left)
  have "(a \<rightarrow>\<^sub>A\<^sub>P P) = (AP ?D ;;\<^sub>A\<^sub>D AP P)"
    by (simp only: Prefix_AP_def PrefixSkip_AP_def Healthy_if[OF assms])
  also have "... = AP (?pre \<turnstile> ?post)"
    by (simp only: AP_seq_design_PBMH comp_apply)
  also have "... = AP (?pre' \<turnstile> ?post')"
    by (simp only: design_eq)
  also have "... = AP
      ((\<not> prefix_handover a (RA2 ?F)) \<turnstile>
       prefix_continuation a (RA2 ?T))"
    by (simp only: impl_neg_disj pred_ba.double_compl RA2_disj
        prefix_handover_aseq prefix_continuation_aseq prefix_design_failure_absorb)
  finally show ?thesis
    by (simp only: comp_apply)
qed

end
