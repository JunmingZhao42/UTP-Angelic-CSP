section \<open>Reactive Angelic Designs\<close>

theory utp_rad_designs
  imports utp_rad_healthy
begin

subsection \<open>Reactive design forms\<close>

(* A design ignores its postcondition when it has not started, so a
   not-started disjunct under RA1 is redundant. *)
lemma design_true_RA1_not_ok:
  "(true \<turnstile> RA1 ((\<not> ok\<^sup><) \<or> X)) = (true \<turnstile> RA1 X)"
proof -
  have inner:
      "((\<not> ok\<^sup><) \<or> X)\<lbrakk>True/ok\<^sup><\<rbrakk> = X\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp add: usubst usubst_eval; pred_auto)
  have "(true \<turnstile> RA1 ((\<not> ok\<^sup><) \<or> X)) =
      (true\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile>
       (RA1 ((\<not> ok\<^sup><) \<or> X))\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (rule sym, rule design_subst_ok)
  also have "... =
      (true\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile> (RA1 X)\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (simp only: RA1_ok_in_subst inner)
  also have "... = (true \<turnstile> RA1 X)"
    by (rule design_subst_ok)
  finally show ?thesis .
qed

(* H1 discards the not-started behaviour that RA1 adds to a design,
   leaving RA1 enforced on both components. *)
lemma H1_RA1_design_gen:
  "H1 (RA1 (P \<turnstile> Q)) = ((\<not> RA1 (\<not> P)) \<turnstile> RA1 Q)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto)

lemma H1_RA1_design: "H1 (RA1 (true \<turnstile> X)) = (true \<turnstile> RA1 X)"
  by (simp only: H1_RA1_design_gen pred_ba.compl_top_eq RA1_false
      pred_ba.compl_bot_eq)

lemma rad_wait_false_design_is_H [closure]:
  "((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t) is \<^bold>H"
  by (rule design_is_H1_H2; pred_auto)

lemma II_Rac_design:
  "II_Rac = RA1 (true \<turnstile> ades_state_choice)"
  by (simp add: II_Rac_def RA1_def design_def ades_state_choice_def
      fun_eq_iff Let_def SEXP_def lens_defs des_vars.ok_def;
      pred_auto; blast intro: rad_trace_extensions_refl)

lemma design_wait_cond:
  "((P \<turnstile> Q) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (R \<turnstile> S)) =
   ((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> R) \<turnstile>
    (Q \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> S))"
  by (simp add: design_def expr_if_def fun_eq_iff; pred_auto)

(* Thesis Lemma L.G.4.1: under RA1, RA3 turns a design into wait
   conditionals over its components. *)
lemma RA1_RA3_design:
  "RA1 (RA3 (P \<turnstile> Q)) =
   RA1 ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
proof -
  have "RA1 (RA3 (P \<turnstile> Q)) =
    (RA1 II_Rac \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 (P \<turnstile> Q))"
    by (simp only: RA3_def RA1_wait_cond)
  also have "... =
    (RA1 (true \<turnstile> ades_state_choice) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 (P \<turnstile> Q))"
    by (simp only: II_Rac_design RA1_idem)
  also have "... =
    RA1 ((true \<turnstile> ades_state_choice) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         (P \<turnstile> Q))"
    by (simp only: RA1_wait_cond)
  also have "... =
    RA1 ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P) \<turnstile>
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
    by (simp only: design_wait_cond)
  finally show ?thesis .
qed

lemma RA_design_components:
  "RA (P \<turnstile> Q) = RA ((\<not> RA1 (\<not> P)) \<turnstile> RA1 Q)"
proof -
  have "RA1 (P \<turnstile> Q) =
      RA1 ((\<not> RA1 (\<not> P)) \<turnstile> Q)"
    by (rule RA1_design_pre)
  also have "... =
      RA1 ((\<not> RA1 (\<not> P)) \<turnstile> RA1 Q)"
    by (rule RA1_design_post)
  finally show ?thesis
    by (simp only: RA_def')
qed

(* The wait-conditional normal form of a reactive angelic design with a
   true precondition. *)
lemma RA_true_design:
  "RA (true \<turnstile> Q) =
   RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 Q))"
  by (simp only: RA_as_RA1_RA3_RA2 RA2_design_distrib RA2_true
      RA1_RA3_design expr_if_idem)

(* RA_A_absorb specialised to designs: PBMH components and freshness of
   the final ok' suffice for the design to satisfy the absorption
   premises. *)
lemma RA_A_absorb_design:
  assumes "(\<not> F) is PBMH_ades" "T is PBMH_ades"
    and "$ok\<^sup>> \<sharp> F" "$ok\<^sup>> \<sharp> T"
  shows "(RA \<circ> A) (F \<turnstile> T) = RA (F \<turnstile> T)"
proof -
  have "(F \<turnstile> T) is PBMH_ades"
    using PBMH_ades_design_closure[OF assms(1,2)]
    by (simp only: pred_ba.double_compl)
  then show ?thesis
    by (rule RA_A_absorb[OF _ design_is_H1_H2[OF assms(3,4)]])
qed

(* The common special case of a true precondition. *)
lemma RA_A_absorb_design_true:
  assumes "T is PBMH_ades" and "$ok\<^sup>> \<sharp> T"
  shows "(RA \<circ> A) (true \<turnstile> T) = RA (true \<turnstile> T)"
  by (rule RA_A_absorb_design[OF _ assms(1) _ assms(2)];
      simp add: pred_ba.compl_top_eq false_PBMH_ades unrest)

lemma RA_wait_false_ok_subst:
  "((rad_wait_false \<circ> RA) P) \<lbrakk>\<guillemotleft>ok'\<guillemotright>/ok\<^sup>>\<rbrakk> =
   (RA2 \<circ> RA1) ((P \<^sub>f) \<lbrakk>\<guillemotleft>ok'\<guillemotright>/ok\<^sup>>\<rbrakk>)"
  apply (simp add: RA_def RA3_def rad_wait_false_def RA1_def RA2_def
      expr_if_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def)
  apply clarify
  subgoal for x z
    by (cases "astate.s\<^sub>v (des_vars.more x)";
        cases "des_vars.more x"; cases x;
        cases "des_vars.more z"; cases z;
        auto simp add: lens_defs des_vars.ok_def rad_wait_def astate.s_def
          des_vars.more\<^sub>L_def rad_trace_extensions_def
          rad_zero_trace_def rad_normalise_choices_def
          rad_trace_difference_def conj_commute conj_left_commute)
  done

lemmas RA_wait_false_ok_subst' =
  RA_wait_false_ok_subst[simplified comp_apply]

(* Paper Lemma 20 *)
(* (rad_wait_false (RA (A
     (\<not> (P \<^sub>f)^f \<turnstile> (P \<^sub>f)^t))))^f =
   RA2 \<circ> RA1 \<circ> PBMH (\<not> ok \<or> (P \<^sub>f)^f) *)
lemma RA_design_wf_ok_false:
  "((rad_wait_false \<circ> RA \<circ> A)
      ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t))\<^sup>f =
   (RA2 \<circ> RA1 \<circ> PBMH_ades) ((\<not> ok\<^sup><) \<or> (P \<^sub>f)\<^sup>f)"
proof -
  have pbmh_design:
    "(rad_wait_false
        (PBMH_ades ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)))\<^sup>f =
     PBMH_ades ((\<not> ok\<^sup><) \<or> (P \<^sub>f)\<^sup>f)"
    apply (simp add: rad_wait_false_def PBMH_ades_def design_def fun_eq_iff
        subst_app_def subst_upd_def subst_id_def SEXP_def Let_def)
    apply (simp add: PBMH_def pbmh_step_def)
    apply pred_auto
    done
  show ?thesis
    unfolding comp_apply
    apply (subst RA_A')
     apply (rule design_is_H1_H2)
      apply pred_auto
     apply pred_auto
    apply (simp only: RA_wait_false_ok_subst' pbmh_design)
    done
qed

lemmas RA_design_wf_ok_false' = RA_design_wf_ok_false[simplified comp_apply]

(* Paper Lemma 21 *)
(* (RA \<circ> A(\<not>P^f_f \<turnstile> P^t_f))^t_f = RA2 \<circ> RA1 \<circ> PBMH(\<not>ok \<or> P^f_f \<or> P^t_f) *)
lemma RA_design_wf_ok_true:
  "((rad_wait_false \<circ> RA \<circ> A)
      ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t))\<^sup>t =
   (RA2 \<circ> RA1 \<circ> PBMH_ades) ((\<not> ok\<^sup><) \<or> (P \<^sub>f)\<^sup>f \<or> (P \<^sub>f)\<^sup>t)"
  unfolding comp_apply
  apply (subst RA_A')
   apply (rule design_is_H1_H2; pred_auto)
  apply (simp only: RA_wait_false_ok_subst')
  apply (rule arg_cong[where f=RA2])
  apply (rule arg_cong[where f=RA1])
  by (simp add: rad_wait_false_def PBMH_ades_def design_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def Let_def
      PBMH_def pbmh_step_def; pred_auto)

lemmas RA_design_wf_ok_true' = RA_design_wf_ok_true[simplified comp_apply]

(* Paper Lemma 22 *)
lemma RA_design_post:
  "RA (P \<turnstile> Q) = RA (P \<turnstile> (RA2 \<circ> RA1) Q)"
  unfolding RA_def' comp_apply
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_design_distrib RA2_idem)
  by (rule arg_cong[where f=RA3], rule RA1_design_post)

(* Under (RA \<circ> A) with a true precondition, a postcondition may be
   replaced by its RA2 \<circ> RA1 \<circ> PBMH_ades normalisation. *)
lemma RA_A_true_design_post:
  assumes "(true \<turnstile> Z) is \<^bold>H" and "(true \<turnstile> T) is \<^bold>H"
    and "RA2 (RA1 (PBMH_ades Z)) = T" and "PBMH_ades T = T"
  shows "(RA \<circ> A) (true \<turnstile> Z) = (RA \<circ> A) (true \<turnstile> T)"
proof -
  have push: "PBMH_ades (true \<turnstile> X) = (true \<turnstile> PBMH_ades X)" for X
    by (simp add: design_as_disj PBMH_ades_disj PBMH_ades_conj_ok)
  have "RA (A (true \<turnstile> Z)) = RA (true \<turnstile> PBMH_ades Z)"
    by (simp only: RA_A'[OF assms(1)] push)
  also have "... = RA (true \<turnstile> RA2 (RA1 (PBMH_ades Z)))"
    by (rule RA_design_post[simplified comp_apply])
  also have "... = RA (A (true \<turnstile> T))"
    by (simp only: assms(3) RA_A'[OF assms(2)] push assms(4))
  finally show ?thesis
    by (simp only: comp_apply)
qed

lemma PBMH_ades_RA2_RA1_absorb:
  "PBMH_ades (RA2 (RA1 (PBMH_ades P))) = RA2 (RA1 (PBMH_ades P))"
  using RA2_PBMH_ades_closure[OF RA1_PBMH_ades_closure[OF
      Healthy_Idempotent[OF PBMH_ades_Idempotent]]]
  by (simp add: Healthy_def')

lemma RA_RA2_RA1_PBMH_ades_conj_ok:
  "RA (RA2 (RA1 (PBMH_ades P)) \<and> ok\<^sup>>) =
   RA (PBMH_ades (P \<and> ok\<^sup>>))"
  by (simp only: RA1_conj_ok[symmetric] RA2_conj_ok[symmetric]
      RA_RA2_RA1_absorb PBMH_ades_conj_ok)

lemma RA_design_PBMH_normalise:
  "RA (PBMH_ades
      ((\<not> RA2 (RA1 (PBMH_ades ((\<not> ok\<^sup><) \<or> F)))) \<turnstile>
        RA2 (RA1 (PBMH_ades
          ((\<not> ok\<^sup><) \<or> F \<or> T))))) =
   RA (PBMH_ades ((\<not> F) \<turnstile> T))"
proof -
  let ?X = "(\<not> ok\<^sup><) \<or> F"
  let ?Z = "(\<not> ok\<^sup><) \<or> F \<or> T"
  let ?U = "RA2 (RA1 (PBMH_ades ?X))"
  let ?V = "RA2 (RA1 (PBMH_ades ?Z))"
  have U_healthy: "PBMH_ades ?U = ?U"
    by (simp only: PBMH_ades_RA2_RA1_absorb)
  have V_healthy: "PBMH_ades ?V = ?V"
    by (simp only: PBMH_ades_RA2_RA1_absorb)
  have absorb:
      "((\<not> ok\<^sup><) \<or> ?X \<or> (?Z \<and> ok\<^sup>>)) =
       ((\<not> ok\<^sup><) \<or> F \<or> (T \<and> ok\<^sup>>))"
    by pred_auto
  have "RA (PBMH_ades ((\<not> ?U) \<turnstile> ?V)) =
        RA (PBMH_ades
          ((\<not> ok\<^sup><) \<or> ?U \<or> (?V \<and> ok\<^sup>>)))"
    by (simp add: design_as_disj)
  also have "... = RA
      (PBMH_ades (\<not> ok\<^sup><) \<or> PBMH_ades ?U \<or>
        PBMH_ades (?V \<and> ok\<^sup>>))"
    by (simp only: PBMH_ades_disj)
  also have "... = RA
      ((\<not> ok\<^sup><) \<or> ?U \<or> (?V \<and> ok\<^sup>>))"
    by (simp only: PBMH_ades_not_ok_expr PBMH_ades_conj_ok
        U_healthy V_healthy)
  also have "... =
      (RA (\<not> ok\<^sup><) \<or> RA (PBMH_ades ?X) \<or>
        RA (PBMH_ades (?Z \<and> ok\<^sup>>)))"
    by (simp only: RA_disj RA_RA2_RA1_absorb[of "PBMH_ades ?X"]
        RA_RA2_RA1_PBMH_ades_conj_ok[of ?Z])
  also have "... = RA (PBMH_ades
      ((\<not> ok\<^sup><) \<or> ?X \<or> (?Z \<and> ok\<^sup>>)))"
    by (simp only: RA_disj PBMH_ades_disj PBMH_ades_not_ok_expr
        PBMH_ades_conj_ok)
  also have "... = RA (PBMH_ades
      ((\<not> ok\<^sup><) \<or> F \<or> (T \<and> ok\<^sup>>)))"
    by (simp only: absorb)
  also have "... = RA (PBMH_ades ((\<not> F) \<turnstile> T))"
    by (simp add: design_as_disj)
  finally show ?thesis .
qed

(* Thesis Theorem T.G.4.5. *)
lemma RA_design_form_idem:
  "(RA \<circ> A)
      ((\<not> (rad_wait_false
          ((RA \<circ> A)
            ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)))\<^sup>f) \<turnstile>
        (rad_wait_false
          ((RA \<circ> A)
            ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)))\<^sup>t) =
   (RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)"
proof -
  show ?thesis
    unfolding comp_apply
    apply (subst RA_A'[OF rad_wait_false_design_is_H])
    apply (simp only: RA_design_wf_ok_false'
        RA_design_wf_ok_true')
    apply (subst RA_design_PBMH_normalise)
    by (rule RA_A'[OF rad_wait_false_design_is_H, symmetric])
qed

subsection \<open>RAD\<close>

(* Paper Definition 35. *)
definition RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RAD = RA \<circ> CSPA1 \<circ> CSPA2 \<circ> PBMH_ades"

lemma RAD_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RAD P \<sqsubseteq> RAD Q"
  by (simp add: RAD_def RA_mono CSPA1_mono CSPA2_mono PBMH_ades_mono)

lemma RAD_Monotonic [closure]: "Monotonic RAD"
  unfolding RAD_def
  by (intro Monotonic_comp RA_Monotonic CSPA1_Monotonic
      CSPA2_Monotonic PBMH_ades_Monotonic)

lemma RAD_PBMH_ades_healthy [closure]: "RAD P is PBMH_ades"
  unfolding RAD_def comp_apply
  apply (rule RA_PBMH_ades_closure)
  apply (simp only: Healthy_def')
  apply (rule CSPA1_PBMH_ades_closure)
  apply (rule CSPA2_PBMH_ades_closure)
  by (simp only: PBMH_ades_idem)

lemma RAD_is_PBMH_ades [closure]:
  assumes "P is RAD"
  shows "P is PBMH_ades"
  using RAD_PBMH_ades_healthy[of P] assms
  by (simp only: Healthy_def')

lemma RAD_H1_CSPA2_PBMH:
  "RAD P = (RA \<circ> H1 \<circ> CSPA2 \<circ> PBMH_ades) P"
  by (simp add: RAD_def CSPA2_def RA_CSPA1[simplified comp_apply])

(* Paper Theorem 11. *)
theorem RAD_design_form:
  "RAD P = (RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)"
proof -
  have design_healthy: "H1 (H2 P) is \<^bold>H"
    by (simp only: Healthy_def' H1_H2_idempotent)
  have "RAD P = RA (A (H1 (H2 P)))"
    by (simp only: comp_apply RAD_H1_CSPA2_PBMH CSPA2_def
        RA_A'[OF design_healthy]
        PBMH_ades_H1_H2_commute[simplified comp_apply])
  also have "... = RA (A (H1 (H2 (P \<^sub>f))))"
    unfolding RA_def comp_apply
    by (simp only: RA3_wait_false_absorb[simplified comp_apply,
          of "A (H1 (H2 P))"]
        rad_wait_false_A_commute[simplified comp_apply]
        rad_wait_false_H1_CSPA2_commute[unfolded CSPA2_def, simplified comp_apply])
  finally show ?thesis
    by (simp add: H1_H2_eq_design)
qed

(* Paper Theorem 11, as an elimination rule for RAD-healthy predicates. *)
lemma RAD_design_form':
  assumes "P is RAD"
  shows "P = (RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)"
  using assms by (simp only: Healthy_def' RAD_design_form)

lemma RAD_wf_ok_false_PBMH:
  assumes "P is RAD"
  shows "(P \<^sub>f)\<^sup>f is PBMH_ades"
proof -
  have component: "(P \<^sub>f)\<^sup>f = RA2 (RA1 (PBMH_ades ((\<not> ok\<^sup><) \<or> (P \<^sub>f)\<^sup>f)))"
    using arg_cong[where f="\<lambda>R. (R \<^sub>f)\<^sup>f", OF RAD_design_form'[OF assms]]
    by (simp only: comp_apply RA_design_wf_ok_false')
  show ?thesis
    unfolding Healthy_def'
    using PBMH_ades_RA2_RA1_absorb[of "(\<not> ok\<^sup><) \<or> (P \<^sub>f)\<^sup>f"]
    by (simp only: component[symmetric])
qed

lemma RAD_wf_ok_true_PBMH:
  assumes "P is RAD"
  shows "(P \<^sub>f)\<^sup>t is PBMH_ades"
proof -
  have component: "(P \<^sub>f)\<^sup>t =
      RA2 (RA1 (PBMH_ades
        ((\<not> ok\<^sup><) \<or> (P \<^sub>f)\<^sup>f \<or> (P \<^sub>f)\<^sup>t)))"
    using arg_cong[where f="\<lambda>R. (R \<^sub>f)\<^sup>t", OF RAD_design_form'[OF assms]]
    by (simp only: comp_apply RA_design_wf_ok_true')
  show ?thesis
    unfolding Healthy_def'
    using PBMH_ades_RA2_RA1_absorb[of "(\<not> ok\<^sup><) \<or> (P \<^sub>f)\<^sup>f \<or> (P \<^sub>f)\<^sup>t"]
    by (simp only: component[symmetric])
qed

(* The normal-form design of a RAD-healthy predicate has PBMH-healthy
   components. *)
lemma RAD_design_PBMH:
  assumes "P is RAD"
  shows "((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t) is PBMH_ades"
  by (rule PBMH_ades_design_closure;
      intro RAD_wf_ok_false_PBMH[OF assms] RAD_wf_ok_true_PBMH[OF assms])

(* The RAD normal form with the A stripped: RAD-healthy predicates are
   RA images of their wait-false design. *)
lemma RAD_RA_design_form:
  assumes "P is RAD"
  shows "P = RA ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)"
  using RAD_design_form'[OF assms]
  by (simp only: RA_A_absorb[OF RAD_design_PBMH[OF assms]
        rad_wait_false_design_is_H])

lemma RAD_idem: "RAD (RAD P) = RAD P"
  by (simp only: RAD_design_form RA_design_form_idem)

lemma RAD_Idempotent [closure]: "Idempotent RAD"
  by (simp add: Idempotent_def RAD_idem)

lemma RAD_healthy [closure]: "RAD P is RAD"
  by (simp add: Healthy_def' RAD_idem)

abbreviation bottom_RAD :: "('t::trace, 'e) reactive_angelic_design"
    ("\<^bold>\<bottom>\<^sub>R\<^sub>A\<^sub>D") where
"\<^bold>\<bottom>\<^sub>R\<^sub>A\<^sub>D \<equiv> RAD true"

abbreviation top_RAD :: "('t::trace, 'e) reactive_angelic_design"
    ("\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D") where
"\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D \<equiv> RAD false"

lemma bottom_RAD_lower:
  assumes "P is RAD"
  shows "\<^bold>\<bottom>\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> P"
proof -
  have "RAD true \<sqsubseteq> RAD P"
    by (rule RAD_mono; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms])
qed

lemma top_RAD_upper:
  assumes "P is RAD"
  shows "P \<sqsubseteq> \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
proof -
  have "RAD P \<sqsubseteq> RAD false"
    by (rule RAD_mono; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms])
qed

lemma RAD_is_RA [closure]:
  assumes "P is RAD"
  shows "P is RA"
proof -
  have "RAD P is RA"
    unfolding RAD_def comp_apply
    by (rule RA_healthy)
  then show ?thesis
    using assms by (simp only: Healthy_def')
qed

lemma RAD_is_RA1:
  assumes "P is RAD"
  shows "P is RA1"
proof -
  have "RA1 (RA P) = RA P" by (simp add: RA_def RA1_idem)
  then show ?thesis using RAD_is_RA[OF assms]
    by (simp add: Healthy_def')
qed

lemma RAD_is_RA2:
  assumes "P is RAD"
  shows "P is RA2"
  by (rule RA_is_RA2[OF RAD_is_RA[OF assms]])

lemma RAD_is_RA3:
  assumes "P is RAD"
  shows "P is RA3"
  by (rule RA_is_RA3[OF RAD_is_RA[OF assms]])

lemma RAD_is_CSPA1:
  assumes "P is RAD"
  shows "P is CSPA1"
proof -
  have "CSPA1 (RAD P) = RAD P"
    by (simp add: RAD_def RA_def RA1_CSPA1_commute[simplified comp_apply, symmetric]
        CSPA1_RA2_commute CSPA1_RA3_commute CSPA1_idem)
  then show ?thesis using assms by (simp add: Healthy_def')
qed

lemma RAD_is_CSPA2:
  assumes "P is RAD"
  shows "P is CSPA2"
proof -
  have "CSPA2 (RAD P) = RAD P"
    by (simp add: RAD_def RA_def
        CSPA2_RA1_commute CSPA2_RA2_commute CSPA2_RA3_commute CSPA2_CSPA1_commute CSPA2_idem)
  then show ?thesis using assms by (simp add: Healthy_def')
qed

lemma RAD_components_iff:
  "(P is RAD) \<longleftrightarrow>
   ((P is RA1) \<and> (P is RA2) \<and> (P is RA3) \<and>
    (P is CSPA1) \<and> (P is CSPA2) \<and> (P is PBMH_ades))"
proof
  assume "P is RAD"
  then show "(P is RA1) \<and> (P is RA2) \<and> (P is RA3) \<and>
    (P is CSPA1) \<and> (P is CSPA2) \<and> (P is PBMH_ades)"
    by (auto intro: RAD_is_RA1 RAD_is_RA2 RAD_is_RA3
        RAD_is_CSPA1 RAD_is_CSPA2 RAD_is_PBMH_ades)
next
  assume "(P is RA1) \<and> (P is RA2) \<and> (P is RA3) \<and>
    (P is CSPA1) \<and> (P is CSPA2) \<and> (P is PBMH_ades)"
  then show "P is RAD"
    by (simp add: Healthy_def' RAD_def RA_def)
qed

lemma RAD_design_closure:
  assumes "P is \<^bold>H" "(P \<^sub>f) = P"
  shows "(RA \<circ> A) P is RAD"
proof -
  have normal_form: "(\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t = P"
    using assms
    by (simp only: Healthy_def' H1_H2_eq_design)
  show ?thesis
    using RAD_healthy[of P]
    by (simp only: RAD_design_form normal_form)
qed

text \<open>
  Closure method for operators in RAD normal form
  \<open>(RA \<circ> A) (F \<turnstile> T)\<close>: discharges the design-healthiness obligation by
  @{method pred_auto} and the wait-false fixed-point obligation by
  @{thm [source] rad_wait_false_distrib}.  Extra simp rules (for example an
  operator's definition) can be passed via \<open>add\<close>.
\<close>

method rad_closure uses add =
  (rule RAD_design_closure,
   (rule design_is_H1_H2; pred_auto),
   (simp add: rad_wait_false_distrib add))

subsubsection \<open>Empty choice sets\<close>

lemma RAD_empty:
  "P is RAD \<Longrightarrow> \<not> P (ades_obs ok0 s0 ok' {})"
proof -
  assume assms: "P is RAD"
  show ?thesis
  by (subst Healthy_if[OF assms, symmetric]; simp add: RAD_def RA_def RA1_obs)
qed

lemma rad_d2ac_not_RAD:
  "\<not> (d2ac D is RAD)"
proof
  assume "d2ac D is RAD"
  then have "\<not> d2ac D (ades_obs False s0 True {})" for s0
    by (rule RAD_empty)
  then show False
    by (simp add: d2ac_def; pred_auto)
qed

lemma A3_not_RAD:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "\<not> (A3 P is RAD)"
proof
  assume "A3 P is RAD"
  then have "\<not> A3 P (ades_obs False s0 True {})" for s0
    by (rule RAD_empty)
  then show False
    by (simp add: A3_def; pred_auto)
qed

end
