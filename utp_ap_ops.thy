section \<open>Angelic Process Operators\<close>

theory utp_ap_ops
  imports utp_ap_rad
begin

subsection \<open>Angelic Choice\<close>

abbreviation achoice_AP ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design"
  (infixl "\<squnion>\<^sub>A\<^sub>P" 70)
where "P \<squnion>\<^sub>A\<^sub>P Q \<equiv> P \<squnion> Q"

(* Paper Definition 50. *)
lemma AP_angelic_choice:
  "P \<squnion>\<^sub>A\<^sub>P Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

lemma AP_angelic_choice_form:
  assumes "P is AP" "Q is AP"
  shows "P \<squnion>\<^sub>A\<^sub>P Q =
    RA3AP (((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f)) \<turnstile>
            (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t)) \<and>
           ((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>f)) \<turnstile>
            (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>t)))"
proof -
  have "P \<squnion>\<^sub>A\<^sub>P Q = (AP P \<and> AP Q)"
    by (simp only: AP_angelic_choice Healthy_if[OF assms(1)]
        Healthy_if[OF assms(2)])
  also have "... =
      (RA3AP ((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t)) \<and>
       RA3AP ((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>t)))"
    by (simp only: AP_RA3AP_design comp_apply)
  finally show ?thesis
    by (simp only: RA3AP_conj[symmetric])
qed

lemma AP_angelic_choice_design:
  assumes "P is AP" "Q is AP"
  shows "P \<squnion>\<^sub>A\<^sub>P Q =
    RA3AP ((\<not> ((RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f) \<and>
               (RA2 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>f))) \<turnstile>
           (((RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f) \<or>
             (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t)) \<and>
            ((RA2 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>f) \<or>
             (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>t))))"
  by (simp only: AP_angelic_choice_form[OF assms]; pred_auto)

(* Thesis Theorem T.6.4.1. *)
lemma AP_angelic_closure [closure]:
  assumes "P is AP" "Q is AP"
  shows "P \<squnion>\<^sub>A\<^sub>P Q is AP"
proof -
  let ?NP = "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
  let ?NQ = "((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>t))"
  have C_A: "(?NP \<and> ?NQ) is A"
    using A_angelic_closure[OF AP_body_is_A[of P] AP_body_is_A[of Q]]
    by (simp only: angelic_design_angelic)
  have C_RA2: "(?NP \<and> ?NQ) is RA2"
    by (rule Healthy_intro,
        simp only: RA2_conj Healthy_if[OF AP_body_is_RA2])
  show ?thesis
    by (simp only: AP_angelic_choice_form[OF assms]
        RA3AP_AP_closure[OF C_A C_RA2])
qed

(* Paper Theorem 45 / Thesis Theorem T.6.4.3. *)
theorem RA1_H1_angelic_choice:
  assumes "P is RAD" "Q is RAD"
  shows "RA1 (H1 P \<squnion>\<^sub>A\<^sub>P H1 Q) = P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q"
  by (simp only: AP_angelic_choice RA1_conj
      RA1_H1_RAD_healthy[OF assms(1), simplified comp_apply]
      RA1_H1_RAD_healthy[OF assms(2), simplified comp_apply])

(* Paper Theorem 46 / Thesis Theorem T.6.4.4. *)
theorem H1_RA1_angelic_choice_refine:
  assumes "P is AP" "Q is AP"
  shows "P \<squnion>\<^sub>A\<^sub>P Q \<sqsubseteq> H1 (RA1 P \<squnion>\<^sub>R\<^sub>A\<^sub>D RA1 Q)"
proof -
  have closed: "(P \<squnion>\<^sub>A\<^sub>P Q) is AP"
    by (rule AP_angelic_closure[OF assms])
  have eq: "H1 (RA1 P \<squnion>\<^sub>R\<^sub>A\<^sub>D RA1 Q) =
      H1 (RA1 (P \<squnion>\<^sub>A\<^sub>P Q))"
    by (simp only: AP_angelic_choice RA1_conj)
  have "(P \<squnion>\<^sub>A\<^sub>P Q) \<sqsubseteq> H1 (RA1 (P \<squnion>\<^sub>A\<^sub>P Q))"
    using H1_RA1_AP_refine[of "P \<squnion>\<^sub>A\<^sub>P Q"]
    by (simp only: comp_apply Healthy_if[OF closed])
  then show ?thesis
    by (simp only: eq)
qed

subsection \<open>Demonic Choice\<close>

abbreviation dchoice_AP ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design"
  (infixl "\<sqinter>\<^sub>A\<^sub>P" 65)
where "P \<sqinter>\<^sub>A\<^sub>P Q \<equiv> P \<sqinter> Q"

(* Paper Definition 51. *)
lemma AP_demonic_choice:
  "P \<sqinter>\<^sub>A\<^sub>P Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

(* Thesis Theorem T.6.4.5. *)
lemma AP_demonic_closure [closure]:
  assumes "P is AP" "Q is AP"
  shows "P \<sqinter>\<^sub>A\<^sub>P Q is AP"
proof -
  let ?NP = "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
  let ?NQ = "((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>wf)\<^sup>t))"
  have form: "P \<sqinter>\<^sub>A\<^sub>P Q = RA3AP (?NP \<or> ?NQ)"
    apply (rule_tac s="AP P \<or> AP Q" in trans)
    apply (simp only: AP_demonic_choice Healthy_if[OF assms(1)]
        Healthy_if[OF assms(2)])
    by (simp only: AP_RA3AP_design RA3AP_disj[symmetric])
  have C_A: "(?NP \<or> ?NQ) is A"
    by (rule Healthy_intro,
        simp only: A_disj Healthy_if[OF AP_body_is_A])
  have C_RA2: "(?NP \<or> ?NQ) is RA2"
    by (rule Healthy_intro,
        simp only: RA2_disj Healthy_if[OF AP_body_is_RA2])
  show ?thesis
    by (simp only: form RA3AP_AP_closure[OF C_A C_RA2])
qed

(* Paper Theorem 48 / Thesis Theorem T.6.4.7. *)
theorem RA1_H1_demonic_choice:
  assumes "P is RAD" "Q is RAD"
  shows "RA1 (H1 P \<sqinter>\<^sub>A\<^sub>P H1 Q) = P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q"
  by (simp only: AP_demonic_choice RA1_disj
      RA1_H1_RAD_healthy[OF assms(1), simplified comp_apply]
      RA1_H1_RAD_healthy[OF assms(2), simplified comp_apply])

(* Paper Theorem 49 / Thesis Theorem T.6.4.8, as Theorem 46. *)
theorem H1_RA1_demonic_choice_refine:
  assumes "P is AP" "Q is AP"
  shows "P \<sqinter>\<^sub>A\<^sub>P Q \<sqsubseteq> H1 (RA1 P \<sqinter>\<^sub>R\<^sub>A\<^sub>D RA1 Q)"
proof -
  have closed: "(P \<sqinter>\<^sub>A\<^sub>P Q) is AP"
    by (rule AP_demonic_closure[OF assms])
  have eq: "H1 (RA1 P \<sqinter>\<^sub>R\<^sub>A\<^sub>D RA1 Q) =
      H1 (RA1 (P \<sqinter>\<^sub>A\<^sub>P Q))"
    by (simp only: AP_demonic_choice RA1_disj)
  have "(P \<sqinter>\<^sub>A\<^sub>P Q) \<sqsubseteq> H1 (RA1 (P \<sqinter>\<^sub>A\<^sub>P Q))"
    using H1_RA1_AP_refine[of "P \<sqinter>\<^sub>A\<^sub>P Q"]
    by (simp only: comp_apply Healthy_if[OF closed])
  then show ?thesis
    by (simp only: eq)
qed

subsection \<open>Chaos\<close>

(* Paper Definition 52 / Thesis Definition 133. *)
definition Chaos_AP ::
  "('t::trace, 'e) reactive_angelic_design" ("Chaos\<^sub>A\<^sub>P") where
[pred]: "Chaos_AP = AP (false \<turnstile> true)"

lemma Chaos_AP_is_AP [closure]: "Chaos\<^sub>A\<^sub>P is AP"
  by (simp add: Chaos_AP_def AP_healthy)

lemma bottom_AP_is_Chaos:
  "(\<^bold>\<bottom>\<^sub>A\<^sub>P ::
      ('t::trace, 'e) reactive_angelic_design) = Chaos\<^sub>A\<^sub>P"
  by (simp only: Chaos_AP_def design_false_pre)

(* Paper Lemma 11 / Thesis Lemma L.6.4.1: Chaos_AP = (s.wait \<turnstile> s \<in> ac').
   AP_true_design does not apply, since the precondition is false.
   The statement's type annotation is needed: the local absorb fact
   must share the statement's type variables, and proof-local type
   variables do not generalise. *)
lemma Chaos_AP_design:
  "(Chaos\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design) =
   (($rad_wait_lens\<^sup><)\<^sub>e \<turnstile>
    ($ades_s_lens\<^sup>< \<in> $ades_ac_lens\<^sup>>)\<^sub>e)"
proof -
  have absorb:
      "((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> true)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Y)) =
       (($rad_wait_lens\<^sup><)\<^sub>e \<turnstile>
        ($ades_s_lens\<^sup>< \<in> $ades_ac_lens\<^sup>>)\<^sub>e)"
      for Y :: "('t, 'e) reactive_angelic_design"
    by pred_auto
  have "(Chaos\<^sub>A\<^sub>P :: ('t, 'e) reactive_angelic_design) = AP true"
    by (simp only: Chaos_AP_def design_false_pre)
  also have "... =
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          (\<not> (RA2 \<circ> PBMH_ades) true)) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          (RA2 \<circ> RA1 \<circ> PBMH_ades) true))"
    by (simp only: AP_wait_cond_design rad_wait_false_true subst_pred(1))
  finally show ?thesis
    by (simp only: comp_apply PBMH_ades_true RA2_true absorb)
qed

(* Paper Theorem 50 / Thesis Theorem T.6.4.9: Chaos_AP is a unit for
   angelic choice.  Unlike the RAD proof (Chaos_RAD_angelic_choice_unit),
   which uses conjunctivity of RA, this goes by monotonicity: true is
   the refinement bottom, so Chaos_AP = AP true \<sqsubseteq> AP P = P. *)
theorem Chaos_AP_angelic_choice_unit:
  assumes "P is AP"
  shows "P \<squnion>\<^sub>A\<^sub>P Chaos\<^sub>A\<^sub>P = P"
proof -
  have bot: "true \<sqsubseteq> P"
    by pred_auto
  have "Chaos\<^sub>A\<^sub>P \<sqsubseteq> P"
    using AP_mono[OF bot]
    by (simp only: Chaos_AP_def design_false_pre Healthy_if[OF assms])
  then show ?thesis
    unfolding ref_by_pred_is_leq
    by (rule inf.absorb1)
qed

(* Paper Definition 53 / Thesis Definition 134: the counterpart of
   Chaos_RAD, whose precondition still requires RA1. *)
definition ChaosCSP_AP ::
  "('t::trace, 'e) reactive_angelic_design" ("ChaosCSP\<^sub>A\<^sub>P") where
[pred]: "ChaosCSP_AP = AP ((\<not> RA1 true) \<turnstile> true)"

lemma ChaosCSP_AP_is_AP [closure]: "ChaosCSP\<^sub>A\<^sub>P is AP"
  by (simp add: ChaosCSP_AP_def AP_healthy)

(* The wait-conditional design with failure condition RA1 true, written
   as the thesis L.6.4.2 explicit design.  Not generic in the failure
   condition: the collapse needs it to be independent of s.wait, as
   RA1 true is. *)
lemma chaos_wait_cond_collapse:
  "((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA1 true)) \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 true)) =
   ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
    (($rad_wait_lens\<^sup><)\<^sub>e \<and>
     ($ades_s_lens\<^sup>< \<in> $ades_ac_lens\<^sup>>)\<^sub>e))"
  by (pred_auto add: rad_trace_extensions_def)

(* Thesis Lemma L.6.4.2: ChaosCSP_AP as an explicit design,
   s.wait \<or> \<not> RA1 true \<turnstile> s.wait \<and> s \<in> ac'. *)
lemma ChaosCSP_AP_design:
  "(ChaosCSP\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design) =
   ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
    (($rad_wait_lens\<^sup><)\<^sub>e \<and>
     ($ades_s_lens\<^sup>< \<in> $ades_ac_lens\<^sup>>)\<^sub>e))"
proof -
  have pbmh_ra1: "PBMH_ades (RA1 true) =
      (RA1 true :: ('t, 'e) reactive_angelic_design)"
    using PBMH_ades_RA1_absorb[of true]
    by (simp only: comp_apply PBMH_ades_true)
  have ok_pre:
      "((\<not> ((\<not> ok\<^sup><) \<or> Z)) \<turnstile> Y) = ((\<not> Z) \<turnstile> Y)"
      for Z Y :: "('t, 'e) reactive_angelic_design"
    by pred_auto
  have projf: "(((\<not> RA1 true) \<turnstile> true) ::
      ('t, 'e) reactive_angelic_design)\<^sup>f = ((\<not> ok\<^sup><) \<or> RA1 true)"
    by pred_auto
  have projt: "(((\<not> RA1 true) \<turnstile> true) ::
      ('t, 'e) reactive_angelic_design)\<^sup>t = true"
    by pred_auto
  have wf: "((((\<not> RA1 true) \<turnstile> true) ::
      ('t, 'e) reactive_angelic_design) \<^sub>wf) =
      ((\<not> RA1 true) \<turnstile> true)"
    by (simp only: rad_wait_false_design rad_wait_false_not
        rad_wait_false_RA1_commute rad_wait_false_true)
  have "ChaosCSP\<^sub>A\<^sub>P =
      RA3AP (((\<not> RA1 true) \<turnstile> RA1 true) ::
        ('t, 'e) reactive_angelic_design)"
    by (simp only: ChaosCSP_AP_def AP_RA3AP_design comp_apply wf
        projf projt PBMH_ades_disj PBMH_ades_not_ok_expr pbmh_ra1
        RA2_disj RA2_not_ok_expr RA2_RA1_true PBMH_ades_true RA2_true
        ok_pre)
  then show ?thesis
    by (simp only: RA3AP_design chaos_wait_cond_collapse)
qed

(* Paper Theorem 51 / Thesis Theorem T.6.4.10. *)
theorem H1_Chaos_RAD:
  "H1 (Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) =
   ChaosCSP\<^sub>A\<^sub>P"
proof -
  have "H1 Chaos\<^sub>R\<^sub>A\<^sub>D =
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA1 true)) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        (RA1 true :: ('t, 'e) reactive_angelic_design)))"
    by (simp only: Chaos_RAD_RAD H1_RAD_design[simplified comp_apply]
        rad_wait_false_true subst_pred(1) PBMH_ades_true RA2_true
        RA2_RA1_true RA3AP_design_post)
  then show ?thesis
    by (simp only: chaos_wait_cond_collapse ChaosCSP_AP_design)
qed

(* Paper Theorem 52 / Thesis Theorem T.6.4.11, from Theorem 51 and the
   general Theorem 41. *)
theorem RA1_ChaosCSP_AP:
  "RA1 ChaosCSP\<^sub>A\<^sub>P = Chaos\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: H1_Chaos_RAD[symmetric] Chaos_RAD_RAD
      RA1_H1_RAD[simplified comp_apply])

subsection \<open>Choice\<close>

(* Paper Definition 54. *)
definition Choice_AP ::
  "('t::trace, 'e) reactive_angelic_design" ("Choice\<^sub>A\<^sub>P") where
[pred]: "Choice_AP = AP (true \<turnstile> ac_non_empty)"

lemma Choice_AP_is_AP [closure]: "Choice\<^sub>A\<^sub>P is AP"
  by (simp add: Choice_AP_def AP_healthy)

lemmas Choice_AP_facts =
  rad_wait_false_ac_non_empty PBMH_ades_ac_non_empty
  ac_non_empty_ok_out_subst

lemmas true_post_facts =
  rad_wait_false_true PBMH_ades_true subst_pred(1)

(* Thesis Lemma L.6.4.3. *)
lemma Choice_AP_design:
  "Choice\<^sub>A\<^sub>P =
   (true \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 true))"
  by (simp only: Choice_AP_def AP_true_design[OF Choice_AP_facts]
      RA1_RA2_ac_non_empty)

lemma Choice_AP_RA3AP: "Choice\<^sub>A\<^sub>P = RA3AP (true \<turnstile> RA1 true)"
  by (simp only: Choice_AP_design RA3AP_design expr_if_idem)

(* The non-emptiness requirement is already enforced by AP. *)
lemma Choice_AP': "Choice\<^sub>A\<^sub>P = AP (true \<turnstile> true)"
  by (simp only: Choice_AP_design
      AP_true_design[OF true_post_facts] RA2_true)

(* Paper Theorem 53 / Thesis Theorem T.6.4.12. *)
theorem H1_Choice_RAD:
  "H1 Choice\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>A\<^sub>P"
  by (simp only: Choice_RAD_RA Choice_AP'
      H1_RA_true_design[OF true_post_facts])

(* Paper Theorem 54 / Thesis Theorem T.6.4.13. *)
theorem RA1_Choice_AP:
  "RA1 Choice\<^sub>A\<^sub>P = Choice\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: Choice_AP' Choice_RAD_RA
      RA1_AP_true_design[OF true_post_facts])

subsection \<open>Stop\<close>

(* Paper Definition 55. *)
definition Stop_AP ::
  "('t::trace, 'e) reactive_angelic_design" ("Stop\<^sub>A\<^sub>P") where
[pred]: "Stop_AP = AP (true \<turnstile> stop_post)"

lemma Stop_AP_is_AP [closure]: "Stop\<^sub>A\<^sub>P is AP"
  by (simp add: Stop_AP_def AP_healthy)

lemmas Stop_AP_facts =
  rad_wait_false_stop_post stop_post_PBMH stop_post_ok_out_subst

lemma Stop_AP_design:
  "Stop\<^sub>A\<^sub>P =
   (true \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 stop_post))"
  by (simp only: Stop_AP_def AP_true_design[OF Stop_AP_facts]
      RA2_stop_post)

(* Paper Theorem 55 / Thesis Theorem T.6.4.14. *)
theorem H1_Stop_RAD:
  "H1 Stop\<^sub>R\<^sub>A\<^sub>D = Stop\<^sub>A\<^sub>P"
  by (simp only: Stop_RAD_RA Stop_AP_def
      H1_RA_true_design[OF Stop_AP_facts])

(* Paper Theorem 56 / Thesis Theorem T.6.4.15. *)
theorem RA1_Stop_AP:
  "RA1 Stop\<^sub>A\<^sub>P = Stop\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: Stop_AP_def Stop_RAD_RA
      RA1_AP_true_design[OF Stop_AP_facts])

subsection \<open>Skip\<close>

(* Paper Definition 56. *)
definition Skip_AP ::
  "('t::trace, 'e) reactive_angelic_design" ("Skip\<^sub>A\<^sub>P") where
[pred]: "Skip_AP = AP (true \<turnstile> skip_post)"

lemma Skip_AP_is_AP [closure]: "Skip\<^sub>A\<^sub>P is AP"
  by (simp add: Skip_AP_def AP_healthy)

lemmas Skip_AP_facts =
  rad_wait_false_skip_post skip_post_PBMH skip_post_ok_out_subst

lemma Skip_AP_design:
  "Skip\<^sub>A\<^sub>P =
   (true \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 skip_post))"
  by (simp only: Skip_AP_def AP_true_design[OF Skip_AP_facts]
      RA2_skip_post)

(* Paper Theorem 57 / Thesis Theorem T.6.4.16. *)
theorem H1_Skip_RAD:
  "H1 Skip\<^sub>R\<^sub>A\<^sub>D = Skip\<^sub>A\<^sub>P"
  by (simp only: Skip_RAD_RA Skip_AP_def
      H1_RA_true_design[OF Skip_AP_facts])

(* Paper Theorem 58 / Thesis Theorem T.6.4.17. *)
theorem RA1_Skip_AP:
  "RA1 Skip\<^sub>A\<^sub>P = Skip\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: Skip_AP_def Skip_RAD_RA
      RA1_AP_true_design[OF Skip_AP_facts])

end
