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
    RA3AP (((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
            (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)) \<and>
           ((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f)) \<turnstile>
            (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t)))"
proof -
  have "P \<squnion>\<^sub>A\<^sub>P Q = (AP P \<and> AP Q)"
    by (simp only: AP_angelic_choice Healthy_if[OF assms(1)]
        Healthy_if[OF assms(2)])
  also have "... =
      (RA3AP ((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)) \<and>
       RA3AP ((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t)))"
    by (simp only: AP_RA3AP_design comp_apply)
  finally show ?thesis
    by (simp only: RA3AP_conj[symmetric])
qed

lemma AP_angelic_choice_design:
  assumes "P is AP" "Q is AP"
  shows "P \<squnion>\<^sub>A\<^sub>P Q =
    RA3AP ((\<not> ((RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f) \<and>
               (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f))) \<turnstile>
           (((RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f) \<or>
             (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)) \<and>
            ((RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f) \<or>
             (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t))))"
  by (simp only: AP_angelic_choice_form[OF assms]; pred_auto)

(* Thesis Theorem T.6.4.1. *)
lemma AP_angelic_closure [closure]:
  assumes "P is AP" "Q is AP"
  shows "P \<squnion>\<^sub>A\<^sub>P Q is AP"
proof -
  let ?NP = "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t))"
  let ?NQ = "((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t))"
  have C_A: "(?NP \<and> ?NQ) is A"
    using A_angelic_closure[OF AP_body_is_A[of P] AP_body_is_A[of Q]]
    by (simp only: angelic_design_angelic)
  have C_RA2: "(?NP \<and> ?NQ) is RA2"
    by (rule Healthy_intro,
        simp only: RA2_conj Healthy_if[OF AP_body_is_RA2])
  show ?thesis
    by (simp only: AP_angelic_choice_form[OF assms]
        RA3AP_AP_intro[OF C_A C_RA2])
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
  let ?NP = "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t))"
  let ?NQ = "((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f)) \<turnstile>
              (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t))"
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
    by (simp only: form RA3AP_AP_intro[OF C_A C_RA2])
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
  "(\<^bold>\<bottom>\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design) = Chaos\<^sub>A\<^sub>P"
  by (simp only: Chaos_AP_def design_false_pre)

(* Paper Lemma 11 / Thesis Lemma L.6.4.1: Chaos_AP = (s.wait \<turnstile> s \<in> ac') *)
lemma Chaos_AP_design:
  "(Chaos\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design) =
   (($rad_wait_lens\<^sup><)\<^sub>e \<turnstile> ades_state_choice)"
proof -
  have absorb:
      "((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> true)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Y)) =
       (($rad_wait_lens\<^sup><)\<^sub>e \<turnstile> ades_state_choice)"
      for Y :: "('t, 'e) reactive_angelic_design"
    by (simp only: ades_state_choice_expr; pred_auto)
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
  have wf: "((((\<not> RA1 true) \<turnstile> true) :: ('t, 'e) reactive_angelic_design) \<^sub>f) =
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

lemmas AP_true_post_facts =
  rad_wait_false_true PBMH_ades_true subst_pred(1)

(* Thesis Lemma L.6.4.3. *)
lemma Choice_AP_design:
  "Choice\<^sub>A\<^sub>P =
   (true \<turnstile> (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 true))"
  by (simp only: Choice_AP_def AP_true_design[OF Choice_AP_facts]
      RA1_RA2_ac_non_empty)

lemma Choice_AP_RA3AP: "Choice\<^sub>A\<^sub>P = RA3AP (true \<turnstile> RA1 true)"
  by (simp only: Choice_AP_design RA3AP_design expr_if_idem)

(* The non-emptiness requirement is already enforced by AP. *)
lemma Choice_AP': "Choice\<^sub>A\<^sub>P = AP (true \<turnstile> true)"
  by (simp only: Choice_AP_design
      AP_true_design[OF AP_true_post_facts] RA2_true)

(* Paper Theorem 53 / Thesis Theorem T.6.4.12. *)
theorem H1_Choice_RAD:
  "H1 Choice\<^sub>R\<^sub>A\<^sub>D = Choice\<^sub>A\<^sub>P"
  by (simp only: Choice_RAD_RA Choice_AP'
      H1_RA_true_design[OF AP_true_post_facts])

(* Paper Theorem 54 / Thesis Theorem T.6.4.13. *)
theorem RA1_Choice_AP:
  "RA1 Choice\<^sub>A\<^sub>P = Choice\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: Choice_AP' Choice_RAD_RA
      RA1_AP_true_design[OF AP_true_post_facts])

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
  "Stop\<^sub>A\<^sub>P = (true \<turnstile> (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 stop_post))"
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
  "Skip\<^sub>A\<^sub>P = (true \<turnstile> (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 skip_post))"
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
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T)) ;;\<^sub>D\<^sub>A
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> U))) =
     RA3AP (((\<not> (F ;;\<^sub>A\<^sub>D true)) \<and>
              (\<not> (T ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> G)))) \<turnstile>
             (T ;;\<^sub>A\<^sub>D
               (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                ((\<not> G) \<longrightarrow> U))))"
proof -
  have not_true:
      "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) = false"
    by pred_auto
  have not_false:
      "(\<not> (false :: ('t::trace, 'e) reactive_angelic_design)) = true"
    by pred_auto
  have wait_conj: "\<And>A B C D.
      ((A \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> B) \<and>
       (C \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> D)) =
      ((A \<and> C) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (B \<and> D))"
    by (simp add: expr_if_def fun_eq_iff; pred_auto)
  have seq_form:
    "(((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> F)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T)) ;;\<^sub>D\<^sub>A
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> U))) =
     (((\<not> ((\<not> (true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> F))) ;;\<^sub>A\<^sub>D true)) \<and>
       (\<not> ((ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T) ;;\<^sub>A\<^sub>D
          (\<not> (true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> G)))))) \<turnstile>
      ((ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> T) ;;\<^sub>A\<^sub>D
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

(* Thesis Theorem T.H.3.3. *)
lemma AP_seq_design_PBMH:
  "(AP P ;;\<^sub>D\<^sub>A AP Q) =
   AP (((\<not> (PBMH_ades ((P \<^sub>f)\<^sup>f) ;;\<^sub>A\<^sub>D true)) \<and>
        (\<not> ((RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>D
          ((\<not> rad_wait_lens\<^sup><) \<and>
           (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f))))) \<turnstile>
       ((RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>D
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         RA2 ((\<not> PBMH_ades ((Q \<^sub>f)\<^sup>f)) \<longrightarrow>
              (RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t)))))"
proof -
  let ?Pf = "PBMH_ades ((P \<^sub>f)\<^sup>f)"
  let ?Pt = "RA1 (PBMH_ades ((P \<^sub>f)\<^sup>t))"
  let ?Qf = "PBMH_ades ((Q \<^sub>f)\<^sup>f)"
  let ?Qt = "RA1 (PBMH_ades ((Q \<^sub>f)\<^sup>t))"
  let ?Qf' = "?Qf\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?Qt' = "?Qt\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?pre = "((\<not> (?Pf ;;\<^sub>A\<^sub>D true)) \<and>
    (\<not> (?Pt ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf))))"
  let ?post = "(?Pt ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 ((\<not> ?Qf) \<longrightarrow> ?Qt)))"
  let ?pre' = "((\<not> (?Pf ;;\<^sub>A\<^sub>D true)) \<and>
    (\<not> (?Pt ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf'))))"
  let ?post' = "(?Pt ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 ((\<not> ?Qf') \<longrightarrow> ?Qt')))"
  let ?N' = "(?pre' \<turnstile> ?post')"
  have Q_push:
    "(true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA2 ?Qf'))\<lbrakk>True/ok\<^sup><\<rbrakk> =
     (true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA2 ?Qf))\<lbrakk>True/ok\<^sup><\<rbrakk>"
    "(ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 ?Qt')\<lbrakk>True/ok\<^sup><\<rbrakk> =
     (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 ?Qt)\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp_all add: usubst ok_in_subst_laws)
  have Q_form:
    "AP Q =
     ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA2 ?Qf')) \<turnstile>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 ?Qt'))"
    by (simp only: AP_wait_cond_design comp_apply
        design_ok_in_cong[OF Q_push])
  have seq_raw:
    "(AP P ;;\<^sub>D\<^sub>A AP Q) =
     RA3AP (((\<not> (RA2 ?Pf ;;\<^sub>A\<^sub>D true)) \<and>
              (\<not> (RA2 ?Pt ;;\<^sub>A\<^sub>D
                ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf')))) \<turnstile>
             (RA2 ?Pt ;;\<^sub>A\<^sub>D
               (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                ((\<not> RA2 ?Qf') \<longrightarrow> RA2 ?Qt'))))"
  proof -
    have "(AP P ;;\<^sub>D\<^sub>A AP Q) =
      (((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA2 ?Pf)) \<turnstile>
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 ?Pt)) ;;\<^sub>D\<^sub>A
       ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA2 ?Qf')) \<turnstile>
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 ?Qt')))"
      by (simp only: Q_form AP_wait_cond_design[of P] comp_apply)
    also have "... = RA3AP
      (((\<not> (RA2 ?Pf ;;\<^sub>A\<^sub>D true)) \<and>
         (\<not> (RA2 ?Pt ;;\<^sub>A\<^sub>D
          ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf')))) \<turnstile>
       (RA2 ?Pt ;;\<^sub>A\<^sub>D
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         ((\<not> RA2 ?Qf') \<longrightarrow> RA2 ?Qt'))))"
      apply (rule AP_wait_design_seq)
           apply (simp_all add: unrest)
       apply (intro RA2_PBMH_ades_closure
          Healthy_Idempotent[OF PBMH_ades_Idempotent])
      apply (intro RA2_PBMH_ades_closure RA1_PBMH_ades_closure
          Healthy_Idempotent[OF PBMH_ades_Idempotent])
      done
    finally show ?thesis .
  qed
  have wait_fixed:
    "RA2 ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf') =
     ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf')"
    by (simp only: RA2_not_wait_conj RA2_idem)
  have seq_RA3AP_RA2:
    "(AP P ;;\<^sub>D\<^sub>A AP Q) = RA3AP (RA2 ?N')"
    unfolding seq_raw
    by (simp only: RA2_design_distrib RA2_conj RA2_not
        RA2_aseq_fixed RA2_aseq_fixed[OF wait_fixed]
        RA2_true RA2_idem RA2_wait_cond RA2_state_choice RA2_impl)
  have Pf_PBMH: "?Pf is PBMH_ades"
    and Pt_PBMH: "?Pt is PBMH_ades"
    and Qf_PBMH: "?Qf' is PBMH_ades"
    and Qt_PBMH: "?Qt' is PBMH_ades"
    by (simp_all add: Healthy_def' PBMH_ades_ok_in_subst
        PBMH_ades_idem
        PBMH_ades_RA1_absorb[simplified comp_apply])
  have N_PBMH: "?N' is PBMH_ades"
  proof -
    have bad_PBMH:
      "((?Pf ;;\<^sub>A\<^sub>D true) \<or>
        (?Pt ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf')))
       is PBMH_ades"
      unfolding rad_wait_cond_false[symmetric]
      by (intro PBMH_ades_disj_closure aseq_ades_PBMH_ades_closure
          rad_wait_cond_PBMH_ades_closure RA2_PBMH_ades_closure
          false_PBMH_ades true_PBMH_ades Pf_PBMH Pt_PBMH Qf_PBMH)
    have post_PBMH: "?post' is PBMH_ades"
      unfolding impl_neg_disj
      apply (simp only: pred_ba.double_compl)
      by (intro aseq_ades_PBMH_ades_closure
          rad_wait_cond_PBMH_ades_closure PBMH_ades_disj_closure
          RA2_PBMH_ades_closure ades_state_choice_is_PBMH_ades
          Pt_PBMH Qf_PBMH Qt_PBMH)
    have pre_as_neg: "?pre' =
        (\<not> ((?Pf ;;\<^sub>A\<^sub>D true) \<or>
          (?Pt ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?Qf'))))"
      by pred_auto
    show ?thesis
      unfolding pre_as_neg
      by (rule PBMH_ades_design_closure[OF bad_PBMH post_PBMH])
  qed
  have seq_nonempty:
    "(ac_non_empty \<and>
      ((\<not> (T ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> G))) \<and>
       (T ;;\<^sub>A\<^sub>D
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (G \<or> RA1 U))))) =
     ((\<not> (T ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> G))) \<and>
      (T ;;\<^sub>A\<^sub>D
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
    "RA2 ?Qt' = RA1 (RA2
      ((PBMH_ades ((Q \<^sub>f)\<^sup>t))\<lbrakk>True/ok\<^sup><\<rbrakk>))"
    by (simp only: RA1_ok_in_subst
        RA1_RA2_commute'[symmetric])
  have absorb0:
    "(ac_non_empty \<and> (?pre' \<and> ?post')) = (?pre' \<and> ?post')"
    apply (simp only: impl_neg_disj pred_ba.double_compl RA2_disj
        Qt_RA1_form)
    by (rule conj_extra_absorb[OF seq_nonempty])
  have AP_N: "AP ?N' = RA3AP (RA2 ?N')"
    by (rule AP_design_RA3AP_RA2[OF _ _ N_PBMH
        RA1_true_absorb_lift[OF absorb0]]; simp add: unrest)
  have desubst: "?N' = (?pre \<turnstile> ?post)"
    by (rule design_ok_in_cong)
      (simp_all add: usubst ok_in_subst_laws)
  have "(AP P ;;\<^sub>D\<^sub>A AP Q) = RA3AP (RA2 ?N')"
    by (rule seq_RA3AP_RA2)
  also have "... = AP ?N'"
    by (rule AP_N[symmetric])
  also have "... = AP (?pre \<turnstile> ?post)"
    by (simp only: desubst)
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
    by (simp only: wf PBMH_ades_ok_in_subst[symmetric] failure
        PBMH_ades_false)
  show "((RA1 \<circ> PBMH_ades) (((true \<turnstile> P) \<^sub>f)\<^sup>t))
      \<lbrakk>True/ok\<^sup><\<rbrakk> =
      (RA1 P)\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp only: wf comp_apply RA1_ok_in_subst
        PBMH_ades_ok_in_subst[symmetric] success
        PBMH_ades_ok_in_subst assms(2))
qed

(* Non-divergent true-precondition instance of the generic sequential
   composition normal form. *)
lemma AP_true_design_seq:
  assumes "(P \<^sub>f) = P" "PBMH_ades P = P"
      "P\<lbrakk>True/ok\<^sup>>\<rbrakk> = P"
    and "(Q \<^sub>f) = Q" "PBMH_ades Q = Q"
      "Q\<lbrakk>True/ok\<^sup>>\<rbrakk> = Q"
  shows "(AP (true \<turnstile> P) ;;\<^sub>D\<^sub>A AP (true \<turnstile> Q)) =
    AP (true \<turnstile>
      (RA1 P ;;\<^sub>A\<^sub>D
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        RA2 (RA1 Q))))"
proof -
  let ?DP = "(true \<turnstile> P)" and ?DQ = "(true \<turnstile> Q)"
  let ?PF = "PBMH_ades ((?DP \<^sub>f)\<^sup>f)"
  let ?PT = "(RA1 \<circ> PBMH_ades) ((?DP \<^sub>f)\<^sup>t)"
  let ?QF = "PBMH_ades ((?DQ \<^sub>f)\<^sup>f)"
  let ?QT = "(RA1 \<circ> PBMH_ades) ((?DQ \<^sub>f)\<^sup>t)"
  let ?pre = "((\<not> (?PF ;;\<^sub>A\<^sub>D true)) \<and>
    (\<not> (?PT ;;\<^sub>A\<^sub>D
      ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?QF))))"
  let ?post = "(?PT ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 ((\<not> ?QF) \<longrightarrow> ?QT)))"
  let ?postND = "(RA1 P ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 Q)))"
  note P_push = true_design_components_ok_in_subst[OF assms(1-3)]
  note Q_push = true_design_components_ok_in_subst[OF assms(4-6)]
  have initial_failure_false:
    "(?PF ;;\<^sub>A\<^sub>D true)\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: ok_in_subst_laws P_push(1)
        aseq_ades_false_left)
  have Qguard_false:
    "(((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?QF))
      \<lbrakk>True/ok\<^sup><\<rbrakk> = false"
    by (simp only: subst_pred ok_in_subst_laws Q_push(1)
        RA2_false pred_ba.inf_bot_right)
  have handover_failure_false:
    "(?PT ;;\<^sub>A\<^sub>D
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
  have "(AP ?DP ;;\<^sub>D\<^sub>A AP ?DQ) = AP (?pre \<turnstile> ?post)"
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
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  assumes "(P \<^sub>f) = P" "PBMH_ades P = P"
    and "P\<lbrakk>True/ok\<^sup>>\<rbrakk> = P"
  shows "(AP (true \<turnstile> P) ;;\<^sub>D\<^sub>A Chaos\<^sub>A\<^sub>P) =
    AP ((\<not> (RA1 P ;;\<^sub>A\<^sub>D (\<not> rad_wait_lens\<^sup><))) \<turnstile>
        (RA1 P ;;\<^sub>A\<^sub>D
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
        PBMH_ades_ok_in_subst[symmetric] Q_comp PBMH_ades_true)
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
  shows "(P ;;\<^sub>D\<^sub>A Q) = AP (
  \<comment> \<open>P's initial, non-waiting precondition holds\<close>
  ((\<not> (((P \<^sub>f)\<^sup>f) ;;\<^sub>A\<^sub>D true)) \<and>
  \<comment> \<open>a successful non-waiting handover from P satisfies Q's precondition\<close>
  (\<not> (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ((Q \<^sub>f)\<^sup>f))))) \<turnstile>
  \<comment> \<open>wait is true: retain P's waiting state through s \<in> ac'\<close>
  (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>D (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
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
  shows "(P ;;\<^sub>D\<^sub>A Q) is AP"
  by (subst AP_seq_design[OF assms]) (rule AP_healthy)

(* Paper Theorem 60 / Thesis Theorem T.6.4.19. *)
theorem RA1_H1_seq_refine:
  assumes "P is RAD" "Q is RAD"
  shows "RA1 (H1 P ;;\<^sub>D\<^sub>A H1 Q) \<sqsubseteq> (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
proof -
  have HP_refine: "H1 P \<sqsubseteq> P"
    and HQ_refine: "H1 Q \<sqsubseteq> Q"
    using RA1_refine[OF H1_RAD_is_PBMH_ades[OF assms(1)]]
      RA1_refine[OF H1_RAD_is_PBMH_ades[OF assms(2)]]
    by (simp_all only:
        RA1_H1_RAD_healthy[OF assms(1), simplified comp_apply]
        RA1_H1_RAD_healthy[OF assms(2), simplified comp_apply])
  have seq_refine:
    "(H1 P ;;\<^sub>D\<^sub>A H1 Q) \<sqsubseteq> (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
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
  shows "(P ;;\<^sub>D\<^sub>A Q) \<sqsubseteq> H1 (RA1 P ;;\<^sub>R\<^sub>A\<^sub>D RA1 Q)"
proof -
  have P_refine: "P \<sqsubseteq> H1 (RA1 P)"
    and Q_refine: "Q \<sqsubseteq> H1 (RA1 Q)"
    using H1_RA1_AP_refine[of P] H1_RA1_AP_refine[of Q]
    by (simp_all only: comp_apply Healthy_if[OF assms(1)]
        Healthy_if[OF assms(2)])
  have linked_seq_refine:
    "(P ;;\<^sub>D\<^sub>A Q) \<sqsubseteq>
      (H1 (RA1 P) ;;\<^sub>D\<^sub>A H1 (RA1 Q))"
    by (rule angelic_design_seq_mono[
          OF AP_is_PBMH_ades[OF assms(1)] P_refine Q_refine])
  have RA1_P_RAD: "RA1 P is RAD"
    and RA1_Q_RAD: "RA1 Q is RAD"
    using RA1_AP_RAD[of P] RA1_AP_RAD[of Q]
    by (simp_all only: comp_apply Healthy_if[OF assms(1)]
        Healthy_if[OF assms(2)] RAD_healthy)
  have seq_RA1_refine:
    "RA1 (P ;;\<^sub>D\<^sub>A Q) \<sqsubseteq>
      (RA1 P ;;\<^sub>R\<^sub>A\<^sub>D RA1 Q)"
    by (rule ref_by_trans[
          OF RA1_mono[OF linked_seq_refine]
          RA1_H1_seq_refine[OF RA1_P_RAD RA1_Q_RAD]])
  have seq_refine:
    "(P ;;\<^sub>D\<^sub>A Q) \<sqsubseteq>
      H1 (RA1 (P ;;\<^sub>D\<^sub>A Q))"
    using H1_RA1_AP_refine[of "P ;;\<^sub>D\<^sub>A Q"]
    by (simp only: comp_apply Healthy_if[OF AP_seq_closure[OF assms]])
  show ?thesis
    by (rule ref_by_trans[
          OF seq_refine H1_monotone[OF seq_RA1_refine]])
qed

(* Paper Theorem 62 / Thesis Theorem T.6.4.21. *)
theorem RA1_H1_seq:
  assumes "P is RAD" "Q is RAD" "P is NDRAD" "Q is NDRAD"
  shows "RA1 (H1 P ;;\<^sub>D\<^sub>A H1 Q) = (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
proof -
  let ?Pt = "(P \<^sub>f)\<^sup>t" and ?Qt = "(Q \<^sub>f)\<^sup>t"
  let ?post = "(RA1 ?Pt ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ?Qt)))"
  note Pt_facts = RAD_wf_ok_true_facts[OF assms(1)]
  note Qt_facts = RAD_wf_ok_true_facts[OF assms(2)]
  have post_wf: "(?post \<^sub>f) = ?post"
    by (simp only: rad_wait_false_aseq_ades
        rad_wait_false_RA1_commute Pt_facts(1))
  have post_PBMH: "?post is PBMH_ades"
    by (intro aseq_ades_PBMH_ades_closure
        RA1_PBMH_ades_closure rad_wait_cond_PBMH_ades_closure
        ades_state_choice_is_PBMH_ades RA2_PBMH_ades_closure
        RAD_wf_ok_true_PBMH[OF assms(1)]
        RAD_wf_ok_true_PBMH[OF assms(2)])
  have post_unrest: "$ok\<^sup>> \<sharp> ?post"
    by (simp add: unrest)
  have post_ok: "?post\<lbrakk>True/ok\<^sup>>\<rbrakk> = ?post"
    using post_unrest by (simp add: unrest usubst)
  have linked_seq:
    "(H1 P ;;\<^sub>D\<^sub>A H1 Q) = AP (true \<turnstile> ?post)"
    by (simp only: H1_NDRAD_AP_true_design[OF assms(1,3)]
        H1_NDRAD_AP_true_design[OF assms(2,4)]
        AP_true_design_seq[OF Pt_facts Qt_facts])
  have "RA1 (H1 P ;;\<^sub>D\<^sub>A H1 Q) = RA (true \<turnstile> ?post)"
    by (simp only: linked_seq
        RA1_AP_true_design[OF post_wf Healthy_if[OF post_PBMH] post_ok])
  also have "... = (RA \<circ> A) (true \<turnstile> ?post)"
    by (rule RA_A_absorb_design_true[OF post_PBMH post_unrest,
          symmetric])
  also have "... = (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
    by (rule NDRAD_seq_design[OF assms, symmetric])
  finally show ?thesis .
qed

subsection \<open>Prefixing\<close>

(* TODO: Generalise prefixing to arbitrary trace algebras equipped with an
   event-to-trace embedding; the current list instance maps a to [a]. *)

(* Paper Definition 57 / Thesis Definition 138. *)
definition PrefixSkip_AP :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design" where
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
   abbreviates (a \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) ;;\<^sub>D\<^sub>A P; its
   Theorem T.6.4.23 normal form instances are in
   \<open>utp_ap_examples\<close>. *)
definition Prefix_AP ::
  "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
   ('e list, 'e) reactive_angelic_design"
  (infixr "\<rightarrow>\<^sub>A\<^sub>P" 80) where
[pred]: "Prefix_AP a P = (PrefixSkip_AP a ;;\<^sub>D\<^sub>A P)"

lemma Prefix_AP_closure [closure]:
  assumes "P is AP"
  shows "(a \<rightarrow>\<^sub>A\<^sub>P P) is AP"
  unfolding Prefix_AP_def
  by (rule AP_seq_closure[OF PrefixSkip_AP_is_AP assms])

end
