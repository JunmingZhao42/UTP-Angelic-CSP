section \<open>Angelic Processes\<close>

theory utp_ap_healthy
  imports "UTP-Reactive-Angelic-Designs.utp_rad"
begin

subsection \<open>Healthiness Conditions\<close>

subsubsection \<open>The identity of angelic processes\<close>

(* Paper Definition 47: II_AP = H1 (ok' \<and> s \<in> ac'). *)
definition II_AP :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "II_AP = H1 (ok\<^sup>> \<and> ades_state_choice)"

lemma II_AP_is_H1 [closure]: "II_AP is H1"
  by (simp add: Healthy_def II_AP_def H1_idem)

(* The identity of angelic processes is a design. *)
lemma II_AP_design:
  "II_AP = (true \<turnstile> ades_state_choice)"
  by pred_auto

lemma RA2_II_AP: "RA2 II_AP = II_AP"
  by (simp only: II_AP_design RA2_design_distrib RA2_true
      RA2_state_choice)

lemma II_AP_is_RA2 [closure]: "II_AP is RA2"
  by (rule Healthy_intro, rule RA2_II_AP)

subsubsection \<open>RA3AP: Waiting\<close>

(* Paper Definition 48: RA3AP (P) = II_AP \<triangleleft> s.wait \<triangleright> P. *)
definition RA3AP :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA3AP P = (II_AP \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)"

lemma RA3AP_idem: "RA3AP (RA3AP P) = RA3AP P"
  by (simp add: RA3AP_def)

lemma RA3AP_Idempotent [closure]: "Idempotent RA3AP"
  by (simp add: Idempotent_def RA3AP_idem)

lemma RA3AP_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA3AP P \<sqsubseteq> RA3AP Q"
  by (simp add: RA3AP_def, pred_auto)

lemma RA3AP_Monotonic [closure]: "Monotonic RA3AP"
  by (rule MonotonicI, rule RA3AP_mono)

lemma RA3AP_conj: "RA3AP (P \<and> Q) = (RA3AP P \<and> RA3AP Q)"
  by (simp add: RA3AP_def expr_if_def fun_eq_iff; pred_auto)

lemma RA3AP_II_AP: "RA3AP II_AP = II_AP"
  by (simp add: RA3AP_def)

lemma II_AP_is_RA3AP [closure]: "II_AP is RA3AP"
  by (rule Healthy_intro, rule RA3AP_II_AP)

(* Thesis Theorem T.6.2.7. *)
lemma RA2_RA3AP_commute: "(RA2 \<circ> RA3AP) P = (RA3AP \<circ> RA2) P"
  by (simp only: comp_apply RA3AP_def RA2_wait_cond RA2_II_AP)

(* RA3AP depends only on the wait-false part of its argument
   (cf. paper Lemma 19 for RA3). *)
lemma RA3AP_wait_false_absorb: "RA3AP P = (RA3AP \<circ> rad_wait_false) P"
  apply (simp add: RA3AP_def rad_wait_false_def expr_if_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def)
  apply clarify
  subgoal for a b
    by (cases "astate.s\<^sub>v (des_vars.more a)";
        cases "des_vars.more a"; cases a;
        simp add: lens_defs rad_state.wait_def astate.s_def
          des_vars.more\<^sub>L_def)
  done

(* The wait-false substitution discards the wait-true branch of a
   conditional. *)
lemma rad_wait_false_wait_cond:
  "rad_wait_false
     (X \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Y) =
   rad_wait_false Y"
  by (simp add: rad_wait_false_def expr_if_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemma rad_wait_false_RA3AP_absorb:
  "rad_wait_false (RA3AP P) = rad_wait_false P"
  by (simp only: RA3AP_def rad_wait_false_wait_cond)

(* Under RA3AP \<circ> RA2 \<circ> A, the wait-false substitution of the
   argument is redundant. *)
lemma RA3AP_RA2_A_wait_false_absorb:
  "(RA3AP \<circ> RA2 \<circ> A \<circ> rad_wait_false) P =
   (RA3AP \<circ> RA2 \<circ> A) P"
proof -
  have "RA3AP (RA2 (A (rad_wait_false P))) =
      RA2 (RA3AP (A (rad_wait_false P)))"
    by (simp only: RA2_RA3AP_commute[simplified comp_apply,
          symmetric])
  also have "... = RA2 (RA3AP (A P))"
    by (simp only: rad_wait_false_A_commute[simplified comp_apply,
          symmetric]
        RA3AP_wait_false_absorb[simplified comp_apply, symmetric])
  also have "... = RA3AP (RA2 (A P))"
    by (simp only: RA2_RA3AP_commute[simplified comp_apply])
  finally show ?thesis
    by (simp only: comp_apply)
qed

lemmas RA3AP_RA2_A_wait_false_absorb' =
  RA3AP_RA2_A_wait_false_absorb[simplified comp_apply]

(* Thesis Lemma L.H.1.4: RA3AP turns a design into wait conditionals
   over its components. *)
lemma RA3AP_design:
  "RA3AP (P \<turnstile> Q) =
   ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P) \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
  by (simp only: RA3AP_def II_AP_design design_wait_cond)

(* Under RA1, the two waiting conditions agree: RA1 turns the angelic
   identity II_AP into the reactive angelic one, II_Rac. *)
lemma RA1_RA3AP_RA3: "RA1 (RA3AP P) = RA1 (RA3 P)"
  by (simp only: RA3AP_def RA3_def RA1_wait_cond II_AP_design
      II_Rac_design[symmetric] RA1_II_Rac)

(* Inside a design, RA3AP on the postcondition is the state-choice wait
   conditional: the identity II_AP collapses under the assumed ok. *)
lemma RA3AP_design_post:
  "(Pre \<turnstile> RA3AP Q) =
   (Pre \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
  by (simp add: RA3AP_def II_AP_def H1_def design_def expr_if_def
      fun_eq_iff; pred_auto)

(* On a design with a true precondition, RA3AP may equivalently be
   applied to the postcondition alone. *)
lemma RA3AP_true_design:
  "RA3AP (true \<turnstile> Y) = (true \<turnstile> RA3AP Y)"
  by (simp only: RA3AP_design_post RA3AP_design expr_if_idem)

subsubsection \<open>AP\<close>

(* Paper Definition 46: AP = RA3AP \<circ> RA2 \<circ> A \<circ> H1 \<circ> CSPA2. *)
definition AP ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "AP = RA3AP \<circ> RA2 \<circ> A \<circ> H1 \<circ> CSPA2"

lemma AP_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> AP P \<sqsubseteq> AP Q"
  by (simp add: AP_def RA3AP_mono RA2_mono A_mono
      H1_monotone CSPA2_mono)

lemma AP_Monotonic [closure]: "Monotonic AP"
  by (rule MonotonicI, rule AP_mono)

(* Paper Theorem 36 / Thesis Theorem T.6.2.8. *)
theorem AP_design_form:
  "AP P = (RA3AP \<circ> RA2 \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  have "AP P = RA2 (RA3AP (A (H1 (H2 P))))"
    by (simp only: AP_def CSPA2_def comp_apply
        RA2_RA3AP_commute[simplified comp_apply, symmetric])
  also have "... = RA2 (RA3AP (A (H1 (H2 (P \<^sub>wf)))))"
    by (simp only: RA3AP_wait_false_absorb[simplified comp_apply,
          of "A (H1 (H2 P))"]
        rad_wait_false_A_commute[simplified comp_apply]
        rad_wait_false_H1_H2_commute[simplified comp_apply])
  also have "... = RA3AP (RA2 (A (H1 (H2 (P \<^sub>wf)))))"
    by (simp only: RA2_RA3AP_commute[simplified comp_apply])
  finally show ?thesis
    by (simp add: H1_H2_eq_design)
qed

(* Paper Theorem 37 / Thesis Theorem T.6.2.9: angelic processes form a
   theory of angelic designs. *)
theorem AP_design:
  "AP P =
   ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       (\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f))) \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t)))"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f" and ?T = "(P \<^sub>wf)\<^sup>t"
  have "AP P = RA3AP (RA2 (A ((\<not> ?F) \<turnstile> ?T)))"
    by (simp only: AP_design_form comp_apply)
  also have "... =
      RA3AP ((\<not> RA2 (PBMH_ades ?F)) \<turnstile>
             (RA2 (RA1 (PBMH_ades ?T))))"
    by (simp only: A_design RA2_design_distrib RA2_not
        RA2_ac_non_empty)
  also have "... =
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          (\<not> RA2 (PBMH_ades ?F))) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          (RA2 (RA1 (PBMH_ades ?T)))))"
    by (rule RA3AP_design)
  finally show ?thesis
    by (simp only: comp_apply)
qed

(* The Theorem 37 normal form with the wait conditionals folded back
   into RA3AP. *)
lemma AP_RA3AP_design:
  "AP P =
   RA3AP ((\<not> RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f))) \<turnstile>
          RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t))))"
  by (simp only: AP_design RA3AP_design comp_apply)

(* The wait-conditional normal form of an angelic process with a true
   precondition: the counterpart of RA_true_design. *)
lemma AP_true_design:
  assumes "(Post \<^sub>wf) = Post" "PBMH_ades Post = Post"
    and "Post\<lbrakk>True/ok\<^sup>>\<rbrakk> = Post"
  shows "AP (true \<turnstile> Post) =
    (true \<turnstile>
     (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA1 (RA2 Post)))"
proof -
  let ?P = "(true \<turnstile> Post)"
  have wf_id: "(?P \<^sub>wf) = ?P"
    by (simp only: rad_wait_false_design rad_wait_false_true assms(1))
  have proj_f: "?P\<^sup>f = (\<not> ok\<^sup><)"
    by pred_auto
  have proj_t_raw:
      "?P\<^sup>t = ((\<not> ok\<^sup><) \<or> Post\<lbrakk>True/ok\<^sup>>\<rbrakk>)"
    by pred_auto
  have proj_t: "?P\<^sup>t = ((\<not> ok\<^sup><) \<or> Post)"
    by (simp only: proj_t_raw assms(3))
  have pre_ok: "((\<not> (\<not> ok\<^sup><)) \<turnstile> T) = (true \<turnstile> T)"
      for T :: "('t, 'e) reactive_angelic_design"
    by pred_auto

  have "AP ?P =
      RA3AP ((\<not> RA2 (PBMH_ades (\<not> ok\<^sup><))) \<turnstile>
             RA2 (RA1 (PBMH_ades ((\<not> ok\<^sup><) \<or> Post))))"
    by (simp only: AP_RA3AP_design wf_id proj_f proj_t)
  also have "... =
      RA3AP ((\<not> (\<not> ok\<^sup><)) \<turnstile>
             RA1 ((\<not> ok\<^sup><) \<or> RA2 Post))"
    by (simp only: PBMH_ades_disj PBMH_ades_not_ok_expr assms(2)
        RA2_not_ok_expr RA1_RA2_commute'[symmetric] RA2_disj)
  also have "... = RA3AP (true \<turnstile> RA1 (RA2 Post))"
    by (simp only: pre_ok design_true_RA1_not_ok)
  finally show ?thesis
    by (simp only: RA3AP_design expr_if_idem)
qed

(* Thesis Lemma L.H.1.5. *)
lemma AP_wait_false:
  "rad_wait_false (AP P) =
   ((\<not> rad_wait_false ((RA2 \<circ> PBMH_ades)
       ((P \<^sub>wf)\<^sup>f))) \<turnstile>
     rad_wait_false ((RA2 \<circ> RA1 \<circ> PBMH_ades)
       ((P \<^sub>wf)\<^sup>t)))"
  by (simp only: AP_design rad_wait_false_design
      rad_wait_false_wait_cond rad_wait_false_not
      rad_wait_false_idem rad_wait_false_ok_false
      rad_wait_false_ok_true)

(* Thesis Lemma L.H.1.6. *)
lemma AP_wait_false_ok_false:
  "(rad_wait_false (AP P))\<^sup>f =
   (ok\<^sup>< \<longrightarrow>
     rad_wait_false ((RA2 \<circ> PBMH_ades)
       ((P \<^sub>wf)\<^sup>f)))"
  by (simp add: AP_wait_false design_def; pred_auto)

(* Thesis Lemma L.H.1.7. *)
lemma AP_wait_false_ok_true:
  "(rad_wait_false (AP P))\<^sup>t =
   ((ok\<^sup>< \<and>
     \<not> rad_wait_false ((RA2 \<circ> PBMH_ades)
       ((P \<^sub>wf)\<^sup>f))) \<longrightarrow>
     rad_wait_false ((RA2 \<circ> RA1 \<circ> PBMH_ades)
       ((P \<^sub>wf)\<^sup>t)))"
  by (simp add: AP_wait_false design_def; pred_auto)

(* PBMH_ades preserves freshness of the final ok, completing the [unrest]
   kit of RA1_unrest_ok_out and RA2_unrest_ok_out.  Kept here instead of the
   ades layer so the parent session heaps stay valid. *)
lemma PBMH_ades_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> PBMH_ades P"
  by (simp add: unrest_lens PBMH_ades_def PBMH_def pbmh_step_def
      fun_eq_iff Let_def; pred_auto; blast)

(* An RA1 image under RA2 keeps the angelic choice set non-empty. *)
lemma RA2_RA1_ac_non_empty_absorb:
  "(ac_non_empty \<and> RA2 (RA1 P)) = RA2 (RA1 P)"
proof -
  have "(ac_non_empty \<and> RA1 Q) = RA1 Q"
      for Q :: "('t::trace, 'e) reactive_angelic_design"
    by (simp add: RA1_def ac_non_empty_def fun_eq_iff Let_def;
        pred_auto)
  then show ?thesis
    by (simp only: RA1_RA2_commute'[symmetric])
qed

(* A0 is a fixed point on designs whose postcondition keeps the choice
   set non-empty. *)
lemma A0_design_absorb:
  "$ok\<^sup>> \<sharp> X \<Longrightarrow> (ac_non_empty \<and> Y) = Y \<Longrightarrow>
   A0 ((\<not> X) \<turnstile> Y) = ((\<not> X) \<turnstile> Y)"
  by (simp add: A0_def unrest; pred_auto; blast)

subsubsection \<open>The design body of the AP normal form\<close>

(* The design inside RA3AP in the Theorem 37 normal form is a fixed
   point of the component healthiness conditions of AP. *)
lemma AP_body_is_H [closure]:
  "((\<not> RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f))) \<turnstile>
    RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t)))) is \<^bold>H"
  by (rule design_is_H1_H2; unrest)

lemma AP_body_is_A [closure]:
  "((\<not> RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f))) \<turnstile>
    RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t)))) is A"
proof -
  let ?F = "RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f))"
  let ?T = "RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t)))"
  let ?N = "((\<not> ?F) \<turnstile> ?T)"
  have F_unrest: "$ok\<^sup>> \<sharp> ?F"
    by (unrest)
  have F_PBMH: "?F is PBMH_ades"
    by (rule RA2_PBMH_ades_closure[OF
        Healthy_Idempotent[OF PBMH_ades_Idempotent]])
  have T_PBMH: "?T is PBMH_ades"
    by (rule RA2_PBMH_ades_closure[OF
        RA1_PBMH_ades_closure[OF
          Healthy_Idempotent[OF PBMH_ades_Idempotent]]])
  have A1_fixed: "A1 ?N = ?N"
    using A1_eq_PBMH_ades[OF AP_body_is_H[of P]]
      PBMH_ades_design_closure[OF F_PBMH T_PBMH]
    by (simp add: Healthy_def')
  show ?thesis
    by (rule Healthy_intro,
        simp only: A_def A1_fixed
          A0_design_absorb[OF F_unrest RA2_RA1_ac_non_empty_absorb])
qed

lemma AP_body_is_RA2 [closure]:
  "((\<not> RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f))) \<turnstile>
    RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t)))) is RA2"
  by (rule Healthy_intro,
      simp only: RA2_design_distrib RA2_not RA2_idem
        RA1_RA2_commute'[symmetric])

(* RA3AP images of A- and RA2-healthy designs are angelic processes. *)
lemma RA3AP_AP_closure [closure]:
  assumes "N is A" "N is RA2"
  shows "RA3AP N is AP"
proof -
  have N_H: "N is \<^bold>H"
    using A_is_H[of N] assms(1) by (simp add: Healthy_def')
  have reform: "((\<not> (N\<^sup>f)) \<turnstile> (N\<^sup>t)) = N"
  proof -
    have "((\<not> (N\<^sup>f)) \<turnstile> (N\<^sup>t)) = \<^bold>H N"
      by (rule sym, rule H1_H2_eq_design)
    also have "... = N"
      using N_H by (simp only: Healthy_def')
    finally show ?thesis .
  qed
  have "AP (RA3AP N) =
      (RA3AP \<circ> RA2 \<circ> A)
        ((\<not> ((RA3AP N) \<^sub>wf)\<^sup>f) \<turnstile>
         ((RA3AP N) \<^sub>wf)\<^sup>t)"
    by (rule AP_design_form)
  also have "... =
      (RA3AP \<circ> RA2 \<circ> A)
        (rad_wait_false ((\<not> (N\<^sup>f)) \<turnstile> (N\<^sup>t)))"
    by (simp only: rad_wait_false_RA3AP_absorb
        rad_wait_false_design rad_wait_false_not
        rad_wait_false_ok_false rad_wait_false_ok_true)
  also have "... = (RA3AP \<circ> RA2 \<circ> A) (rad_wait_false N)"
    by (simp only: reform)
  also have "... = RA3AP (RA2 (A N))"
    by (simp only: comp_apply RA3AP_RA2_A_wait_false_absorb')
  also have "... = RA3AP N"
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])
  finally show ?thesis
    by (rule Healthy_intro)
qed

lemma AP_idem: "AP (AP P) = AP P"
proof -
  let ?N = "((\<not> RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f))) \<turnstile>
             RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t))))"
  have "AP (AP P) = AP (RA3AP ?N)"
    by (simp only: AP_RA3AP_design)
  also have "... = RA3AP ?N"
    by (rule Healthy_if[OF RA3AP_AP_closure[OF
        AP_body_is_A AP_body_is_RA2]])
  also have "... = AP P"
    by (simp only: AP_RA3AP_design)
  finally show ?thesis .
qed

lemma AP_Idempotent [closure]: "Idempotent AP"
  by (simp add: Idempotent_def AP_idem)

lemma AP_healthy [closure]: "AP P is AP"
  by (simp add: Healthy_def' AP_idem)

end
