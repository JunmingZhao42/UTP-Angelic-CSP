section \<open>Angelic Processes\<close>

theory utp_ap_healthy
  imports "UTP-Reactive-Angelic-Designs.utp_rad"
begin

subsection \<open>The Identity of Angelic Processes\<close>

(* Paper Definition 47: II_AP \<equiv> H1 (ok' \<and> s \<in> ac'). *)
definition II_AP :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "II_AP = H1 (ok\<^sup>> \<and> ades_state_choice)"

lemma II_AP_is_H1 [closure]: "II_AP is H1"
  by (simp add: Healthy_def II_AP_def H1_idem)

lemma II_AP_design:
  "II_AP = (true \<turnstile> ades_state_choice)"
  by pred_auto

lemma RA2_II_AP: "RA2 II_AP = II_AP"
  by (simp only: II_AP_design RA2_design_distrib RA2_true
      RA2_state_choice)

lemma II_AP_is_RA2 [closure]: "II_AP is RA2"
  by (rule Healthy_intro, rule RA2_II_AP)

lemma II_AP_is_PBMH_ades [closure]: "II_AP is PBMH_ades"
  by (simp add: Healthy_def' II_AP_design PBMH_ades_def design_def
      fun_eq_iff; pred_auto; blast)

subsection \<open>RA3AP: Waiting\<close>

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

lemma RA3AP_disj: "RA3AP (P \<or> Q) = (RA3AP P \<or> RA3AP Q)"
  by (simp add: RA3AP_def expr_if_def fun_eq_iff; pred_auto)

lemma RA3AP_II_AP: "RA3AP II_AP = II_AP"
  by (simp add: RA3AP_def)

lemma II_AP_is_RA3AP [closure]: "II_AP is RA3AP"
  by (rule Healthy_intro, rule RA3AP_II_AP)

lemma RA3AP_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "RA3AP P is PBMH_ades"
  unfolding RA3AP_def
  by (rule rad_wait_cond_PBMH_ades_closure[OF II_AP_is_PBMH_ades assms])

(* Thesis Theorem T.6.2.7. *)
lemma RA2_RA3AP_commute: "(RA2 \<circ> RA3AP) P = (RA3AP \<circ> RA2) P"
  by (simp only: comp_apply RA3AP_def RA2_wait_cond RA2_II_AP)

(* Cf. paper Lemma 19 for RA3. *)
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

lemma rad_wait_false_wait_cond:
  "rad_wait_false
     (X \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Y) =
   rad_wait_false Y"
  by (simp add: rad_wait_false_def expr_if_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemma rad_wait_false_RA3AP_absorb:
  "(rad_wait_false \<circ> RA3AP) P = rad_wait_false P"
  by (simp only: comp_apply RA3AP_def rad_wait_false_wait_cond)

lemma RA3AP_RA2_A_wait_false_absorb:
  "(RA3AP \<circ> RA2 \<circ> A \<circ> rad_wait_false) P =
   (RA3AP \<circ> RA2 \<circ> A) P"
proof -
  have "(RA3AP \<circ> RA2 \<circ> A \<circ> rad_wait_false) P =
      (RA2 \<circ> RA3AP \<circ> A \<circ> rad_wait_false) P"
    by (simp only: comp_apply RA2_RA3AP_commute[simplified comp_apply,
          symmetric])
  also have "... = (RA2 \<circ> RA3AP \<circ> A) P"
    by (simp only: rad_wait_false_A_commute[simplified comp_apply,
          symmetric]
        RA3AP_wait_false_absorb[simplified comp_apply, symmetric]
        comp_apply)
  also have "... = (RA3AP \<circ> RA2 \<circ> A) P"
    by (simp only: comp_apply RA2_RA3AP_commute[simplified comp_apply])
  finally show ?thesis .
qed

lemmas RA3AP_RA2_A_wait_false_absorb' =
  RA3AP_RA2_A_wait_false_absorb[simplified comp_apply]

(* Thesis Lemma L.H.1.4. *)
lemma RA3AP_design:
  "RA3AP (P \<turnstile> Q) =
   ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P) \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
  by (simp only: RA3AP_def II_AP_design design_wait_cond)

(* Under RA1 the waiting conditions agree: RA1 II_AP = II_Rac. *)
lemma RA1_RA3AP_RA3: "(RA1 \<circ> RA3AP) P = (RA1 \<circ> RA3) P"
  by (simp only: comp_apply RA3AP_def RA3_def RA1_wait_cond II_AP_design
      II_Rac_design[symmetric] RA1_II_Rac)

(* II_AP collapses to ades_state_choice under the design's ok. *)
lemma RA3AP_design_post:
  "(P \<turnstile> RA3AP Q) =
   (P \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
  by (simp add: RA3AP_def II_AP_def H1_def design_def expr_if_def
      fun_eq_iff; pred_auto)

lemma RA3AP_true_design:
  "RA3AP (true \<turnstile> Y) = (true \<turnstile> RA3AP Y)"
  by (simp only: RA3AP_design_post RA3AP_design expr_if_idem)

subsection \<open>AP\<close>

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
  "AP P = (RA3AP \<circ> RA2 \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)"
proof -
  have "AP P = (RA2 \<circ> RA3AP \<circ> A \<circ> H1 \<circ> H2) P"
    by (simp only: AP_def CSPA2_def comp_apply
        RA2_RA3AP_commute[simplified comp_apply, symmetric])
  also have "... = (RA2 \<circ> RA3AP \<circ> A \<circ> H1 \<circ> H2) (P \<^sub>f)"
    by (simp only: comp_apply RA3AP_wait_false_absorb[simplified comp_apply,
          of "A (H1 (H2 P))"]
        rad_wait_false_A_commute[simplified comp_apply]
        rad_wait_false_H1_H2_commute[simplified comp_apply])
  also have "... = (RA3AP \<circ> RA2 \<circ> A \<circ> H1 \<circ> H2) (P \<^sub>f)"
    by (simp only: comp_apply RA2_RA3AP_commute[simplified comp_apply])
  finally show ?thesis
    by (simp add: H1_H2_eq_design)
qed

(* Paper Theorem 37 / Thesis Theorem T.6.2.9 *)
theorem AP_wait_cond_design:
  "AP P = ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f))) \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)))"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  have "AP P = (RA3AP \<circ> RA2 \<circ> A) ((\<not> ?F) \<turnstile> ?T)"
    by (simp only: AP_design_form comp_apply)
  also have "... =
      RA3AP ((\<not> (RA2 \<circ> PBMH_ades) ?F) \<turnstile>
             ((RA2 \<circ> RA1 \<circ> PBMH_ades) ?T))"
    by (simp only: comp_apply A_design RA2_design_distrib RA2_not
        RA2_ac_non_empty)
  also have "... =
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          (\<not> (RA2 \<circ> PBMH_ades) ?F)) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          ((RA2 \<circ> RA1 \<circ> PBMH_ades) ?T)))"
    by (rule RA3AP_design)
  finally show ?thesis .
qed

(* Theorem 37 with the wait conditionals folded into RA3AP. *)
lemma AP_RA3AP_design:
  "AP P = RA3AP ((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
          (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t))"
  by (simp only: AP_wait_cond_design RA3AP_design comp_apply)

(* Counterpart of RA_true_design. *)
lemma AP_true_design:
  assumes "(Q \<^sub>f) = Q" "PBMH_ades Q = Q"
    and "Q\<lbrakk>True/ok\<^sup>>\<rbrakk> = Q"
  shows "AP (true \<turnstile> Q) =
    (true \<turnstile>
     (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA1 (RA2 Q)))"
proof -
  have f: "(true \<turnstile> Q)\<^sup>f = (\<not> ok\<^sup><)"
    and t_raw: "(true \<turnstile> Q)\<^sup>t =
      ((\<not> ok\<^sup><) \<or> Q\<lbrakk>True/ok\<^sup>>\<rbrakk>)"
    by pred_auto+
  have pre_ok: "((\<not> (\<not> ok\<^sup><)) \<turnstile> T) = (true \<turnstile> T)"
      for T :: "('t, 'e) reactive_angelic_design"
    by pred_auto
  show ?thesis
    by (simp only: AP_RA3AP_design comp_apply rad_wait_false_design
        rad_wait_false_true assms(1) f t_raw assms(3)
        PBMH_ades_disj PBMH_ades_not_ok_expr assms(2)
        RA2_not_ok_expr RA1_RA2_commute'[symmetric] RA2_disj
        pre_ok design_true_RA1_not_ok RA3AP_design expr_if_idem)
qed

(* Thesis Lemma L.H.1.5. *)
lemma AP_wait_false:
  "rad_wait_false (AP P) =
   ((\<not> rad_wait_false ((RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f))) \<turnstile>
     rad_wait_false ((RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)))"
  by (simp only: AP_wait_cond_design rad_wait_false_design
      rad_wait_false_wait_cond rad_wait_false_not
      rad_wait_false_idem rad_wait_false_ok_false
      rad_wait_false_ok_true)

(* Thesis Lemma L.H.1.6. *)
lemma AP_wait_false_ok_false:
  "(rad_wait_false (AP P))\<^sup>f =
   (ok\<^sup>< \<longrightarrow> rad_wait_false ((RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)))"
  by (simp add: AP_wait_false design_def; pred_auto)

(* Thesis Lemma L.H.1.7. *)
lemma AP_wait_false_ok_true:
  "(rad_wait_false (AP P))\<^sup>t =
   ((ok\<^sup>< \<and> \<not> rad_wait_false ((RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f))) \<longrightarrow>
     rad_wait_false ((RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)))"
  by (simp add: AP_wait_false design_def; pred_auto)

(* Kept here instead of the ades layer so the parent session heaps
   stay valid. *)
lemma PBMH_ades_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> PBMH_ades P"
  by (simp add: unrest_lens PBMH_ades_def PBMH_def pbmh_step_def
      fun_eq_iff Let_def; pred_auto; blast)

lemma RA2_RA1_ac_non_empty_absorb:
  "(ac_non_empty \<and> (RA2 \<circ> RA1) P) = (RA2 \<circ> RA1) P"
proof -
  have "(ac_non_empty \<and> RA1 Q) = RA1 Q"
      for Q :: "('t::trace, 'e) reactive_angelic_design"
    by (simp add: RA1_def ac_non_empty_def fun_eq_iff Let_def;
        pred_auto)
  then show ?thesis
    by (simp only: comp_apply RA1_RA2_commute'[symmetric])
qed

lemma A0_design_absorb:
  "$ok\<^sup>> \<sharp> X \<Longrightarrow> (ac_non_empty \<and> Y) = Y \<Longrightarrow>
   A0 ((\<not> X) \<turnstile> Y) = ((\<not> X) \<turnstile> Y)"
  by (simp add: A0_def unrest; pred_auto; blast)

subsection \<open>Idempotence of AP\<close>

(* The design inside RA3AP in the Theorem 37 normal form is a fixed
   point of each component healthiness condition of AP, so RA3AP images
   of A- and RA2-healthy designs are angelic processes and AP is
   idempotent. *)
lemma AP_body_is_H [closure]:
  "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
    (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)) is \<^bold>H"
  by (rule design_is_H1_H2; unrest)

lemma AP_body_is_A [closure]:
  "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
    (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)) is A"
proof -
  let ?F = "(RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)"
    and ?T = "(RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)"
  let ?N = "((\<not> ?F) \<turnstile> ?T)"
  have F_unrest: "$ok\<^sup>> \<sharp> ?F"
    by (unrest)
  have F_PBMH: "?F is PBMH_ades"
    by (simp only: comp_apply,
        rule RA2_PBMH_ades_closure[OF
          Healthy_Idempotent[OF PBMH_ades_Idempotent]])
  have T_PBMH: "?T is PBMH_ades"
    by (simp only: comp_apply,
        rule RA2_PBMH_ades_closure[OF
          RA1_PBMH_ades_closure[OF
            Healthy_Idempotent[OF PBMH_ades_Idempotent]]])
  have A1_fixed: "A1 ?N = ?N"
    using A1_eq_PBMH_ades[OF AP_body_is_H[of P]]
      PBMH_ades_design_closure[OF F_PBMH T_PBMH]
    by (simp add: Healthy_def')
  have T_ac: "(ac_non_empty \<and> ?T) = ?T"
    by (simp only: comp_apply
        RA2_RA1_ac_non_empty_absorb[simplified comp_apply])
  show ?thesis
    by (rule Healthy_intro,
        simp only: A_def A1_fixed A0_design_absorb[OF F_unrest T_ac])
qed

lemma AP_body_is_RA2 [closure]:
  "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
    (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)) is RA2"
  by (rule Healthy_intro,
      simp only: comp_apply RA2_design_distrib RA2_not RA2_idem
        RA1_RA2_commute'[symmetric])

lemma RA3AP_AP_closure [closure]:
  assumes "N is A" "N is RA2"
  shows "RA3AP N is AP"
proof -
  have reform: "((\<not> (N\<^sup>f)) \<turnstile> (N\<^sup>t)) = N"
    using A_is_H[of N] assms(1)
    by (simp add: Healthy_def' H1_H2_eq_design)
  have "AP (RA3AP N) =
      (RA3AP \<circ> RA2 \<circ> A)
        (rad_wait_false ((\<not> (N\<^sup>f)) \<turnstile> (N\<^sup>t)))"
    by (simp only: AP_design_form
        rad_wait_false_RA3AP_absorb[simplified comp_apply]
        rad_wait_false_design rad_wait_false_not
        rad_wait_false_ok_false rad_wait_false_ok_true)
  also have "... = RA3AP N"
    by (simp only: reform comp_apply RA3AP_RA2_A_wait_false_absorb'
        Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])
  finally show ?thesis
    by (rule Healthy_intro)
qed

lemma AP_idem: "AP (AP P) = AP P"
  by (rule Healthy_if, subst AP_RA3AP_design[of P],
      rule RA3AP_AP_closure, rule AP_body_is_A, rule AP_body_is_RA2)

lemma AP_Idempotent [closure]: "Idempotent AP"
  by (simp add: Idempotent_def AP_idem)

lemma AP_healthy [closure]: "AP P is AP"
  by (simp add: Healthy_def' AP_idem)

subsection \<open>Inherited Healthiness\<close>

lemma AP_PBMH_ades_healthy [closure]: "AP P is PBMH_ades"
  apply (simp only: AP_RA3AP_design)
  apply (rule RA3AP_PBMH_ades_closure)
  apply (rule PBMH_ades_design_closure)
   apply (simp only: comp_apply,
      rule RA2_PBMH_ades_closure,
      rule Healthy_Idempotent[OF PBMH_ades_Idempotent])
  apply (simp only: comp_apply,
      rule RA2_PBMH_ades_closure,
      rule RA1_PBMH_ades_closure,
      rule Healthy_Idempotent[OF PBMH_ades_Idempotent])
  done

lemma AP_is_PBMH_ades:
  assumes "P is AP"
  shows "P is PBMH_ades"
  using AP_PBMH_ades_healthy[of P]
  by (simp only: Healthy_def' Healthy_if[OF assms])

lemma AP_H_healthy [closure]: "AP P is \<^bold>H"
  by (simp only: AP_wait_cond_design,
      rule design_is_H1_H2; unrest)

lemma AP_is_H:
  assumes "P is AP"
  shows "P is \<^bold>H"
  using AP_H_healthy[of P]
  by (simp only: Healthy_def' Healthy_if[OF assms])

lemma AP_wait_false_PBMH_ades:
  assumes "P is AP"
  shows "(P \<^sub>f) is PBMH_ades"
proof -
  have P_H: "P is \<^bold>H"
    by (rule AP_is_H[OF assms])
  have P_PBMH: "PBMH_ades P = P"
    using AP_is_PBMH_ades[OF assms]
    by (simp only: Healthy_def')
  have P_A1: "A1 P = P"
    by (simp only: A1_eq_PBMH_ades[OF P_H] P_PBMH)
  have wf_H: "(P \<^sub>f) is \<^bold>H"
    unfolding rad_wait_false_as_state_subst
    by (rule state_subst_H1_H2_closed[OF P_H])
  have wf_A1: "A1 (P \<^sub>f) = (P \<^sub>f)"
    using arg_cong[where f=rad_wait_false, OF P_A1]
    by (simp only: rad_wait_false_as_state_subst A1_state_subst)
  show ?thesis
    by (rule Healthy_intro,
        simp only: A1_eq_PBMH_ades[OF wf_H, symmetric] wf_A1)
qed

lemma AP_wf_ok_false_PBMH_ades:
  assumes "P is AP"
  shows "(P \<^sub>f)\<^sup>f is PBMH_ades"
  by (rule Healthy_intro,
      simp only: PBMH_ades_ok_false
        Healthy_if[OF AP_wait_false_PBMH_ades[OF assms]])

lemma AP_wf_ok_true_PBMH_ades:
  assumes "P is AP"
  shows "(P \<^sub>f)\<^sup>t is PBMH_ades"
  by (rule Healthy_intro,
      simp only: PBMH_ades_ok_true
        Healthy_if[OF AP_wait_false_PBMH_ades[OF assms]])

abbreviation bottom_AP :: "('t::trace, 'e) reactive_angelic_design"
    ("\<^bold>\<bottom>\<^sub>A\<^sub>P") where
"\<^bold>\<bottom>\<^sub>A\<^sub>P \<equiv> AP true"

abbreviation top_AP :: "('t::trace, 'e) reactive_angelic_design"
    ("\<^bold>\<top>\<^sub>A\<^sub>P") where
"\<^bold>\<top>\<^sub>A\<^sub>P \<equiv> AP false"

lemma bottom_AP_lower:
  assumes "P is AP"
  shows "\<^bold>\<bottom>\<^sub>A\<^sub>P \<sqsubseteq> P"
proof -
  have "AP true \<sqsubseteq> AP P"
    by (rule AP_mono; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms])
qed

lemma top_AP_upper:
  assumes "P is AP"
  shows "P \<sqsubseteq> \<^bold>\<top>\<^sub>A\<^sub>P"
proof -
  have "AP P \<sqsubseteq> AP false"
    by (rule AP_mono; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms])
qed

end
