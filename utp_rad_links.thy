section \<open>Links with Reactive Designs\<close>

theory utp_rad_links
  imports utp_rad_csp_healthy "UTP-Reactive-Designs.utp_rdes_healths"
begin

subsection \<open>From reactive angelic designs to CSP\<close>

(* Thesis Theorem T.G.7.1. *)
lemma rad_ac2p_RA1:
  assumes "P is PBMH_ades"
  shows "(rad_ac2p \<circ> RA1) P = (R1 \<circ> rad_ac2p) P"
proof -
  have pbmh: "PBMH_ades P = P"
    using assms by (simp add: Healthy_def')
  have ra1_healthy: "PBMH_ades (RA1 P) = RA1 P"
    using PBMH_ades_RA1_PBMH_ades[of P] pbmh
    by simp
  show ?thesis
    apply (simp only: comp_apply rad_ac2p_def rad2csp_rel_def ac2p_def
        ra1_healthy pbmh)
    apply (simp add: R1_def RA1_def csp2rad_obs_def
        rad_trace_extensions_def StateII_def fun_eq_iff Let_def)
    apply pred_auto
    done
qed

(* Thesis Theorem T.G.7.2. *)
lemma rad_ac2p_RA1_RA2:
  assumes "P is PBMH_ades"
  shows "(rad_ac2p \<circ> RA1 \<circ> RA2) P =
    (R1 \<circ> R2 \<circ> rad_ac2p) P"
proof -
  have pbmh: "PBMH_ades P = P"
    using assms by (simp add: Healthy_def')
  have ra2_healthy: "PBMH_ades (RA2 P) = RA2 P"
    using PBMH_ades_RA2_PBMH_ades[of P] pbmh
    by simp
  have ra1_ra2_healthy:
      "PBMH_ades (RA1 (RA2 P)) = RA1 (RA2 P)"
    using PBMH_ades_RA1_PBMH_ades[of "RA2 P"] ra2_healthy
    by simp
  show ?thesis
    apply (simp only: comp_apply rad_ac2p_def rad2csp_rel_def ac2p_def
        ra1_ra2_healthy pbmh)
    apply (simp add: RA1_def RA2_def R1_def R2_def R2s_def
        csp2rad_obs_def rad_trace_extensions_def rad_zero_trace_def
        rad_normalise_choices_def rad_trace_difference_def StateII_def
        fun_eq_iff Let_def)
    apply pred_auto
    done
qed

lemma rad_ac2p_II_Rac [simp]:
  "rad_ac2p (II_Rac :: 'e reactive_angelic_design) = II\<^sub>C"
  apply (simp only: rad_ac2p_def rad2csp_rel_def ac2p_def
      PBMH_ades_II_Rac)
  apply (simp add: II_Rac_def RA1_def csp2rad_obs_def
      rad_trace_extensions_def StateII_def skip_rea_def pred_skip
      fun_eq_iff Let_def lens_defs)
  apply pred_auto
  subgoal premises assms for ok more ok' morea
    using rea_vars.equality[
      of "\<lparr>ok\<^sub>v = True, \<dots> = morea\<rparr>"
         "\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>"]
    by (simp add: assms)
  subgoal premises assms for ok more ok' morea
    using rea_vars.equality[
      of "\<lparr>ok\<^sub>v = True, \<dots> = morea\<rparr>"
         "\<lparr>ok\<^sub>v = True, \<dots> = more\<rparr>"]
    by (simp add: assms)
  done

(* Thesis Theorem T.G.7.3. *)
lemma rad_ac2p_RA3:
  "(rad_ac2p \<circ> RA3) P = (R3c \<circ> rad_ac2p) P"
proof -
  have pbmh_wait:
      "PBMH_ades (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
       (PBMH_ades P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        PBMH_ades Q)" for P Q
    by (simp add: PBMH_ades_def PBMH_def pbmh_step_def expr_if_def
        fun_eq_iff lens_defs; pred_auto; blast)
  have ac2p_wait:
      "rad_ac2p (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
       (rad_ac2p P \<triangleleft> $wait\<^sup>< \<triangleright> rad_ac2p Q)"
      for P Q
    by (simp only: rad_ac2p_def rad2csp_rel_def ac2p_def pbmh_wait;
        simp add: csp2rad_obs_def expr_if_def fun_eq_iff lens_defs;
        pred_auto)
  show ?thesis
    by (simp add: RA3_def R3c_def ac2p_wait)
qed

(* Paper Theorem 12 / Thesis Theorem T.5.3.1. *)
theorem rad_ac2p_RA:
  assumes "P is PBMH_ades"
  shows "(rad_ac2p \<circ> RA) P = (\<^bold>R \<circ> rad_ac2p) P"
  by (simp add: RA_def RA1_RA3_commute[simplified comp_apply]
      RA2_RA3_commute[simplified comp_apply]
      rad_ac2p_RA3[simplified comp_apply]
      rad_ac2p_RA1_RA2[simplified comp_apply] assms R2_def RH_def R1_idem
      R1_R3c_commute R2c_R3c_commute R1_R2s_R2c)

(* Paper Theorem 13 / Thesis Theorem T.5.3.2. *)
theorem rad_ac2p_RA_design:
  "(rad_ac2p \<circ> RA \<circ> A) ((\<not> (rad_wait_false P)\<^sup>f) \<turnstile> (rad_wait_false P)\<^sup>t) =
   \<^bold>R ((\<not> rad_ac2p ((rad_wait_false P)\<^sup>f)) \<turnstile> rad_ac2p ((rad_wait_false P)\<^sup>t))"
proof -
  let ?D =
    "(\<not> (rad_wait_false P)\<^sup>f) \<turnstile>
      (rad_wait_false P)\<^sup>t"
  have design_healthy: "?D is \<^bold>H"
    by (rule design_is_H1_H2; pred_auto)
  have pbmh_healthy: "PBMH_ades ?D is PBMH_ades"
    by (rule Healthy_Idempotent[OF PBMH_ades_Idempotent])
  have mapped_design:
      "rad_ac2p ?D =
       ((\<not> rad_ac2p ((rad_wait_false P)\<^sup>f)) \<turnstile>
        rad_ac2p ((rad_wait_false P)\<^sup>t))"
    unfolding rad_ac2p_def
    by (subst ac2p_design[OF design_healthy];
        simp add: rad2csp_rel_def design_def fun_eq_iff
          csp2rad_obs_def subst_app_def subst_upd_def subst_id_def SEXP_def;
        pred_auto)
  have "rad_ac2p (RA (A ?D)) =
      rad_ac2p (RA (PBMH_ades ?D))"
    by (simp only: RA_A[OF design_healthy, simplified comp_apply])
  also have "... = \<^bold>R (rad_ac2p (PBMH_ades ?D))"
    by (rule rad_ac2p_RA[OF pbmh_healthy, simplified comp_apply])
  also have "... = \<^bold>R (rad_ac2p ?D)"
    by (simp only: rad_ac2p_def ac2p_PBMH_ades)
  also have "... =
      \<^bold>R ((\<not> rad_ac2p ((rad_wait_false P)\<^sup>f)) \<turnstile>
        rad_ac2p ((rad_wait_false P)\<^sup>t))"
    by (simp only: mapped_design)
  finally show ?thesis
    by (simp only: comp_apply)
qed

(* Theorems 11 and 13 give the CSP image of a RAD-healthy predicate.
   Theorem 13 uses Theorem 12 to transport RA healthiness to R healthiness. *)
theorem rad_ac2p_RAD:
  assumes "P is RAD"
  shows "rad_ac2p P = \<^bold>R ((\<not> rad_ac2p ((rad_wait_false P)\<^sup>f)) \<turnstile> rad_ac2p ((rad_wait_false P)\<^sup>t))"
proof -
  have "rad_ac2p P = rad_ac2p (RAD P)"
    using assms
    by (simp only: Healthy_def')
  also have "... = rad_ac2p
      ((RA \<circ> A) ((\<not> (rad_wait_false P)\<^sup>f) \<turnstile>
        (rad_wait_false P)\<^sup>t))"
    by (simp only: RAD_design_form)
  also have "... =
      \<^bold>R ((\<not> rad_ac2p ((rad_wait_false P)\<^sup>f)) \<turnstile>
        rad_ac2p ((rad_wait_false P)\<^sup>t))"
    unfolding comp_apply
    by (rule rad_ac2p_RA_design[simplified comp_apply])
  finally show ?thesis .
qed

lemma rad_ac2p_RAD_healthy:
  assumes "P is RAD"
  shows "rad_ac2p P is \<^bold>R"
  using rad_ac2p_RAD[OF assms]
  by (simp add: Healthy_def' RH_idem)

subsection \<open>From CSP to reactive angelic designs\<close>

(* Thesis Theorem T.G.7.8. *)
lemma rad_p2ac_R1:
  "(rad_p2ac \<circ> R1) P = (RA1 \<circ> rad_p2ac) P"
proof -
  have "(RA1 \<circ> rad_p2ac) P = (rad_p2ac \<circ> R1) P"
    apply (simp add: RA1_def rad_p2ac_def p2ac_def
        csp2rad_rel_def R1_def rad2csp_obs_def
        rad_trace_extensions_def fun_eq_iff Let_def)
    apply pred_auto
    subgoal premises assms for ok tr ref wait ok' ac tr' ref' wait'
    proof -
      let ?z = "\<lparr>rad_state.tr\<^sub>v = tr', rad_state.ref\<^sub>v = ref',
          rad_state.wait\<^sub>v = wait', \<dots> = ()\<rparr>"
      have "?z \<in> {z. tr \<le> rad_state.tr\<^sub>v z} \<inter> ac"
        using assms(1) assms(3)
        by simp
      with assms(4) show False
        by simp
    qed
    done
  then show ?thesis by simp
qed

(* Thesis Theorem T.G.7.9. *)
lemma rad_p2ac_R1_R2:
  "(rad_p2ac \<circ> R1 \<circ> R2) P =
   (RA2 \<circ> rad_p2ac) P"
  apply (simp add: RA2_def rad_p2ac_def p2ac_def
      csp2rad_rel_def R2_def R2s_def R1_def rad2csp_obs_def
      rad_normalise_choices_def rad_trace_difference_def
      rad_zero_trace_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)
  apply pred_auto
  subgoal premises assms for ok tr ref wait ok' ac tr' ref' wait'
    apply (rule exI[of _ "tr' - tr"])
    apply (rule exI[of _ ref'])
    apply (rule exI[of _ wait'])
    using assms
    by auto
  subgoal premises assms for ok tr ref wait more morea ok' ac moreb
      ref' wait' tr''
  proof -
    let ?z = "\<lparr>rad_state.tr\<^sub>v = tr'', rad_state.ref\<^sub>v = ref',
        rad_state.wait\<^sub>v = wait', \<dots> = ()\<rparr>"
    show ?thesis
      apply (rule bexI[of _ ?z])
      subgoal using assms(1,3)
        by (simp add: lens_defs alpha_defs)
      subgoal using assms(2)
        by simp
      done
  qed
  done

(* Thesis Lemma L.G.7.2: reactive identity. *)
lemma rad_p2ac_II_C [simp]:
  "rad_p2ac (II\<^sub>C :: ('e list, 'e set) rp_hrel) = II_Rac"
proof -
  have round_trip:
      "p2ac (ac2p (II_Rac :: 'e reactive_angelic_design)) = II_Rac"
    apply (simp add: p2ac_def ac2p_def StateII_def II_Rac_def RA1_def
        rad_trace_extensions_def fun_eq_iff Let_def)
    apply pred_auto
    done
  have mapped:
      "rad2csp_rel (ac2p (II_Rac :: 'e reactive_angelic_design)) =
       (II\<^sub>C :: ('e list, 'e set) rp_hrel)"
    using rad_ac2p_II_Rac
    by (simp only: rad_ac2p_def)
  have rel:
      "csp2rad_rel (II\<^sub>C :: ('e list, 'e set) rp_hrel) =
       ac2p (II_Rac :: 'e reactive_angelic_design)"
    using arg_cong[where f=csp2rad_rel, OF mapped]
    by simp
  show ?thesis
    by (simp add: rad_p2ac_def rel round_trip)
qed

(* Thesis Theorem T.G.7.10. *)
lemma rad_p2ac_R3:
  "(rad_p2ac \<circ> R3c) P = (RA3 \<circ> rad_p2ac) P"
proof -
  have p2ac_wait:
      "rad_p2ac (P \<triangleleft> $wait\<^sup>< \<triangleright> Q) =
       (rad_p2ac P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> rad_p2ac Q)"
      for P Q
    by (simp add: rad_p2ac_def p2ac_def csp2rad_rel_def
        expr_if_def rad2csp_obs_def fun_eq_iff lens_defs alpha_defs)
  show ?thesis
    by (simp add: R3c_def RA3_def p2ac_wait)
qed

(* Paper Theorem 14. *)
theorem rad_p2ac_R:
  "(rad_p2ac \<circ> \<^bold>R) P = (RA \<circ> rad_p2ac) P"
proof -
  have "rad_p2ac (\<^bold>R P) =
      rad_p2ac (R3c (R1 (R2 P)))"
    by (simp add: RH_def R2_def R1_R3c_commute
        R2c_R3c_commute R1_R2s_R2c R1_idem)
  also have "... = RA3 (rad_p2ac (R1 (R2 P)))"
    by (simp only: rad_p2ac_R3[simplified comp_apply])
  also have "... = RA3 (RA1 (rad_p2ac (R1 (R2 P))))"
    by (simp add: rad_p2ac_R1[simplified comp_apply] RA1_idem)
  also have "... = RA3 (RA1 (RA2 (rad_p2ac P)))"
    by (simp only: rad_p2ac_R1_R2[simplified comp_apply])
  also have "... = RA (rad_p2ac P)"
    by (simp add: RA_def
        RA1_RA3_commute[simplified comp_apply]
        RA2_RA3_commute[simplified comp_apply])
  finally show ?thesis
    by simp
qed

(* Paper Theorem 15 / Thesis Theorem T.5.3.4. *)
theorem rad_p2ac_R_design:
  "(rad_p2ac \<circ> \<^bold>R)
      ((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) =
   (RA \<circ> A)
      ((\<not> rad_p2ac (P\<^sup>f\<^sub>f)) \<turnstile>
        rad_p2ac (P\<^sup>t\<^sub>f))"
proof -
  have csp2rad_design:
      "csp2rad_rel ((\<not> F) \<turnstile> T) =
       ((\<not> csp2rad_rel F) \<turnstile> csp2rad_rel T)"
    for F T
    by (simp add: csp2rad_rel_def design_def fun_eq_iff
        rad2csp_obs_def; pred_auto)
  have p2ac_design_full:
      "(ac_non_empty \<and> p2ac ((\<not> F) \<turnstile> T)) =
       (ac_non_empty \<and>
         ((\<not> p2ac F) \<turnstile> p2ac T))"
    for F T
    by (simp add: ac_non_empty_def p2ac_def design_def fun_eq_iff;
        pred_auto)
  have mapped_design:
      "(ac_non_empty \<and>
        rad_p2ac ((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)) =
       (ac_non_empty \<and>
        ((\<not> rad_p2ac (P\<^sup>f\<^sub>f)) \<turnstile>
          rad_p2ac (P\<^sup>t\<^sub>f)))"
    using p2ac_design_full[
        of "csp2rad_rel (P\<^sup>f\<^sub>f)"
           "csp2rad_rel (P\<^sup>t\<^sub>f)"]
    by (simp add: rad_p2ac_def csp2rad_design)
  have mapped_unrest:
      "$ok\<^sup>> \<sharp>
        rad_p2ac ((P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk>) \<^sub>f)"
    for b
    apply (simp add: unrest_lens rad_p2ac_def p2ac_def
        csp2rad_rel_def rad2csp_obs_def)
    apply (simp add: subst_app_def subst_upd_def subst_id_def
        SEXP_def lens_defs alpha_defs)
    done
  let ?D = "((\<not> rad_p2ac (P\<^sup>f\<^sub>f)) \<turnstile>
    rad_p2ac (P\<^sup>t\<^sub>f))"
  have design_healthy: "?D is \<^bold>H"
    apply (rule design_is_H1_H2)
     apply (rule unrest_pred(6))
     apply (rule mapped_unrest)
    by (rule mapped_unrest)
  have RA1_nonempty: "RA1 (ac_non_empty \<and> X) = RA1 X" for X
    by (simp add: RA1_def ac_non_empty_def fun_eq_iff Let_def;
        pred_auto)
  have design_pbmh: "PBMH_ades ?D = ?D"
    by (simp add: RA_design_as_disj PBMH_ades_disj
        PBMH_ades_not_ok_expr PBMH_ades_conj_ok rad_p2ac_def)
  let ?S = "rad_p2ac ((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
  have mapped_ra1: "RA1 ?S = RA1 ?D"
  proof -
    have "RA1 ?S = RA1 (ac_non_empty \<and> ?S)"
      by (simp only: RA1_nonempty)
    also have "... = RA1 (ac_non_empty \<and> ?D)"
      by (simp only: mapped_design)
    also have "... = RA1 ?D"
      by (simp only: RA1_nonempty)
    finally show ?thesis .
  qed
  have RA_via_components: "RA X = RA3 (RA2 (RA1 X))" for X
    by (simp add: RA_def
        RA1_RA2_commute[simplified comp_apply]
        RA1_RA3_commute[simplified comp_apply]
        RA2_RA3_commute[simplified comp_apply])
  have mapped_RA: "RA ?S = RA ?D"
    by (simp only: RA_via_components mapped_ra1)
  have A_absorb: "RA (A ?D) = RA ?D"
    by (simp only: RA_A[OF design_healthy, simplified comp_apply]
        design_pbmh)
  have "(rad_p2ac \<circ> \<^bold>R)
      ((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = RA ?S"
    by (simp only: comp_apply rad_p2ac_R[simplified comp_apply])
  also have "... = RA ?D"
    by (rule mapped_RA)
  also have "... = (RA \<circ> A) ?D"
    by (simp only: comp_apply A_absorb)
  finally show ?thesis .
qed

end
