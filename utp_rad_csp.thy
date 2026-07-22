section \<open>Relationship with CSP\<close>

theory utp_rad_csp
  imports utp_rad_designs "UTP-Reactive-Designs.utp_rdes_healths"
begin

subsection \<open>Observation isomorphism\<close>

(* CSP's flat alphabet is {ok, tr, ref, wait}; rea_vars.more stores ref. *)
type_synonym 'e csp_obs = "('e list, 'e set) rp"

(* Repackage one nested RAD observation as a flat CSP observation. *)
definition rad2csp_obs ::
  "'e rad_state des_vars_scheme \<Rightarrow> 'e csp_obs" where
[pred]: "rad2csp_obs x =
  \<lparr> utp_des_core.des_vars.ok\<^sub>v = ok\<^sub>v x,
    utp_rea_core.rea_vars.wait\<^sub>v =
      utp_rad_core.rad_state.wait\<^sub>v (des_vars.more x),
    utp_rea_core.rea_vars.tr\<^sub>v =
      utp_rad_core.rad_state.tr\<^sub>v (des_vars.more x),
    \<dots> = utp_rad_core.rad_state.ref\<^sub>v (des_vars.more x) \<rparr>"

(* Repackage one flat CSP observation as a nested RAD observation. *)
definition csp2rad_obs ::
  "'e csp_obs \<Rightarrow> 'e rad_state des_vars_scheme" where
[pred]: "csp2rad_obs x =
  \<lparr> utp_des_core.des_vars.ok\<^sub>v = ok\<^sub>v x,
    \<dots> = \<lparr> utp_rad_core.rad_state.tr\<^sub>v = rea_vars.tr\<^sub>v x,
          utp_rad_core.rad_state.ref\<^sub>v = rea_vars.more x,
          utp_rad_core.rad_state.wait\<^sub>v = rea_vars.wait\<^sub>v x,
          \<dots> = () \<rparr> \<rparr>"

(* The observation conversions are bijective. *)
lemma csp2rad_obs_inverse [simp]:
  "csp2rad_obs (rad2csp_obs x) = x"
  by (cases x; simp add: rad2csp_obs_def csp2rad_obs_def)

lemma rad2csp_obs_inverse [simp]:
  "rad2csp_obs (csp2rad_obs x) = x"
  by (cases x; simp add: rad2csp_obs_def csp2rad_obs_def)

subsection \<open>Relation and design mappings\<close>

(* Lift the observation conversions pointwise to both ends of a relation. *)
definition rad2csp_rel :: "'e rad_state des_hrel \<Rightarrow> ('e list, 'e set) rp_hrel"
where [pred]: "rad2csp_rel P = (\<lambda> (x, y). P (csp2rad_obs x, csp2rad_obs y))"

definition csp2rad_rel :: "('e list, 'e set) rp_hrel \<Rightarrow> 'e rad_state des_hrel"
where [pred]: "csp2rad_rel P = (\<lambda> (x, y). P (rad2csp_obs x, rad2csp_obs y))"

lemma csp2rad_rel_inverse [simp]:
  "csp2rad_rel (rad2csp_rel P) = P"
  by (simp add: rad2csp_rel_def csp2rad_rel_def fun_eq_iff)

lemma rad2csp_rel_inverse [simp]:
  "rad2csp_rel (csp2rad_rel P) = P"
  by (simp add: rad2csp_rel_def csp2rad_rel_def fun_eq_iff)

(* Designs distribute through the observation repackaging. *)
lemma csp2rad_rel_design:
  "csp2rad_rel ((\<not> F) \<turnstile> T) =
   ((\<not> csp2rad_rel F) \<turnstile> csp2rad_rel T)"
  by (simp add: csp2rad_rel_def design_def fun_eq_iff
      rad2csp_obs_def; pred_auto)

lemma rad2csp_rel_design:
  "rad2csp_rel ((\<not> F) \<turnstile> T) =
   ((\<not> rad2csp_rel F) \<turnstile> rad2csp_rel T)"
  by (simp add: rad2csp_rel_def design_def fun_eq_iff
      csp2rad_obs_def; pred_auto)

(* Forget the angelic choices, then repackage the resulting observations as CSP. *)
definition rad_ac2p :: "'e reactive_angelic_design \<Rightarrow> ('e list, 'e set) rp_hrel"
where [pred]: "rad_ac2p = rad2csp_rel \<circ> ac2p"

(* Repackage CSP observations as RAD state, then introduce angelic choices. *)
definition rad_p2ac :: "('e list, 'e set) rp_hrel \<Rightarrow> 'e reactive_angelic_design"
where [pred]: "rad_p2ac = p2ac \<circ> csp2rad_rel"

(* The design-level adapter uses d2ac rather than the paper's predicate p2ac. *)
definition rad_d2ac :: "('e list, 'e set) rp_hrel \<Rightarrow> 'e reactive_angelic_design"
where [pred]: "rad_d2ac = d2ac \<circ> csp2rad_rel"

lemma rad_p2ac_PBMH_ades [closure]:
  "rad_p2ac P is PBMH_ades"
  by (simp add: Healthy_def rad_p2ac_def)

lemma rad_ac2p_d2ac:
  assumes "csp2rad_rel P is \<^bold>H"
  shows "(rad_ac2p \<circ> rad_d2ac) P = P"
  by (simp add: rad_ac2p_def rad_d2ac_def
      ac2p_d2ac[simplified comp_apply] assms)

subsection \<open>From reactive angelic designs to CSP\<close>

(* Thesis Theorem T.G.7.1. *)
lemma rad_ac2p_RA1:
  assumes "P is PBMH_ades"
  shows "(rad_ac2p \<circ> RA1) P = (R1 \<circ> rad_ac2p) P"
  using assms RA1_PBMH_ades_healthy[OF assms]
  apply (simp only: comp_apply rad_ac2p_def rad2csp_rel_def ac2p_def
      Healthy_def')
  apply (simp add: R1_def RA1_def csp2rad_obs_def
      rad_trace_extensions_def StateII_def fun_eq_iff Let_def)
  apply pred_auto
  done

(* Thesis Theorem T.G.7.2. *)
lemma rad_ac2p_RA1_RA2:
  assumes "P is PBMH_ades"
  shows "(rad_ac2p \<circ> RA1 \<circ> RA2) P =
    (R1 \<circ> R2 \<circ> rad_ac2p) P"
proof -
  have ra2_healthy: "RA2 P is PBMH_ades"
    by (rule RA2_PBMH_ades_healthy[OF assms])
  have ra1_ra2_healthy: "RA1 (RA2 P) is PBMH_ades"
    by (rule RA1_PBMH_ades_healthy[OF ra2_healthy])
  show ?thesis
    using assms ra2_healthy ra1_ra2_healthy
    apply (simp only: comp_apply rad_ac2p_def rad2csp_rel_def ac2p_def
        Healthy_def')
    apply (simp add: RA1_def RA2_def R1_def R2_def R2s_def
        csp2rad_obs_def rad_trace_extensions_def rad_zero_trace_def
        rad_normalise_choices_def rad_trace_difference_def StateII_def
        fun_eq_iff Let_def)
    apply pred_auto
    done
qed

lemma rad_ac2p_II_Rac [simp]:
  "rad_ac2p (II_Rac :: 'e reactive_angelic_design) = II\<^sub>C"
  apply (simp only: rad_ac2p_def comp_apply rad2csp_rel_def ac2p_def
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
  have ac2p_wait:
      "rad_ac2p (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
       (rad_ac2p P \<triangleleft> $wait\<^sup>< \<triangleright> rad_ac2p Q)"
      for P Q
    by (simp only: rad_ac2p_def comp_apply rad2csp_rel_def ac2p_def
          PBMH_ades_wait_cond;
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
  "(rad_ac2p \<circ> RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t) =
   \<^bold>R ((\<not> rad_ac2p ((P \<^sub>wf)\<^sup>f)) \<turnstile> rad_ac2p ((P \<^sub>wf)\<^sup>t))"
proof -
  let ?D = "(\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t"
  have design_healthy: "?D is \<^bold>H"
    by (rule rad_wait_false_design_healthy)
  have pbmh_healthy: "PBMH_ades ?D is PBMH_ades"
    by (rule Healthy_Idempotent[OF PBMH_ades_Idempotent])
  have mapped_ac2p:
      "ac2p ?D = ((\<not> ac2p ((P \<^sub>wf)\<^sup>f)) \<turnstile> ac2p ((P \<^sub>wf)\<^sup>t))"
    by (subst ac2p_design[OF design_healthy];
        simp add: design_def fun_eq_iff
          subst_app_def subst_upd_def subst_id_def SEXP_def;
        pred_auto)
  have mapped_design:
      "rad_ac2p ?D = ((\<not> rad_ac2p ((P \<^sub>wf)\<^sup>f)) \<turnstile> rad_ac2p ((P \<^sub>wf)\<^sup>t))"
    unfolding rad_ac2p_def comp_apply
    by (simp only: mapped_ac2p rad2csp_rel_design)
  have "rad_ac2p (RA (A ?D)) =
      rad_ac2p (RA (PBMH_ades ?D))"
    by (simp only: RA_A[OF design_healthy, simplified comp_apply])
  also have "... = \<^bold>R (rad_ac2p (PBMH_ades ?D))"
    by (rule rad_ac2p_RA[OF pbmh_healthy, simplified comp_apply])
  also have "... = \<^bold>R (rad_ac2p ?D)"
    by (simp only: rad_ac2p_def comp_apply ac2p_PBMH_ades)
  also have "... = \<^bold>R ((\<not> rad_ac2p ((P \<^sub>wf)\<^sup>f)) \<turnstile> rad_ac2p ((P \<^sub>wf)\<^sup>t))"
    by (simp only: mapped_design)
  finally show ?thesis
    by (simp only: comp_apply)
qed

(* Theorems 11 and 13 give the CSP image of a RAD-healthy predicate.
   Theorem 13 uses Theorem 12 to transport RA healthiness to R healthiness. *)
theorem rad_ac2p_RAD:
  assumes "P is RAD"
  shows "rad_ac2p P = \<^bold>R ((\<not> rad_ac2p ((P \<^sub>wf)\<^sup>f)) \<turnstile> rad_ac2p ((P \<^sub>wf)\<^sup>t))"
proof -
  have "rad_ac2p P = rad_ac2p (RAD P)"
    using assms
    by (simp only: Healthy_def')
  also have "... = rad_ac2p ((RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t))"
    by (simp only: RAD_design_form)
  also have "... = \<^bold>R ((\<not> rad_ac2p ((P \<^sub>wf)\<^sup>f)) \<turnstile> rad_ac2p ((P \<^sub>wf)\<^sup>t))"
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
    by (simp only: rad_ac2p_def comp_apply)
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

(* After fixing ok' and wait in the source, the mapped predicate no
   longer depends on ok'. *)
lemma rad_p2ac_subst_unrest_ok:
  "$ok\<^sup>> \<sharp>
    rad_p2ac ((P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk>) \<^sub>f)"
  apply (simp add: unrest_lens rad_p2ac_def p2ac_def
      csp2rad_rel_def rad2csp_obs_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

(* Paper Theorem 15 / Thesis Theorem T.5.3.4. *)
theorem rad_p2ac_R_design:
  "(rad_p2ac \<circ> \<^bold>R) ((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) =
   (RA \<circ> A) ((\<not> rad_p2ac (P\<^sup>f\<^sub>f)) \<turnstile> rad_p2ac (P\<^sup>t\<^sub>f))"
proof -
  have mapped_design:
      "(ac_non_empty \<and>
        rad_p2ac ((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)) =
       (ac_non_empty \<and>
        ((\<not> rad_p2ac (P\<^sup>f\<^sub>f)) \<turnstile>
          rad_p2ac (P\<^sup>t\<^sub>f)))"
    using p2ac_design_nonempty[
        of "csp2rad_rel (P\<^sup>f\<^sub>f)"
           "csp2rad_rel (P\<^sup>t\<^sub>f)"]
    by (simp add: rad_p2ac_def csp2rad_rel_design)
  let ?D = "((\<not> rad_p2ac (P\<^sup>f\<^sub>f)) \<turnstile>
    rad_p2ac (P\<^sup>t\<^sub>f))"
  have design_healthy: "?D is \<^bold>H"
    apply (rule design_is_H1_H2)
     apply (rule unrest_pred(6))
     apply (rule rad_p2ac_subst_unrest_ok)
    by (rule rad_p2ac_subst_unrest_ok)
  have design_pbmh: "PBMH_ades ?D = ?D"
    by (simp add: RA_design_as_disj PBMH_ades_disj
        PBMH_ades_not_ok_expr PBMH_ades_conj_ok rad_p2ac_def)
  let ?S = "rad_p2ac ((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
  have mapped_RA: "RA ?S = RA ?D"
    by (rule RA_cong_ac_non_empty[OF mapped_design])
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

(* Paper Theorem 16 / Thesis Theorem T.5.3.5. *)
theorem rad_ac2p_p2ac:
  "(rad_ac2p \<circ> rad_p2ac) P = P"
proof -
  have base_round_trip:
      "(ac2p \<circ> p2ac) Q = Q" for Q :: "'s des_hrel"
    apply (simp only: comp_apply ac2p_subset p2ac_def)
    apply (simp add: fun_eq_iff StateII_def)
    by (pred_auto)
  show ?thesis
    by (simp only: comp_apply rad_ac2p_def rad_p2ac_def
        base_round_trip[simplified comp_apply] rad2csp_rel_inverse)
qed

(* Paper Lemma 6. *)
lemma rad_p2ac_ac2p:
  fixes P :: "'e reactive_angelic_design"
  shows "(rad_p2ac \<circ> rad_ac2p) P =
    (\<lambda> (s0, ac'). \<exists> ac0 y.
      P (s0, des_vars.more_update
        (achoices.ac\<^sub>v_update (\<lambda>_. ac0)) ac') \<and>
      ac0 \<subseteq> {y} \<and> y \<in> achoices.ac\<^sub>v (des_vars.more ac'))"
proof -
  have input_repackage:
      "\<lparr>ok\<^sub>v = ok\<^sub>v s0,
        \<dots> = StateII (astate.s\<^sub>v (des_vars.more s0))\<rparr> = s0"
      for s0 :: "'s astate des_vars_scheme"
    by (rule des_vars.equality; simp add: StateII_def;
        rule astate.equality; simp add: StateII_def)
  have output_repackage:
      "des_vars.more_update (achoices.ac\<^sub>v_update (\<lambda>_. ac0)) ac' =
       \<lparr>ok\<^sub>v = ok\<^sub>v ac',
         \<dots> = \<lparr>ac\<^sub>v = ac0, \<dots> = ()\<rparr>\<rparr>"
      for ac0 and ac' :: "'s achoices des_vars_scheme"
    by (rule des_vars.equality; simp;
        rule achoices.equality; simp)
  show ?thesis
    apply (simp only: comp_apply rad_p2ac_def rad_ac2p_def
        csp2rad_rel_inverse p2ac_def ac2p_subset)
    apply (simp add: fun_eq_iff input_repackage output_repackage)
    by auto
qed

(* Paper Theorem 17. *)
theorem rad_p2ac_ac2p_refine:
  assumes "P is PBMH_ades"
  shows "P \<sqsubseteq> (rad_p2ac \<circ> rad_ac2p) P"
  using assms
  apply (simp only: Healthy_def' rad_p2ac_ac2p)
  apply (simp add: PBMH_ades_def pred_refine_iff)
  by (pred_auto; blast)

(* Thesis Lemma L.G.7.11. *)
lemma rad_p2ac_ac2p_A2:
  fixes P :: "'e reactive_angelic_design"
  assumes "P is A2"
  shows "(rad_p2ac \<circ> rad_ac2p) P = (ac_non_empty \<and> P)"
proof -
  have bridge:
      "(rad_p2ac \<circ> rad_ac2p) Q = (p2ac \<circ> ac2p) Q"
      for Q :: "'e reactive_angelic_design"
    by (simp add: rad_p2ac_def rad_ac2p_def)
  have nonempty: "p2ac Q = (ac_non_empty \<and> p2ac Q)"
      for Q :: "'s des_hrel"
    by (simp add: p2ac_def ac_non_empty_def fun_eq_iff; pred_auto)
  have fixed: "A2 P = P"
    using assms by (simp add: Healthy_def')
  have "(rad_p2ac \<circ> rad_ac2p) P = p2ac (ac2p (A2 P))"
    by (subst bridge; simp only: comp_apply fixed)
  also have "... = (ac_non_empty \<and> p2ac (ac2p (A2 P)))"
    by (rule nonempty)
  also have "... = (ac_non_empty \<and>
      ((\<not> (A2_rel (\<not> pre\<^sub>D P) \<and>
          ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)) \<turnstile>\<^sub>r
       (A2_rel (post\<^sub>D P) \<and>
          ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)))"
    by (simp add: A2_def ac2p_rdesign p2ac_design
        p2ac_ac2p_rel_A2[simplified comp_apply] A2_rel_idem)
  also have "... = (ac_non_empty \<and> A2 P)"
    by (simp add: A2_def ac_non_empty_def rdesign_refinement fun_eq_iff;
        pred_simp; auto)
  also have "... = (ac_non_empty \<and> P)"
    by (simp only: fixed)
  finally show ?thesis .
qed

(* Paper Theorem 18 / Thesis Theorem T.5.3.7. *)
theorem rad_p2ac_ac2p_RA_design:
  assumes "(P \<^sub>wf)\<^sup>f is A2"
    and "(P \<^sub>wf)\<^sup>t is A2"
  shows "(rad_p2ac \<circ> rad_ac2p \<circ> RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t) = (RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  let ?F = "(P \<^sub>wf)\<^sup>f"
  let ?T = "(P \<^sub>wf)\<^sup>t"
  let ?D = "(\<not> ?F) \<turnstile> ?T"
  let ?C = "(\<not> rad_ac2p ?F) \<turnstile> rad_ac2p ?T"
  let ?S = "rad_p2ac ?C"
  let ?M = "((\<not> (rad_p2ac \<circ> rad_ac2p) ?F) \<turnstile>
    (rad_p2ac \<circ> rad_ac2p) ?T)"
  have mapped_RA: "RA ?S = RA ?M"
    apply (rule RA_cong_ac_non_empty)
    using p2ac_design_nonempty[
        of "csp2rad_rel (rad_ac2p ?F)"
           "csp2rad_rel (rad_ac2p ?T)"]
    by (simp add: rad_p2ac_def csp2rad_rel_design)
  have F_round:
      "(rad_p2ac \<circ> rad_ac2p) ?F = (ac_non_empty \<and> ?F)"
    by (rule rad_p2ac_ac2p_A2[OF assms(1)])
  have T_round:
      "(rad_p2ac \<circ> rad_ac2p) ?T = (ac_non_empty \<and> ?T)"
    by (rule rad_p2ac_ac2p_A2[OF assms(2)])
  have nonempty_design_absorb:
      "RA ((\<not> (ac_non_empty \<and> ?F)) \<turnstile>
          (ac_non_empty \<and> ?T)) = RA ?D"
    by (simp only:
        RA_design_components[
          of "\<not> (ac_non_empty \<and> ?F)" "ac_non_empty \<and> ?T"]
        RA_design_components[of "\<not> ?F" ?T]
        pred_ba.boolean_algebra.double_compl
        RA1_ac_non_empty_absorb)
  have A2_PBMH: "PBMH_ades (A2 Q) = A2 Q"
      for Q :: "'e reactive_angelic_design"
    by (simp add: A2_def PBMH_ades_rdesign A2_rel_def PBMH_idem)
  have design_pbmh: "PBMH_ades ?D = ?D"
    using assms A2_PBMH[of ?F] A2_PBMH[of ?T]
    by (simp add: Healthy_def' RA_design_as_disj PBMH_ades_disj
        PBMH_ades_not_ok_expr PBMH_ades_conj_ok)
  have A_absorb: "RA (A ?D) = RA ?D"
    by (simp only:
        RA_A[OF rad_wait_false_design_healthy, simplified comp_apply]
        design_pbmh)
  have "(rad_p2ac \<circ> rad_ac2p \<circ> RA \<circ> A) ?D =
      rad_p2ac (\<^bold>R ?C)"
    by (simp only: comp_apply
        rad_ac2p_RA_design[simplified comp_apply])
  also have "... = RA ?S"
    by (simp only: rad_p2ac_R[simplified comp_apply])
  also have "... = RA ?M"
    by (rule mapped_RA)
  also have "... = RA
      ((\<not> (ac_non_empty \<and> ?F)) \<turnstile>
        (ac_non_empty \<and> ?T))"
    by (simp only: F_round T_round)
  also have "... = RA ?D"
    by (rule nonempty_design_absorb)
  also have "... = (RA \<circ> A) ?D"
    by (simp only: comp_apply A_absorb)
  finally show ?thesis .
qed

end
