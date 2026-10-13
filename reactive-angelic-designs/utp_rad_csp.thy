section \<open>Relationship with CSP\<close>

theory utp_rad_csp
  imports utp_rad_designs "UTP-Reactive-Designs.utp_rdes_healths"
begin

no_notation utp_rea_core.wait_f ("_\<^sub>f" [1000] 1000)

subsection \<open>Direct relation and design mappings\<close>

text \<open>The ordinary reactive alphabet is exactly the design alphabet over
  @{typ "('t::trace, 'e) rad_state"}. The generic AD mappings therefore apply
  directly as @{term p2ac}, @{term ac2p}, and @{term d2ac}.\<close>

lemma rad_p2ac_PBMH_ades [closure]: "p2ac P is PBMH_ades"
  by (simp add: Healthy_def)

lemma rad_p2ac_design_nonempty:
  "(ac_non_empty \<and> p2ac ((\<not> F) \<turnstile> T)) =
   (ac_non_empty \<and> ((\<not> p2ac F) \<turnstile> p2ac T))"
  by (simp only: comp_apply
      p2ac_design_nonempty)

lemma rad_ac2p_disj: "ac2p (P \<or> Q) = (ac2p P \<or> ac2p Q)"
  by (simp add: ac2p_disj)

lemma rad_p2ac_disj: "p2ac (P \<or> Q) = (p2ac P \<or> p2ac Q)"
  by (simp add: p2ac_disj)

lemma rad_p2ac_conj:
  "(p2ac P \<and> p2ac Q) \<sqsubseteq> p2ac (P \<and> Q)"
  by (rule p2ac_conj)

lemma rad_ac2p_d2ac:
  assumes "P is \<^bold>H"
  shows "(ac2p \<circ> d2ac) P = P"
  by (simp add:
      ac2p_d2ac[simplified comp_apply] assms)

subsection \<open>From reactive angelic designs to CSP\<close>

(* Thesis Theorem T.G.7.1. *)
lemma rad_ac2p_RA1:
  assumes "P is PBMH_ades"
  shows "(ac2p \<circ> RA1) P = (R1 \<circ> ac2p) P"
  using assms RA1_PBMH_ades_closure[OF assms]
  apply (simp only: comp_apply ac2p_def
      Healthy_def')
  apply (simp add: R1_def RA1_def
      rad_trace_extensions_def StateII_def fun_eq_iff Let_def)
  apply pred_auto
  done

(* Thesis Theorem T.G.7.2. *)
lemma rad_ac2p_RA1_RA2:
  assumes "P is PBMH_ades"
  shows "(ac2p \<circ> RA1 \<circ> RA2) P =
    (R1 \<circ> R2 \<circ> ac2p) P"
proof -
  have ra2_healthy: "RA2 P is PBMH_ades"
    by (rule RA2_PBMH_ades_closure[OF assms])
  have ra1_ra2_healthy: "RA1 (RA2 P) is PBMH_ades"
    by (rule RA1_PBMH_ades_closure[OF ra2_healthy])
  show ?thesis
    using assms ra2_healthy ra1_ra2_healthy
    apply (simp only: comp_apply ac2p_def
        Healthy_def')
    apply (simp add: RA1_def RA2_def R1_def R2_def R2s_def
         rad_trace_extensions_def rad_zero_trace_def
        rad_normalise_choices_def rad_trace_difference_def StateII_def
        fun_eq_iff Let_def)
    apply pred_auto
    done
qed

lemma rad_ac2p_II_Rac [simp]:
  "ac2p (II_Rac :: ('t::trace, 'e) reactive_angelic_design) = II\<^sub>C"
  apply (simp only: comp_apply ac2p_def
      PBMH_ades_II_Rac)
  apply (simp add: II_Rac_def RA1_def
      rad_trace_extensions_def StateII_def skip_rea_def pred_skip
      fun_eq_iff Let_def lens_defs)
  apply pred_auto
  done

(* Thesis Theorem T.G.7.3. *)
lemma rad_ac2p_RA3: "(ac2p \<circ> RA3) P = (R3c \<circ> ac2p) P"
proof -
  have ac2p_wait:
      "ac2p (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
       (ac2p P \<triangleleft> $rea_vars.wait\<^sup>< \<triangleright> ac2p Q)"
      for P Q
    by (simp only: comp_apply ac2p_def
          PBMH_ades_wait_cond;
        simp add: expr_if_def fun_eq_iff lens_defs;
        pred_auto)
  show ?thesis
    by (simp add: RA3_def R3c_def ac2p_wait)
qed

(* Paper Theorem 12 / Thesis Theorem T.5.3.1. *)
theorem rad_ac2p_RA:
  assumes "P is PBMH_ades"
  shows "(ac2p \<circ> RA) P = (\<^bold>R \<circ> ac2p) P"
  by (simp add: RA_def RA1_RA3_commute' RA2_RA3_commute'
      rad_ac2p_RA3[simplified comp_apply]
      rad_ac2p_RA1_RA2[simplified comp_apply] assms R2_def RH_def R1_idem
      R1_R3c_commute R2c_R3c_commute R1_R2s_R2c)

(* Paper Theorem 13 / Thesis Theorem T.5.3.2. *)
theorem rad_ac2p_RA_design:
  "(ac2p \<circ> RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t) =
   \<^bold>R ((\<not> ac2p ((P \<^sub>f)\<^sup>f)) \<turnstile> ac2p ((P \<^sub>f)\<^sup>t))"
proof -
  let ?D = "(\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t"
  have design_healthy: "?D is \<^bold>H"
    by (rule rad_wait_false_design_is_H)
  have pbmh_healthy: "PBMH_ades ?D is PBMH_ades"
    by (rule Healthy_Idempotent[OF PBMH_ades_Idempotent])
  have mapped_ac2p: "ac2p ?D = ((\<not> ac2p ((P \<^sub>f)\<^sup>f)) \<turnstile> ac2p ((P \<^sub>f)\<^sup>t))"
    by (subst ac2p_design[OF design_healthy];
        simp add: design_def fun_eq_iff
          subst_app_def subst_upd_def subst_id_def SEXP_def;
        pred_auto)
  have mapped_design:
    "ac2p ?D = ((\<not> ac2p ((P \<^sub>f)\<^sup>f)) \<turnstile> ac2p ((P \<^sub>f)\<^sup>t))"
    unfolding comp_apply
    by (simp only: mapped_ac2p)
  have "ac2p (RA (A ?D)) =
      ac2p (RA (PBMH_ades ?D))"
    by (simp only: RA_A'[OF design_healthy])
  also have "... = \<^bold>R (ac2p (PBMH_ades ?D))"
    by (rule rad_ac2p_RA[OF pbmh_healthy, simplified comp_apply])
  also have "... = \<^bold>R (ac2p ?D)"
    by (simp only: comp_apply ac2p_PBMH_ades)
  also have "... = \<^bold>R ((\<not> ac2p ((P \<^sub>f)\<^sup>f)) \<turnstile> ac2p ((P \<^sub>f)\<^sup>t))"
    by (simp only: mapped_design)
  finally show ?thesis
    by (simp only: comp_apply)
qed

lemmas rad_ac2p_RA_design' = rad_ac2p_RA_design[simplified comp_apply]

(* Theorems 11 and 13 give the CSP image of a RAD-healthy predicate.
   Theorem 13 uses Theorem 12 to transport RA healthiness to R healthiness. *)
lemma rad_ac2p_RAD:
  assumes "P is RAD"
  shows "ac2p P = \<^bold>R ((\<not> ac2p ((P \<^sub>f)\<^sup>f)) \<turnstile> ac2p ((P \<^sub>f)\<^sup>t))"
proof -
  have "ac2p P = ac2p ((RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t))"
    by (rule arg_cong[where f=ac2p, OF RAD_design_form'[OF assms]])
  also have "... = \<^bold>R ((\<not> ac2p ((P \<^sub>f)\<^sup>f)) \<turnstile> ac2p ((P \<^sub>f)\<^sup>t))"
    unfolding comp_apply
    by (rule rad_ac2p_RA_design')
  finally show ?thesis .
qed

lemma rad_ac2p_RAD_healthy:
  assumes "P is RAD"
  shows "ac2p P is \<^bold>R"
  using rad_ac2p_RAD[OF assms]
  by (simp add: Healthy_def' RH_idem)

subsection \<open>From CSP to reactive angelic designs\<close>

(* Thesis Theorem T.G.7.8. *)
lemma rad_p2ac_R1: "(p2ac \<circ> R1) P = (RA1 \<circ> p2ac) P"
  apply (rule ades_obs_ext)
  subgoal for b s c X
    by (cases b; cases c; simp add: p2ac_def RA1_def R1_def rad_trace_extensions_def
        expr_defs lens_defs alpha_defs Let_def conj_pred_def
        disj_pred_def not_pred_def; blast)
  done

(* Thesis Theorem T.G.7.9. *)
lemma rad_p2ac_R1_R2:
  "(p2ac \<circ> R1 \<circ> R2) P = (RA2 \<circ> p2ac) P"
  apply (rule ades_obs_ext)
  subgoal for b s c X
    by (cases b; cases c;
        auto simp: p2ac_def RA2_def R2_def R2s_def R1_def
          rad_normalise_choices_def rad_trace_difference_def rad_zero_trace_def
          expr_defs lens_defs alpha_defs Let_def conj_pred_def)
  done

(* Thesis Lemma L.G.7.2: reactive identity. *)
lemma rad_p2ac_II_C [simp]:
  "p2ac (II\<^sub>C :: ('t::trace, 'e set) rp_hrel) = II_Rac"
  apply (rule ades_obs_ext)
  subgoal for b s c X
    by (cases b; cases c; simp add: p2ac_def II_Rac_def RA1_def rad_trace_extensions_def
        skip_rea_def pred_skip expr_defs lens_defs alpha_defs Let_def conj_pred_def disj_pred_def not_pred_def; blast)
  done

(* Thesis Theorem T.G.7.10. *)
lemma rad_p2ac_R3: "(p2ac \<circ> R3c) P = (RA3 \<circ> p2ac) P"
proof -
  have p2ac_wait:
      "p2ac (P \<triangleleft> $rea_vars.wait\<^sup>< \<triangleright> Q) =
       (p2ac P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> p2ac Q)"
      for P Q
    by (simp add: p2ac_def
        expr_if_def fun_eq_iff lens_defs alpha_defs; pred_auto)
  show ?thesis
    by (simp add: R3c_def RA3_def p2ac_wait)
qed

(* Paper Theorem 14. *)
theorem rad_p2ac_R:
  "(p2ac \<circ> \<^bold>R) P = (RA \<circ> p2ac) P"
proof -
  have "p2ac (\<^bold>R P) =
      p2ac (R3c (R1 (R2 P)))"
    by (simp add: RH_def R2_def R1_R3c_commute
        R2c_R3c_commute R1_R2s_R2c R1_idem)
  also have "... = RA3 (p2ac (R1 (R2 P)))"
    by (simp only: rad_p2ac_R3[simplified comp_apply])
  also have "... = RA3 (RA1 (p2ac (R1 (R2 P))))"
    by (simp add: rad_p2ac_R1[simplified comp_apply] RA1_idem)
  also have "... = RA3 (RA1 (RA2 (p2ac P)))"
    by (simp only: rad_p2ac_R1_R2[simplified comp_apply])
  also have "... = RA (p2ac P)"
    by (simp add: RA_def RA1_RA3_commute' RA2_RA3_commute')
  finally show ?thesis
    by simp
qed

lemmas rad_p2ac_R' = rad_p2ac_R[simplified comp_apply]

(* After fixing ok' and wait in the source, the mapped predicate no
   longer depends on ok'. *)
lemma rad_p2ac_subst_unrest_ok:
  "$ok\<^sup>> \<sharp>
    p2ac (wait_f (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk>))"
  apply (simp add: unrest_lens p2ac_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma rad_p2ac_wait_false_ok:
  "(((p2ac P) \<^sub>f)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk>) =
   p2ac (wait_f (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk>))"
  by (auto simp add: p2ac_def
      rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs rad_wait_def rea_vars.wait_def astate.s_def
      des_vars.more\<^sub>L_def des_vars.ok_def comp_def split: prod.splits)

(* A reactive design maps componentwise when the mapped failure and
   success predicates are independent of final ok. *)
lemma rad_p2ac_R_design_components:
  assumes "$ok\<^sup>> \<sharp> p2ac F" "$ok\<^sup>> \<sharp> p2ac T"
  shows "p2ac (\<^bold>R ((\<not> F) \<turnstile> T)) =
    (RA \<circ> A) ((\<not> p2ac F) \<turnstile> p2ac T)"
proof -
  have "p2ac (\<^bold>R ((\<not> F) \<turnstile> T)) =
      RA ((\<not> p2ac F) \<turnstile> p2ac T)"
    by (simp only: rad_p2ac_R' RA_cong_ac_non_empty[OF rad_p2ac_design_nonempty])
  also have "... = (RA \<circ> A) ((\<not> p2ac F) \<turnstile> p2ac T)"
    apply (rule RA_A_absorb_design[symmetric])
       apply (simp only: pred_ba.double_compl; rule rad_p2ac_PBMH_ades)
      apply (rule rad_p2ac_PBMH_ades)
     apply (simp add: unrest assms)
    by (rule assms(2))
  finally show ?thesis .
qed

(* Paper Theorem 15 / Thesis Theorem T.5.3.4. *)
theorem rad_p2ac_R_design:
  "(p2ac \<circ> \<^bold>R) ((\<not> wait_f (P\<^sup>f)) \<turnstile> wait_f (P\<^sup>t)) =
   (RA \<circ> A) ((\<not> p2ac (wait_f (P\<^sup>f))) \<turnstile> p2ac (wait_f (P\<^sup>t)))"
  unfolding comp_apply
  by (rule rad_p2ac_R_design_components[simplified comp_apply];
      rule rad_p2ac_subst_unrest_ok)

subsection \<open>Isomorphism and Galois Connection\<close>

(* Paper Theorem 16 / Thesis Theorem T.5.3.5. *)
theorem rad_ac2p_p2ac_inverse: "(ac2p \<circ> p2ac) P = P"
  by (simp add: ac2p_subset p2ac_def StateII_def fun_eq_iff; pred_auto)

lemmas rad_ac2p_p2ac_inverse' = rad_ac2p_p2ac_inverse[simplified comp_apply]

(* Paper Lemma 6. *)
lemma rad_p2ac_ac2p:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "(p2ac \<circ> ac2p) P =
    (\<lambda> (s0, ac'). \<exists> ac0 y.
      P (s0, des_vars.more_update
        (achoices.ac\<^sub>v_update (\<lambda>_. ac0)) ac') \<and>
      ac0 \<subseteq> {y} \<and> y \<in> achoices.ac\<^sub>v (des_vars.more ac'))"
  by (rule ades_obs_ext; auto simp: p2ac_def ac2p_subset StateII_def)

lemma rad_p2ac_ac2p_A2_form:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "(p2ac \<circ> ac2p) P = (ac_non_empty \<and> A2 P)"
  by (rule ades_obs_ext;
      auto simp: p2ac_def ac2p_subset StateII_def A2_def ac_non_empty_def
        conj_pred_def subset_singleton_iff expr_defs lens_defs alpha_defs)

(* Paper Theorem 17. *)
theorem rad_p2ac_ac2p_refine:
  assumes "P is PBMH_ades"
  shows "P \<sqsubseteq> (p2ac \<circ> ac2p) P"
  using assms
  apply (simp only: Healthy_def' rad_p2ac_ac2p)
  apply (simp add: PBMH_ades_def pred_refine_iff)
  by (pred_auto; blast)

lemmas rad_p2ac_ac2p_refine' = rad_p2ac_ac2p_refine[simplified comp_apply]

(* Thesis Lemma L.G.7.11. *)
lemma rad_p2ac_ac2p_A2:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is A2"
  shows "(p2ac \<circ> ac2p) P = (ac_non_empty \<and> P)"
  by (simp only: rad_p2ac_ac2p_A2_form Healthy_if[OF assms])

(* Paper Theorem 18 / Thesis Theorem T.5.3.7. *)
theorem rad_p2ac_ac2p_RA_design:
  assumes "(P \<^sub>f)\<^sup>f is A2"
    and "(P \<^sub>f)\<^sup>t is A2"
  shows "(p2ac \<circ> ac2p \<circ> RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t) = (RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t)"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  let ?D = "(\<not> ?F) \<turnstile> ?T"
  let ?C = "(\<not> ac2p ?F) \<turnstile> ac2p ?T"
  let ?M = "((\<not> (p2ac \<circ> ac2p) ?F) \<turnstile>
    (p2ac \<circ> ac2p) ?T)"
  have mapped: "RA (p2ac ?C) = RA ?M"
    apply (rule RA_cong_ac_non_empty)
    using p2ac_design_nonempty[
        of " (ac2p ?F)"
           " (ac2p ?T)"]
    by (simp)
  have round:
      "(p2ac \<circ> ac2p) ?F = (ac_non_empty \<and> ?F)"
      "(p2ac \<circ> ac2p) ?T = (ac_non_empty \<and> ?T)"
    by (rule rad_p2ac_ac2p_A2[OF assms(1)])
       (rule rad_p2ac_ac2p_A2[OF assms(2)])
  have remove_nonempty:
      "RA ((\<not> (ac_non_empty \<and> ?F)) \<turnstile>
          (ac_non_empty \<and> ?T)) = RA ?D"
    by (simp only:
        RA_design_components[
          of "\<not> (ac_non_empty \<and> ?F)" "ac_non_empty \<and> ?T"]
        RA_design_components[of "\<not> ?F" ?T]
        pred_ba.boolean_algebra.double_compl
        RA1_ac_non_empty_absorb)
  have D_PBMH: "?D is PBMH_ades"
    using assms PBMH_ades_A2[of ?F] PBMH_ades_A2[of ?T]
    by (simp add: Healthy_def' design_as_disj PBMH_ades_disj
        PBMH_ades_not_ok_expr PBMH_ades_conj_ok)
  have "(p2ac \<circ> ac2p \<circ> RA \<circ> A) ?D =
      RA (p2ac ?C)"
    by (simp only: comp_apply rad_ac2p_RA_design' rad_p2ac_R')
  also have "... = RA ?M"
    by (rule mapped)
  also have "... = RA
      ((\<not> (ac_non_empty \<and> ?F)) \<turnstile>
        (ac_non_empty \<and> ?T))"
    by (simp only: round)
  also have "... = RA ?D"
    by (rule remove_nonempty)
  also have "... = (RA \<circ> A) ?D"
    by (rule RA_A_absorb[OF D_PBMH rad_wait_false_design_is_H, symmetric])
  finally show ?thesis .
qed

lemma rad_p2ac_ac2p_RAD_A2:
  assumes "P is RAD" "P is A2"
  shows "(p2ac \<circ> ac2p) P = P"
proof -
  have nonempty: "(ac_non_empty \<and> P) = P"
    apply (subst (1 2) Healthy_if[OF assms(1), symmetric])
    unfolding RAD_def comp_apply
    by (rule RA_ac_non_empty_absorb)
  show ?thesis
    by (simp only: rad_p2ac_ac2p_A2_form Healthy_if[OF assms(2)] nonempty)
qed

lemmas rad_p2ac_ac2p_RAD_A2' = rad_p2ac_ac2p_RAD_A2[simplified comp_apply]

end
