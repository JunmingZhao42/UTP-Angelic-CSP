section \<open>A2, A3 and Normal Angelic Designs\<close>

theory utp_ades_a2
  imports utp_ades_healthy
begin

subsection \<open>A2\<close>

(* {s} = ac' *)
definition singleton_ac :: "('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "singleton_ac = (\<lambda> (s0, ac').
  achoices.ac\<^sub>v ac' = {astate.s\<^sub>v s0})"

(* Paper Definition 20: A2 = PBMH (P ;; {s} = ac') *)
definition A2_rel ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where [pred]:
  "A2_rel P = PBMH (P ;;\<^sub>A singleton_ac)"

(* Paper Theorem 4: expanded form of @{const A2_rel}. *)
(* P[\<emptyset>/ac'] \<or> \<exists>y. y \<in> ac' P[{y'}/ac'] *)
definition A2_rel_expanded :: "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "A2_rel_expanded P = (\<lambda> (s0, ac').
  P (s0, achoices.ac\<^sub>v_update (\<lambda>_. {}) ac') \<or>
  (\<exists> y \<in> achoices.ac\<^sub>v ac'.
    P (s0, achoices.ac\<^sub>v_update (\<lambda>_. {y}) ac')))"

(* Paper Definition 36: some y in ac' is the single angelic choice
   admitted by P.  \<exists> y \<bullet> y \<in> ac' \<and> P[{y}/ac'] *)
definition ac_singleton_choice ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "ac_singleton_choice P = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v ac'.
    P (s0, achoices.ac\<^sub>v_update (\<lambda>_. {y}) ac'))"

(* A2 is determined by P on the empty and singleton choice sets. *)
lemma A2_rel_expanded_singleton_choice:
  "A2_rel_expanded P =
   ((\<lambda> (s0, ac'). P (s0, achoices.ac\<^sub>v_update (\<lambda>_. {}) ac')) \<or>
    ac_singleton_choice P)"
  by (pred_auto)

(* Paper Definition 36: \<exists> y \<bullet> y \<in> ac' \<and> P[{y}/ac']. *)
(* Binder form of the lifting: \<in>\<^sub>a\<^sub>c y. B binds the chosen
   state y in the body, as in the paper's notation. *)
definition ades_singleton_choice ::
  "('s \<Rightarrow> 's angelic_design) \<Rightarrow> 's angelic_design"
  (binder "\<in>\<^sub>a\<^sub>c " 10) where
[pred]: "ades_singleton_choice B = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    B y (s0, des_vars.more_update
        (achoices.ac\<^sub>v_update (\<lambda>_. {y})) ac'))"

abbreviation ades_singleton_choice_app ::
  "'s angelic_design \<Rightarrow> 's angelic_design" ("\<in>\<^sub>a\<^sub>c'(_')" [0] 999)
  where "\<in>\<^sub>a\<^sub>c(P) \<equiv> \<in>\<^sub>a\<^sub>c y. P"

lemma ades_singleton_choice_PBMH [simp]:
  "PBMH_ades (\<in>\<^sub>a\<^sub>c(P)) = \<in>\<^sub>a\<^sub>c(P)"
  by (simp add: PBMH_ades_def ades_singleton_choice_def fun_eq_iff;
      pred_auto; blast)

lemma ades_singleton_choice_ok_in_subst:
  "(\<in>\<^sub>a\<^sub>c(P))\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> =
   \<in>\<^sub>a\<^sub>c(P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: ades_singleton_choice_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

lemma ades_singleton_choice_unrest_ok [unrest]:
  assumes "$ok\<^sup>> \<sharp> P"
  shows "$ok\<^sup>> \<sharp> \<in>\<^sub>a\<^sub>c(P)"
proof -
  have put_P:
      "\<forall> s0 ac1 v. P (s0, ac1\<lparr>des_vars.ok\<^sub>v := v\<rparr>) = P (s0, ac1)"
    using assms
    apply (subst (asm) unrest_lens)
     apply simp
    by (simp add: lens_defs des_vars.ok_def case_prod_beta
        split_paired_All)
  show ?thesis
    apply (subst unrest_lens)
     apply simp
    apply (simp add: ades_singleton_choice_def lens_defs
        des_vars.ok_def case_prod_beta)
    using put_P
    by (simp add: des_more_ok_update_commute)
qed

text \<open>
  Paper Definition 20 in the expanded form of Theorem 4. A2 changes only
  the final choice set; the arbitrary input observation and the output
  termination flag are preserved.
\<close>
definition A2 ::
  "('\<beta>, 's achoices des_vars_ext) urel \<Rightarrow> ('\<beta>, 's achoices des_vars_ext) urel" where
[pred]: "A2 P \<equiv> (\<lambda>(s0, out).
  P (s0, des_vars.more_update
    (achoices.ac\<^sub>v_update (\<lambda>_. {})) out) \<or>
  (\<exists>y \<in> achoices.ac\<^sub>v (des_vars.more out).
    P (s0, des_vars.more_update
      (achoices.ac\<^sub>v_update (\<lambda>_. {y})) out)))"

(* Paper Theorem 4. *)
theorem A2_rel_eq_expanded: "A2_rel P = A2_rel_expanded P"
  apply (pred_auto)
  subgoal for s more ac morea X
    by (cases "\<exists> y. X = {y}", auto)
  subgoal for s more ac morea
    by (rule_tac x="{}" in exI, auto)
  subgoal for s more ac morea y
    by (rule_tac x="{y}" in exI, auto)
  done

lemma A2_rel_expanded_disj:
  "A2_rel_expanded (P \<or> Q) = (A2_rel_expanded P \<or> A2_rel_expanded Q)"
  by (simp add: A2_rel_expanded_def, pred_auto)

lemma A2_rel_expanded_idem:
  "A2_rel_expanded (A2_rel_expanded P) = A2_rel_expanded P"
  by (pred_auto)

lemma A2_rel_disj: "A2_rel (P \<or> Q) = (A2_rel P \<or> A2_rel Q)"
  by (simp add: A2_rel_eq_expanded A2_rel_expanded_disj)

lemma A2_rel_idem: "A2_rel (A2_rel P) = A2_rel P"
  by (simp add: A2_rel_eq_expanded A2_rel_expanded_idem)

lemma A2_rel_Idempotent [closure]: "Idempotent A2_rel"
  by (simp add: Idempotent_def A2_rel_idem)

lemma A2_rel_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A2_rel P \<sqsubseteq> A2_rel Q"
  by (simp add: A2_rel_eq_expanded, pred_auto; blast)

lemma A2_rel_Monotonic [closure]: "Monotonic A2_rel"
  by (rule MonotonicI, rule A2_rel_mono)

(* Paper Appendix Lemma 17. *)
lemma A2_rdesign:
  "A2 (B \<turnstile>\<^sub>r C) =
   ((\<not> A2_rel (\<not> B)) \<turnstile>\<^sub>r A2_rel C)"
  by (simp add: A2_def A2_rel_eq_expanded A2_rel_expanded_def
      rdesign_def design_def fun_eq_iff; pred_auto; blast)

lemma A2_output_obs:
  "A2 P (x, ades_output ok' X) \<longleftrightarrow>
    (P (x, ades_output ok' {}) \<or>
     (\<exists>y\<in>X. P (x, ades_output ok' {y})))"
  by (simp add: A2_def)

lemma A2_obs:
  "A2 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c {}) \<or>
     (\<exists>z\<in>X. P (ades_obs b s0 c {z})))"
  by (simp add: A2_output_obs)

lemma A2_idem: "A2 (A2 P) = A2 P"
  by (simp add: A2_def fun_eq_iff comp_def; blast)

lemma A2_Idempotent [closure]: "Idempotent A2"
  by (simp add: Idempotent_def A2_idem)

lemma A2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A2 P \<sqsubseteq> A2 Q"
  by (auto simp add: A2_def pred_refine_iff split: prod.splits)

lemma A2_Monotonic [closure]: "Monotonic A2"
  by (rule MonotonicI, rule A2_mono)

lemma A2_healthy [closure]: "A2 P is A2"
  by (simp add: Healthy_def' A2_idem)

lemma A2_def':
  "A2 P = PBMH_ades (P ;;\<^sub>A\<^sub>R \<lceil>singleton_ac\<rceil>\<^sub>D)"
  apply (simp add: A2_def PBMH_ades_def aseq_ades_def
      singleton_ac_def fun_eq_iff)
  apply pred_auto
  subgoal for ok s oka X
    by (rule_tac x="{}" in exI; auto)
  subgoal for ok s oka X y
    by (rule_tac x="{y}" in exI; auto)
  subgoal for ok s oka X ac
    by (cases "\<exists>y. ac = {y}"; auto)
  done

lemma PBMH_ades_A2 [simp]: "PBMH_ades (A2 P) = A2 P"
  by (simp add: PBMH_ades_def A2_def fun_eq_iff; pred_auto; blast)

lemma A_obs_A2:
  assumes "P is A2"
  shows "A P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not>b \<or> P (ades_obs True s0 False X) \<or>
      (c \<and> X \<noteq> {} \<and> P (ades_obs True s0 True X)))"
proof -
  have PB: "PBMH_ades P = P"
    using assms by (metis Healthy_def' PBMH_ades_A2)
  show ?thesis
    by (simp only: A_obs PBMH_ades_obs[symmetric] PB)
qed

lemma A_preserves_A2 [closure]:
  assumes "P is A2"
  shows "A P is A2"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c X
  have obs: "P (ades_obs True s0 d Y) \<longleftrightarrow>
    (P (ades_obs True s0 d {}) \<or> (\<exists>z\<in>Y. P (ades_obs True s0 d {z})))" for d Y
    using A2_obs[of P True s0 d Y] by (simp only: Healthy_if[OF assms])
  have up: "P (ades_obs True s0 True {}) \<Longrightarrow>
    P (ades_obs True s0 True {z})" for z
    using obs[of True "{z}"] by blast
  show "A2 (A P) (ades_obs b s0 c X) = A P (ades_obs b s0 c X)"
    apply (simp only: A2_obs A_obs_A2[OF assms])
    using obs[of False X] obs[of True X] up
    by blast
qed

lemma A2_false [simp]: "A2 false = false"
  by (simp add: A2_def fun_eq_iff; pred_auto)

lemma A2_state_choice [simp]:
  "A2 ades_state_choice = ades_state_choice"
  by (simp add: A2_def ades_state_choice_def fun_eq_iff)

lemma A2_true_design:
  "A2 (true \<turnstile> P) = (true \<turnstile> A2 P)"
  by (simp add: A2_def design_def fun_eq_iff; pred_auto; blast)

lemma A2_disj: "A2 (P \<or> Q) = (A2 P \<or> A2 Q)"
  by (simp add: A2_def fun_eq_iff; pred_auto; blast)

(* Thesis Theorem T.C.4.1. *)
lemma angelic_design_seq_A2_closure [closure]:
  assumes "P is A2" "Q is A2"
  shows "(P ;;\<^sub>A\<^sub>D Q) is A2"
proof -
  have "A2 (A2 P ;;\<^sub>A\<^sub>D A2 Q) = (A2 P ;;\<^sub>A\<^sub>D A2 Q)"
    by (simp add: A2_def angelic_design_seq_def fun_eq_iff comp_def; blast)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)] Healthy_def')
qed

(* Component characterisation for H-healthy designs. *)
lemma A2_components_iff:
  assumes "P is \<^bold>H"
  shows "P is A2 \<longleftrightarrow>
    (((\<not> pre\<^sub>D P) is A2_rel) \<and> (post\<^sub>D P is A2_rel))"
proof -
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using H1_H2_eq_rdesign[of P] by (simp only: Healthy_if[OF assms])
  have form: "A2 P =
      ((\<not> A2_rel (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r A2_rel (post\<^sub>D P))"
    using arg_cong[where f=A2, OF P_form]
    by (simp only: A2_rdesign)
  have post_eq: "post\<^sub>D (A2 P) =
      (A2_rel (\<not> pre\<^sub>D P) \<or> A2_rel (post\<^sub>D P))"
    by (simp only: form rdesign_post; pred_auto)
  have pre: "(\<not> pre\<^sub>D (A2 P)) is A2_rel"
    by (simp add: form arel_not_not Healthy_def' A2_rel_idem)
  have post: "post\<^sub>D (A2 P) is A2_rel"
    by (simp add: post_eq Healthy_def' A2_rel_disj A2_rel_idem)
  show ?thesis
  proof
    assume healthy: "P is A2"
    show "((\<not> pre\<^sub>D P) is A2_rel) \<and> (post\<^sub>D P is A2_rel)"
      using pre post by (simp only: Healthy_if[OF healthy]; simp)
  next
    assume "((\<not> pre\<^sub>D P) is A2_rel) \<and> (post\<^sub>D P is A2_rel)"
    then show "P is A2"
      using form P_form by (simp add: Healthy_def' arel_not_not)
  qed
qed

lemma A2_implies_neg_preD_A2_rel:
  assumes "P is \<^bold>H" "P is A2"
  shows "(\<not> pre\<^sub>D P) is A2_rel"
  using A2_components_iff[OF assms(1)] assms(2) by blast

subsection \<open>A3 Relation Healthiness (for supporting theorem 6)\<close>

(* A3_rel R \<equiv> R \<and> (ac' \<noteq> \<emptyset> \<or> \<exists>z. R(s, {z})) *)
(* todo: further simplification? *)
definition A3_rel :: "'s angelic_rel \<Rightarrow> 's angelic_rel" where
[pred]: "A3_rel R = (\<lambda>(s, ac').
  R (s, ac') \<and>
  (achoices.ac\<^sub>v ac' \<noteq> {} \<or>
    (\<exists>z. R (s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>))))"

lemma A3_rel_healthy':
  "R is A3_rel \<longleftrightarrow>
    (\<forall>s. R (s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<longrightarrow> (\<exists>z. R (s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>)))"
  by (simp add: Healthy_def' A3_rel_def fun_eq_iff; pred_auto)

lemma A3_rel_nonempty [simp]:
  fixes R :: "'s angelic_rel" and s :: "'s astate" and X :: "'s set"
  assumes "X \<noteq> {}"
  shows "A3_rel R (s, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>) = R (s, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>)"
  using assms by (simp add: A3_rel_def)

lemma A3_rel_empty [simp]:
  fixes R :: "'s angelic_rel" and s :: "'s astate"
  shows "A3_rel R (s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) =
    (R (s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<and> (\<exists>z. R (s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>)))"
  by (simp add: A3_rel_def)

(* The healthiness condition over angelic design to make sure that
  the design precondition is A3_rel-healthy (the singleton-witness condition) *)
definition A3 :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A3 P = (A3_rel (pre\<^sub>D P) \<turnstile>\<^sub>r post\<^sub>D P)"

lemma A3_is_H: "A3 P is \<^bold>H"
  by (simp add: A3_def rdesign_is_H1_H2)

text \<open>For a design, A3 adds empty-choice behaviour exactly when every
  singleton permits failure. Nonempty choice sets are unchanged.\<close>

lemma A3_obs:
  "A3 P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not>b \<or> P (ades_obs True s0 False X) \<or>
     (X = {} \<and> (\<forall>z. P (ades_obs True s0 False {z}))) \<or>
     (c \<and> P (ades_obs True s0 True X)))"
  apply (simp add: A3_def A3_rel_def rdesign_def design_def pre_design_def post_design_def)
  apply pred_auto
  apply (simp_all add: des_more_ok_update_commute des_vars_collapse)
  by auto

text \<open>An H1 and H3 relation is A3. Under H3, failure at one output admits every
  output, so failure at every singleton gives failure at the empty set.\<close>

lemma H1_H3_impl_A3:
  assumes "P is H1" "P is H3"
  shows "P is A3"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c Z
  have h3: "P (ades_obs b s0 c Z) \<longleftrightarrow>
    ((\<exists>Y. P (ades_obs b s0 False Y)) \<or> (c \<and> P (ades_obs b s0 True Z)))"
    for b s0 c Z
    using H3_obs[of P b s0 c Z] by (simp only: Healthy_if[OF assms(2)])
  have allfail: "(\<forall>z. P (ades_obs True s0 False {z})) \<Longrightarrow>
    P (ades_obs True s0 False {})"
    using h3[of True s0 False "{}"] by fastforce
  show "A3 P (ades_obs b s0 c Z) = P (ades_obs b s0 c Z)"
    apply (cases b)
    subgoal using h3[of True s0 c Z] allfail
      by (cases c; simp add: A3_obs; blast)
    subgoal using assms(1)[unfolded H1_healthy_obs_iff]
      by (simp add: A3_obs)
    done
qed

lemma A3_healthy:
  assumes "P is A"
  shows "P is A3 \<longleftrightarrow> pre\<^sub>D P is A3_rel"
proof
  assume a3_healthy: "P is A3"
  have "pre\<^sub>D (A3 P) = pre\<^sub>D P"
    using a3_healthy by (simp add: Healthy_def')
  then show "pre\<^sub>D P is A3_rel"
    by (simp add: Healthy_def' A3_def)
next
  assume pre_healthy: "pre\<^sub>D P is A3_rel"
  have design_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using assms A_is_H[of P] H1_H2_eq_rdesign[of P]
    by (simp add: Healthy_def')
  show "P is A3"
    using design_form pre_healthy
    by (simp add: Healthy_def' A3_def)
qed

lemma A3_rel_PBMH:
  fixes P :: "'s angelic_rel"
  shows "A3_rel (\<not> PBMH (\<not> P)) = (\<not> PBMH (\<not> A3_rel P))"
  apply (rule ext)
  subgoal for x
    apply (cases x)
    subgoal for s ac'
      apply (cases ac')
      subgoal for X
        apply (cases "X = {}")
        subgoal
          by (simp_all add: A3_rel_def neg_PBMH_eval;
              auto dest: subset_singletonD)
        subgoal
          by (simp_all add: A3_rel_def neg_PBMH_eval; blast)
        done
      done
    done
  done

lemma A3_rel_rdesign_post:
  "(A3_rel P \<turnstile>\<^sub>r [\<lambda>s. P s \<longrightarrow> Q s]\<^sub>e) = (A3_rel P \<turnstile>\<^sub>r Q)"
  apply (rule ref_antisym; rule rdesign_refine_intro;
      simp add: A3_rel_def; pred_auto)
  done

lemma A3_rel_mono:
  assumes "P \<sqsubseteq> Q"
  shows "A3_rel P \<sqsubseteq> A3_rel Q"
  using assms
  by (auto simp add: A3_rel_def pred_refine_iff split: prod.splits)

lemma A3_rel_Monotonic [closure]: "Monotonic A3_rel"
  by (rule MonotonicI, rule A3_rel_mono)

lemma A3_rel_idem: "A3_rel (A3_rel P) = A3_rel P"
  by (simp add: A3_rel_def fun_eq_iff; pred_auto)

lemma A3_rel_Idempotent [closure]: "Idempotent A3_rel"
  by (simp add: Idempotent_def A3_rel_idem)

lemma A3_mono:
  assumes "P \<sqsubseteq> Q"
  shows "A3 P \<sqsubseteq> A3 Q"
  apply (simp add: A3_def)
  apply (rule rdesign_refine_intro')
   apply (rule A3_rel_mono)
   apply (insert design_refine_thms(1)[OF assms])
   apply (pred_auto)
  apply (insert design_refine_thms(2)[OF assms])
  apply (simp add: A3_rel_def pred_refine_iff)
  apply (pred_auto)
  done

lemma A3_Monotonic [closure]: "Monotonic A3"
  by (rule MonotonicI, rule A3_mono)

lemma A3_idem: "A3 (A3 P) = A3 P"
  by (simp add: A3_def A3_rel_idem; pred_auto)

lemma A3_Idempotent [closure]: "Idempotent A3"
  by (simp add: Idempotent_def A3_idem)

lemma A3_A_commute: "A3 (A P) = A (A3 P)"
proof -
  have post_absorb:
      "\<And>P Q N :: 's angelic_rel.
        ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r
          (PBMH [\<lambda>s. P s \<longrightarrow> Q s]\<^sub>e \<and> N)) =
        ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r (PBMH Q \<and> N))"
    by (simp add: PBMH_disj rdesign_refinement fun_eq_iff; pred_auto)
  show ?thesis
    apply (simp add: A3_def A_design_form A3_rel_rdesign_post post_absorb)
    by (simp add: A3_rel_PBMH)
qed

lemma A3_A2_commute:
  "A3 (A2 P) = A2 (A3 P)"
  apply (simp add: A3_def A2_def A3_rel_def rdesign_def design_def
      fun_eq_iff)
  apply pred_auto
  apply (simp_all only: comp_def)
  apply (simp_all add: des_more_ok_update_commute des_vars_collapse)
  by blast+

(* other lemmas to show the compatibility *)
lemma A_preserves_A3: "P is A3 \<Longrightarrow> A P is A3"
  apply (simp add: Healthy_def' A3_A_commute)
  done

lemma A2_preserves_A3: "P is A3 \<Longrightarrow> A2 P is A3"
  apply (simp add: Healthy_def' A3_A2_commute)
  done

lemma A3_preserves_A: "P is A \<Longrightarrow> A3 P is A"
  apply (simp add: Healthy_def' A3_A_commute[symmetric])
  done

lemma A3_preserves_A2: "P is A2 \<Longrightarrow> A3 P is A2"
  apply (simp add: Healthy_def' A3_A2_commute[symmetric])
  done

subsection \<open>Support Laws\<close>

lemma PBMH_ades_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> PBMH_ades P"
  by (simp add: unrest_lens PBMH_ades_def PBMH_def pbmh_step_def
      fun_eq_iff Let_def; pred_auto; blast)

(* The angelic state choice requires a non-empty choice set. *)
lemma ades_state_choice_ac_non_empty_absorb:
  "(ac_non_empty \<and> ades_state_choice) = ades_state_choice"
  by (simp add: ades_state_choice_def ac_non_empty_def fun_eq_iff;
      pred_auto)

(* On an empty choice set the continuation of an angelic composition
   is immaterial: operands that agree there compose equally. *)
lemma aseq_ades_ac_empty_cong:
  assumes "((\<not> ac_non_empty) \<and> Y) = ((\<not> ac_non_empty) \<and> Z)"
  shows "((\<not> ac_non_empty) \<and> (T ;;\<^sub>A\<^sub>R Y)) =
    ((\<not> ac_non_empty) \<and> (T ;;\<^sub>A\<^sub>R Z))"
  using assms
  apply (simp add: aseq_ades_def ac_non_empty_def fun_eq_iff
      lens_defs des_vars.more\<^sub>L_def)
  apply pred_auto
  subgoal premises prems for ok s okv'
    using prems(2) prems(1)[rule_format, of "{}"] by simp
  subgoal premises prems for ok s okv'
    using prems(2) prems(1)[rule_format, of "{}"] by simp
  done

lemma A0_design_absorb:
  "$ok\<^sup>> \<sharp> X \<Longrightarrow> (ac_non_empty \<and> Y) = Y \<Longrightarrow>
   A0 ((\<not> X) \<turnstile> Y) = ((\<not> X) \<turnstile> Y)"
  by (simp add: A0_def unrest; pred_auto; blast)

lemma A0_design_gen:
  "$ok\<^sup>> \<sharp> X \<Longrightarrow>
   A0 (X \<turnstile> Y) = (X \<turnstile> (Y \<and> ac_non_empty))"
  by (simp add: A0_def unrest; pred_auto; blast)

lemma H2_disj: "H2 (P \<or> Q) = (H2 P \<or> H2 Q)"
  by (simp add: H2_split fun_eq_iff; pred_auto)

end
