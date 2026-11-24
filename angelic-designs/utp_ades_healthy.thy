section \<open>Angelic Design Healthiness Conditions\<close>

(* Paper Section 5.1, Definition 17. *)

theory utp_ades_healthy
  imports utp_ades_pbmh
begin

subsection \<open>A0\<close>

definition ac_non_empty :: "'s angelic_design" where
[pred]: "ac_non_empty = \<lceil>($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e\<rceil>\<^sub>D"

lemma ac_non_empty_ok_out_subst [usubst]:
  "ac_non_empty\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk> = ac_non_empty"
  by pred_auto

(* The design-level lifting of paper Lemma 15. *)
lemma PBMH_ades_ac_non_empty [simp]:
  "PBMH_ades ac_non_empty = ac_non_empty"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def ac_non_empty_def
      fun_eq_iff; pred_auto)

definition A0 :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A0 P = (P \<and> ((ok\<^sup>< \<and> \<not> P\<^sup>f) \<longrightarrow> (ok\<^sup>> \<longrightarrow> ac_non_empty)))"

lemma A0_obs:
  "A0 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c X) \<and>
      (b \<and> c \<and> X = {} \<longrightarrow> P (ades_obs b s0 False X)))"
  by (simp add: A0_def; pred_auto)

lemma A0_healthy_obs_iff:
  fixes P :: "'s angelic_design"
  shows "P is A0 \<longleftrightarrow>
    (\<forall>s0. P (ades_obs True s0 True {}) \<longrightarrow>
      P (ades_obs True s0 False {}))"
proof
  assume h: "P is A0"
  show "\<forall>s0. P (ades_obs True s0 True {}) \<longrightarrow>
    P (ades_obs True s0 False {})"
    using A0_obs[of P True _ True "{}"] h
    by (simp only: Healthy_if; blast)
next
  assume h: "\<forall>s0. P (ades_obs True s0 True {}) \<longrightarrow>
    P (ades_obs True s0 False {})"
  show "P is A0"
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: A0_obs; insert h; auto)
qed

lemma A0_idem: "A0 (A0 P) = A0 P"
  by (pred_auto)

lemma A0_Idempotent [closure]: "Idempotent A0"
  by (simp add: Idempotent_def A0_idem)

lemma A0_mono: "P \<sqsubseteq> Q \<Longrightarrow> A0 P \<sqsubseteq> A0 Q"
  by (pred_auto)

lemma A0_Monotonic [closure]: "Monotonic A0"
  by (rule MonotonicI, rule A0_mono) 

lemma A0_state_subst:
  "ades_state_subst st_subst (A0 P) = A0 (ades_state_subst st_subst P)"
  by (simp add: A0_def, pred_auto)

(* Paper Theorem 3. *)
theorem A0_design: "A0 ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t) = ((\<not> P\<^sup>f) \<turnstile> (P\<^sup>t \<and> ac_non_empty))"
  by pred_auto

lemma A0_healthy_non_empty:
  assumes "P is A0" "P (s0, out)"
    "des_vars.ok\<^sub>v s0"
    "\<not> P (s0, ok\<^sub>v_update (\<lambda>_. False) out)"
    "des_vars.ok\<^sub>v out"
  shows "achoices.ac\<^sub>v (des_vars.more out) \<noteq> {}"
proof -
  have fixed: "A0 P = P"
    using assms(1) by (simp add: Healthy_def')
  have fixed_at: "A0 P (s0, out) = P (s0, out)"
    by (simp only: fixed)
  show ?thesis
    using fixed_at assms(2-)
    by (cases s0; cases out; simp add: A0_def; pred_auto)
qed

subsection \<open>A1\<close>

definition A1 :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A1 P = ((\<not> PBMH (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r PBMH (post\<^sub>D P))"

lemma A1_obs:
  "A1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not> b \<or> (\<exists>Y\<subseteq>X. P (ades_obs True s0 False Y)) \<or>
      (c \<and> (\<exists>Y\<subseteq>X. P (ades_obs True s0 True Y))))"
  apply (simp add: A1_def)
  apply pred_simp
  by (auto simp: des_vars_collapse)

lemma A1_is_H: "A1 P is \<^bold>H"
  by (simp add: A1_def rdesign_is_H1_H2)

(* Paper Lemma 16. Putting a design in PBMH. *)
lemma PBMH_rdesign:
  "A1 (P \<turnstile>\<^sub>r Q) = ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r PBMH Q)"
  by (simp add: A1_def PBMH_disj rdesign_refinement, pred_auto)

lemma A1_PBMH_ades_rdesign:
  "A1 (P \<turnstile>\<^sub>r Q) = PBMH_ades (P \<turnstile>\<^sub>r Q)"
  by (simp add: PBMH_rdesign PBMH_ades_rdesign)

(* Paper Definition 17 defines A1 on designs and observes that A1 and PBMH are
   interchangeable.  In the shallow embedding, H records that an arbitrary
   predicate P is a design. *)
lemma A1_eq_PBMH_ades:
  assumes "P is \<^bold>H"
  shows "A1 P = PBMH_ades P"
  using A1_PBMH_ades_rdesign[of "pre\<^sub>D P" "post\<^sub>D P"]
    H1_H2_eq_rdesign[of P] assms
  by (simp add: Healthy_def')

lemma A1_state_subst:
  "ades_state_subst st_subst (A1 P) = A1 (ades_state_subst st_subst P)"
proof -
  have pre_subst:
    "pre\<^sub>D (ades_state_subst st_subst P) = arel_state_subst st_subst (pre\<^sub>D P)"
    apply (pred_auto)
     apply (simp add: des_vars_update_commute)
    apply (simp add: des_vars_update_commute)
    done
  have post_subst:
    "post\<^sub>D (ades_state_subst st_subst P) = arel_state_subst st_subst (post\<^sub>D P)"
    apply (pred_auto)
     apply (simp add: des_vars_update_commute)
    apply (simp add: des_vars_update_commute)
    done
  show ?thesis
    unfolding A1_def
    apply (simp add: PBMH_state_subst usubst)
    apply (simp add: pre_subst post_subst)
    done
qed

lemma A1_idem: "A1 (A1 P) = A1 P"
  by (pred_auto)

lemma A1_Idempotent [closure]: "Idempotent A1"
  by (simp add: Idempotent_def A1_idem)

lemma A1_mono: "P \<sqsubseteq> Q \<Longrightarrow> A1 P \<sqsubseteq> A1 Q"
  apply (simp add: A1_def)
  apply (rule rdesign_refine_intro')
   apply (rule PBMH_neg_guard)
   apply (insert design_refine_thms(1)[of P Q])
   apply (pred_auto)
  apply (rule_tac y="PBMH (pre\<^sub>D P \<and> post\<^sub>D Q)" in pred_ba.order_trans)
   apply (rule PBMH_guarded_post)
  apply (rule PBMH_mono)
  apply (insert design_refine_thms(2)[of P Q])
  apply (pred_auto)
  done

lemma A1_Monotonic [closure]: "Monotonic A1"
  by (rule MonotonicI, rule A1_mono)

subsection \<open>A\<close>

definition A :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A P = A0 (A1 P)"

lemma A_comp: "A = A0 \<circ> A1"
  by (auto simp add: A_def)

lemma A_mono: "P \<sqsubseteq> Q \<Longrightarrow> A P \<sqsubseteq> A Q"
  by (simp add: A_def A0_mono A1_mono)

lemma A_Monotonic [closure]: "Monotonic A"
  by (rule MonotonicI, rule A_mono)

lemma A_design_form:
  "A P =
   ((\<not> PBMH (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r
     (PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
  by (pred_auto)

lemma A_obs:
  "A P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not> b \<or> (\<exists>Y \<subseteq> X. P (ades_obs True s0 False Y)) \<or>
      (c \<and> X \<noteq> {} \<and> (\<exists>Y \<subseteq> X. P (ades_obs True s0 True Y))))"
  apply (simp add: A_design_form)
  apply pred_simp
  by (auto simp: des_vars_collapse)

(* A over the ok'-substituted design of a predicate, in \<turnstile> form. *)
lemma A_design:
  "A ((\<not> Q\<^sup>f) \<turnstile> Q\<^sup>t) =
   ((\<not> PBMH_ades (Q\<^sup>f)) \<turnstile> (PBMH_ades (Q\<^sup>t) \<and> ac_non_empty))"
  by (pred_auto; auto simp add: des_vars_collapse)

(* Thesis Theorem T.4.5.11 *)
lemma A_disj: "A (P \<or> Q) = (A P \<or> A Q)"
  by (simp add: A_design_form preD_disj postD_disj PBMH_disj rdesign_choice'
      pred_ba.boolean_algebra.conj_disj_distrib
      pred_ba.boolean_algebra.conj_disj_distrib2)

lemma A_demonic:
  "A (P \<sqinter>\<^sub>A\<^sub>D Q) = (A P \<sqinter>\<^sub>A\<^sub>D A Q)"
  by (simp add: angelic_design_demonic A_disj)

(* Thesis Theorem T.4.5.12 *)
lemma A_demonic_closure:
  assumes "P is A" "Q is A"
  shows "A (P \<sqinter>\<^sub>A\<^sub>D Q) = (P \<sqinter>\<^sub>A\<^sub>D Q)"
  using assms by (simp add: A_demonic Healthy_def')

(* Thesis Theorem T.4.5.16. *)
lemma A_angelic_closure:
  assumes "P is A" "Q is A"
  shows "P \<squnion>\<^sub>A\<^sub>D Q is A"
proof -
  let ?N = "($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  let ?PF = "PBMH (\<not> pre\<^sub>D P)"
  let ?PT = "PBMH (post\<^sub>D P)"
  let ?QF = "PBMH (\<not> pre\<^sub>D Q)"
  let ?QT = "PBMH (post\<^sub>D Q)"
  let ?Pre = "(\<not> ?PF) \<or> (\<not> ?QF)"
  let ?Post =
    "(?PF \<or> (?PT \<and> ?N)) \<and>
     (?QF \<or> (?QT \<and> ?N))"
  let ?PostD = "(?PF \<and> ?QF) \<or> ?Post"
  let ?DP = "(\<not> ?PF) \<turnstile>\<^sub>r (?PT \<and> ?N)"
  let ?DQ = "(\<not> ?QF) \<turnstile>\<^sub>r (?QT \<and> ?N)"

  have P_form: "P = ?DP"
    using assms(1) by (simp add: Healthy_def' A_design_form)
  have Q_form: "Q = ?DQ"
    using assms(2) by (simp add: Healthy_def' A_design_form)
  have choice_form:
      "P \<squnion>\<^sub>A\<^sub>D Q = (?Pre \<turnstile>\<^sub>r ?Post)"
    apply (subst P_form)
    apply (subst Q_form)
    apply (simp only: rdesign_inf)
    by pred_auto

  have pre_not: "(\<not> ?Pre) = (?PF \<and> ?QF)"
    by pred_auto
  have pre_healthy: "(?PF \<and> ?QF) is PBMH"
    by (intro PBMH_conj_closure PBMH_healthy)
  have pre_norm: "PBMH (\<not> ?Pre) = (?PF \<and> ?QF)"
    using pre_healthy by (simp add: pre_not Healthy_def')

  have post_of_design:
      "post\<^sub>D (?Pre \<turnstile>\<^sub>r ?Post) = ?PostD"
    by pred_auto
  have post_healthy: "?PostD is PBMH"
    by (intro PBMH_disj_closure PBMH_conj_closure PBMH_healthy;
        simp add: Healthy_def')
  have post_norm:
      "PBMH (post\<^sub>D (?Pre \<turnstile>\<^sub>r ?Post)) = ?PostD"
    using post_healthy by (simp only: post_of_design Healthy_def')

  show ?thesis
    apply (simp only: choice_form Healthy_def')
    apply (simp only: A_design_form rdesign_pre post_of_design
        pre_norm post_norm)
    by (rule ref_antisym; rule rdesign_refine_intro; pred_simp; blast)
qed

(* Thesis Theorem T.4.5.14 *)
lemma angelic_design_demonic_bottom:
  "P \<sqinter>\<^sub>A\<^sub>D \<bottom>\<^sub>D = \<bottom>\<^sub>D"
  by (simp add: angelic_design_demonic bot_d_true)

lemma A_idem: "A (A P) = A P"
  apply (simp add: A_design_form PBMH_idem)
  apply (rule pred_ba.order_antisym)
   apply (rule rdesign_refine_intro)
    apply pred_auto
   apply (pred_simp; blast)
  apply (rule rdesign_refine_intro)
   apply pred_auto
  apply (pred_simp; blast)
  done

lemma A_Idempotent [closure]: "Idempotent A"
  by (simp add: Idempotent_def A_idem)

lemma A_H1_commute: "(H1 \<circ> A) P = (A \<circ> H1) P"
  by (simp add: A_design_form H1_rdesign preD_H1 postD_H1)

lemma A_H2_commute: "(H2 \<circ> A) P = (A \<circ> H2) P"
proof -
  have post_absorb:
    "\<And>P Q N.
      ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r ((PBMH (\<not> P) \<or> PBMH Q) \<and> N)) =
      ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r (PBMH Q \<and> N))"
    apply (rule pred_ba.order_antisym)
     apply (rule rdesign_refine_intro; pred_auto)
    apply (rule rdesign_refine_intro; pred_auto)
    done
  show ?thesis
    by (simp add: A_design_form H2_rdesign preD_H2 postD_H2 PBMH_disj post_absorb)
qed

(* Paper Lemma 18: state substitution commutes with A. *)
lemma A_state_subst:
  "ades_state_subst st_subst (A P) = A (ades_state_subst st_subst P)"
  by (simp add: A_def A0_state_subst A1_state_subst)

lemma A_is_H1: "H1 (A P) = A P"
  by (simp add: A_design_form H1_rdesign)

lemma A_is_H2: "H2 (A P) = A P"
  by (simp add: A_design_form H2_rdesign)

lemma A_is_H: "\<^bold>H (A P) = A P"
  by (simp add: A_design_form H1_rdesign H2_rdesign)

lemma A_healthy_design_form:
  "P is A \<Longrightarrow> P =
   ((\<not> PBMH (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r
     (PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
  by (simp add: A_design_form Healthy_def')

(* corollary *)
lemma A_healthy_complete_lattice:
  "complete_lattice (fpl \<P> (A :: 's angelic_design \<Rightarrow> 's angelic_design))"
proof -
  interpret weak_complete_lattice "fpl \<P> (A :: 's angelic_design \<Rightarrow> 's angelic_design)"
    by (rule Knaster_Tarski, auto simp add: A_Monotonic)
  show ?thesis
    by (unfold_locales, simp add: fps_def sup_exists,
        (blast intro: sup_exists inf_exists)+)
qed

abbreviation bottom_AD :: "'s angelic_design" ("\<^bold>\<bottom>\<^sub>A\<^sub>D") where
"\<^bold>\<bottom>\<^sub>A\<^sub>D \<equiv> A true"

abbreviation top_AD :: "'s angelic_design" ("\<^bold>\<top>\<^sub>A\<^sub>D") where
"\<^bold>\<top>\<^sub>A\<^sub>D \<equiv> A false"

lemma bottom_AD_lower:
  assumes "P is A"
  shows "\<^bold>\<bottom>\<^sub>A\<^sub>D \<sqsubseteq> P"
proof -
  have "A true \<sqsubseteq> A P"
    by (rule A_mono; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms])
qed

lemma top_AD_upper:
  assumes "P is A"
  shows "P \<sqsubseteq> \<^bold>\<top>\<^sub>A\<^sub>D"
proof -
  have "A P \<sqsubseteq> A false"
    by (rule A_mono; pred_auto)
  then show ?thesis
    by (simp only: Healthy_if[OF assms])
qed

(* Sequential composition preserves the full-alphabet choice closure. *)
lemma A_PBMH_ades:
  "PBMH_ades (A P) = A P"
  by (simp add: A_design_form PBMH_ades_rdesign PBMH_idem
      PBMH_conj_nonempty)

lemma A1_A: "A1 (A P) = A P"
  using A1_eq_PBMH_ades[of "A P"] A_is_H[of P]
  by (simp add: Healthy_def' A_PBMH_ades)

lemma A_is_PBMH_ades:
  assumes "P is A"
  shows "P is PBMH_ades"
  using A_PBMH_ades[of P] by (simp only: Healthy_if[OF assms] Healthy_def')

lemma A_healthy_components_iff:
  fixes P :: "'s angelic_design"
  shows "P is A \<longleftrightarrow>
    ((P is H1) \<and> (P is H2) \<and> (P is PBMH_ades) \<and> (P is A0))"
proof
  assume h: "P is A"
  have h1: "P is H1"
    using A_is_H1[of P] by (simp only: Healthy_if[OF h] Healthy_def')
  have h2: "P is H2"
    using A_is_H2[of P] by (simp only: Healthy_if[OF h] Healthy_def')
  have a0: "P is A0"
  proof -
    have "A P is A0" by (simp add: Healthy_def A_def A0_idem)
    then show ?thesis by (simp only: Healthy_if[OF h])
  qed
  show "(P is H1) \<and> (P is H2) \<and> (P is PBMH_ades) \<and> (P is A0)"
    using h1 h2 A_is_PBMH_ades[OF h] a0 by blast
next
  assume h: "(P is H1) \<and> (P is H2) \<and> (P is PBMH_ades) \<and> (P is A0)"
  have hh: "P is \<^bold>H"
    using h by (simp add: Healthy_def H1_H2_comp)
  show "P is A"
    using h by (simp add: Healthy_def A_def A1_eq_PBMH_ades[OF hh])
qed

lemma angelic_design_seq_PBMH_closure:
  assumes "P is PBMH_ades" "Q is PBMH_ades"
  shows "(P ;;\<^sub>A\<^sub>D Q) is PBMH_ades"
  unfolding angelic_design_seq_ok_cases
  apply (rule PBMH_ades_disj_closure)
   apply (rule aseq_ades_PBMH_ades_closure)
    using assms apply (simp add: Healthy_def' PBMH_ades_ok_true)
   using assms apply (simp add: Healthy_def' PBMH_ades_ok_in_subst)
  apply (rule aseq_ades_PBMH_ades_closure)
   using assms apply (simp add: Healthy_def' PBMH_ades_ok_false)
  using assms by (simp add: Healthy_def' PBMH_ades_ok_in_subst)

lemma angelic_design_seq_H_closure:
  assumes "P is A" "Q is \<^bold>H"
  shows "(P ;;\<^sub>A\<^sub>D Q) is \<^bold>H"
proof -
  let ?F = "PBMH (\<not> pre\<^sub>D P)"
  let ?T = "PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  have P_form: "P = ((\<not> ?F) \<turnstile>\<^sub>r ?T)"
    by (rule A_healthy_design_form[OF assms(1)])
  have Q_form: "Q = (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q)"
    using H1_H2_eq_rdesign[of Q] by (simp only: Healthy_if[OF assms(2)])
  have normal:
    "((\<not> ?F) \<turnstile>\<^sub>r ?T) ;;\<^sub>A\<^sub>D (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q) =
      angelic_design_seq_simplified ((\<not> ?F) \<turnstile>\<^sub>r ?T)
        (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q)"
    by (rule angelic_design_seq_eq_simplified;
        simp add: PBMH_idem PBMH_conj_nonempty)
  have "(((\<not> ?F) \<turnstile>\<^sub>r ?T) ;;\<^sub>A\<^sub>D
      (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q)) is \<^bold>H"
    by (simp only: normal angelic_design_seq_simplified_def Healthy_def';
        simp add: H1_rdesign H2_rdesign)
  then show ?thesis by (simp only: P_form[symmetric] Q_form[symmetric])
qed

lemma angelic_design_seq_A0_closure:
  assumes "Q is A"
  shows "(P ;;\<^sub>A\<^sub>D Q) is A0"
proof -
  have empty_normal:
    "(((\<not> F) \<turnstile>\<^sub>r (T \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)))
      (s0, ok\<^sub>v_update (\<lambda>_. True) out) =
     (((\<not> F) \<turnstile>\<^sub>r (T \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)))
      (s0, ok\<^sub>v_update (\<lambda>_. False) out)"
    if "achoices.ac\<^sub>v (des_vars.more out) = {}" for F T s0 out
    using that by pred_auto
  have empty_ok:
    "Q (s0, ok\<^sub>v_update (\<lambda>_. True) out) =
      Q (s0, ok\<^sub>v_update (\<lambda>_. False) out)"
    if "achoices.ac\<^sub>v (des_vars.more out) = {}" for s0 out
  proof -
    let ?D = "((\<not> PBMH (\<not> pre\<^sub>D Q)) \<turnstile>\<^sub>r
      (PBMH (post\<^sub>D Q) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
    have "?D (s0, ok\<^sub>v_update (\<lambda>_. True) out) =
      ?D (s0, ok\<^sub>v_update (\<lambda>_. False) out)"
      by (rule empty_normal[OF that])
    then show ?thesis
      by (simp only: A_healthy_design_form[OF assms, symmetric])
  qed
  have empty_concrete:
    "Q (s0, \<lparr>ok\<^sub>v = True, \<dots> = \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>\<rparr>) =
      Q (s0, \<lparr>ok\<^sub>v = False, \<dots> = \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>\<rparr>)"
    for s0
  proof -
    let ?out = "\<lparr>ok\<^sub>v = False, \<dots> = \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>\<rparr>"
    have "Q (s0, ok\<^sub>v_update (\<lambda>_. True) ?out) =
      Q (s0, ok\<^sub>v_update (\<lambda>_. False) ?out)"
      by (rule empty_ok; simp)
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding Healthy_def' A0_def
    apply (rule ext)
    apply (simp add: angelic_design_seq_def ac_non_empty_def)
    apply pred_auto
    by (simp only: empty_concrete; blast)
qed

(* Thesis Theorem T.4.5.3. The A normal form supplies control-independent components. *)
lemma angelic_design_seq_A_closure [closure]:
  assumes "P is A" "Q is A"
  shows "(P ;;\<^sub>A\<^sub>D Q) is A"
proof -
  have Q_H: "Q is \<^bold>H"
    using A_is_H[of Q] by (simp only: Healthy_if[OF assms(2)] Healthy_def')
  have H: "(P ;;\<^sub>A\<^sub>D Q) is \<^bold>H"
    by (rule angelic_design_seq_H_closure[OF assms(1) Q_H])
  have PBMH: "(P ;;\<^sub>A\<^sub>D Q) is PBMH_ades"
    by (rule angelic_design_seq_PBMH_closure;
        rule A_is_PBMH_ades; rule assms)
  have A0: "(P ;;\<^sub>A\<^sub>D Q) is A0"
    by (rule angelic_design_seq_A0_closure[OF assms(2)])
  show ?thesis
    using PBMH A0
    by (simp add: Healthy_def' A_def A1_eq_PBMH_ades[OF H])
qed

(* Thesis Theorems T.4.5.5 and T.4.5.6. *)
lemma Skip_AD_A [simp]: "A Skip_AD = Skip_AD"
  by (simp add: Skip_AD_def arel_to_ades_def A_design_form; pred_auto)

lemma Skip_AD_is_A [closure]: "Skip_AD is A"
  by (simp add: Healthy_def')

lemma Skip_AD_seq_left_unit:
  assumes "P is \<^bold>H"
  shows "(Skip_AD ;;\<^sub>A\<^sub>D P) = P"
proof -
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using H1_H2_eq_rdesign[of P] by (simp only: Healthy_if[OF assms])
  have unit: "(Skip_AD ;;\<^sub>A\<^sub>D (R \<turnstile>\<^sub>r S)) = (R \<turnstile>\<^sub>r S)"
    for R S :: "'s angelic_rel"
    by (simp add: Skip_AD_def arel_to_ades_def angelic_design_seq_def fun_eq_iff;
        pred_auto)
  show ?thesis
    using unit[of "pre\<^sub>D P" "post\<^sub>D P"] by (simp only: P_form[symmetric])
qed

(* Thesis Theorems T.4.5.7 and T.4.5.8. Right identity requires a normal precondition. *)
lemma Skip_AD_seq_right_normal:
  assumes "P is A"
  shows "(P ;;\<^sub>A\<^sub>D Skip_AD) =
    ((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) \<turnstile>\<^sub>r post\<^sub>D P)"
proof -
  let ?F = "PBMH (\<not> pre\<^sub>D P)"
  let ?T = "PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  have P_form: "P = ((\<not> ?F) \<turnstile>\<^sub>r ?T)"
    by (rule A_healthy_design_form[OF assms])
  have empty: "(?T ;;\<^sub>A false) = false"
    by (simp add: aseq_def fun_eq_iff; pred_auto)
  have seq: "(P ;;\<^sub>A\<^sub>D Skip_AD) =
      ((\<not> (?F ;;\<^sub>A true)) \<turnstile>\<^sub>r ?T)"
    apply (subst P_form)
    apply (simp only: Skip_AD_def arel_to_ades_def)
    apply (subst angelic_rdesign_seq)
      apply (simp add: PBMH_idem)
     apply (simp add: PBMH_conj_nonempty)
    by (simp add: empty)
  have absorb: "((\<not> (?F ;;\<^sub>A true)) \<turnstile>\<^sub>r (?F \<or> ?T)) =
      ((\<not> (?F ;;\<^sub>A true)) \<turnstile>\<^sub>r ?T)"
    by (simp add: aseq_def rdesign_refinement fun_eq_iff;
        pred_auto; blast)
  have pre: "pre\<^sub>D P = (\<not> ?F)"
    using arg_cong[where f="pre\<^sub>D", OF P_form] by (simp only: rdesign_pre)
  have post_form: "post\<^sub>D ((\<not> F) \<turnstile>\<^sub>r T) = (F \<or> T)"
    for F T :: "'s angelic_rel"
    by pred_auto
  have post: "post\<^sub>D P = (?F \<or> ?T)"
    using arg_cong[where f="post\<^sub>D", OF P_form]
    by (simp only: post_form)
  have mapped: "((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) \<turnstile>\<^sub>r post\<^sub>D P) =
      ((\<not> (?F ;;\<^sub>A true)) \<turnstile>\<^sub>r ?T)"
    using arg_cong2[OF pre post,
      where f="\<lambda>R S. ((\<not> ((\<not> R) ;;\<^sub>A true)) \<turnstile>\<^sub>r S)"]
    by (simp only: pred_ba.double_compl absorb)
  show ?thesis by (simp only: seq; rule mapped[symmetric])
qed

lemma Skip_AD_seq_right_unit_iff:
  assumes "P is A"
  shows "(P ;;\<^sub>A\<^sub>D Skip_AD) = P \<longleftrightarrow> (out\<alpha> \<sharp> pre\<^sub>D P)"
proof -
  have H: "P is \<^bold>H"
    using A_is_H[of P] by (simp only: Healthy_if[OF assms] Healthy_def')
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using H1_H2_eq_rdesign[of P] by (simp only: Healthy_if[OF H])
  have fixed_iff: "(P ;;\<^sub>A\<^sub>D Skip_AD) = P \<longleftrightarrow>
      (\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) = pre\<^sub>D P"
  proof
    assume fixed: "(P ;;\<^sub>A\<^sub>D Skip_AD) = P"
    show "(\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) = pre\<^sub>D P"
      using arg_cong[where f="pre\<^sub>D", OF fixed]
      by (simp only: Skip_AD_seq_right_normal[OF assms] rdesign_pre)
  next
    assume fixed: "(\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) = pre\<^sub>D P"
    show "(P ;;\<^sub>A\<^sub>D Skip_AD) = P"
      by (simp only: Skip_AD_seq_right_normal[OF assms] fixed P_form[symmetric])
  qed
  show ?thesis by (simp only: fixed_iff aseq_univ_pre_iff)
qed

lemma Skip_AD_seq_right_unit_iff_normal:
  assumes "P is A"
  shows "(P ;;\<^sub>A\<^sub>D Skip_AD) = P \<longleftrightarrow> P is \<^bold>N"
proof -
  have H: "P is \<^bold>H"
    using A_is_H[of P] by (simp only: Healthy_if[OF assms] Healthy_def')
  show ?thesis
    by (simp only: Skip_AD_seq_right_unit_iff[OF assms];
        blast intro: H1_H3_intro[OF H] H3_unrest_out_alpha)
qed

lemma Skip_AD_seq_right_unit:
  assumes "P is A" "P is \<^bold>N"
  shows "(P ;;\<^sub>A\<^sub>D Skip_AD) = P"
  using Skip_AD_seq_right_unit_iff_normal[OF assms(1)] assms(2) by blast

end
