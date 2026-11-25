section \<open>Reactive Angelic Design Choice\<close>

theory utp_rad_choice
  imports utp_rad_csp
begin

subsection \<open>Angelic Choice\<close>

lemma RA_A_angelic_choice:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is PBMH_ades" "Q is PBMH_ades"
      "P is \<^bold>H" "Q is \<^bold>H"
  shows
    "(RA \<circ> A) P \<squnion> (RA \<circ> A) Q =
     (RA \<circ> A) (P \<squnion> Q)"
proof -
  have choice_PBMH: "(P \<squnion> Q) is PBMH_ades"
    using PBMH_ades_conj_closure[OF assms(1,2)]
    by (simp only: angelic_design_angelic)
  have choice_design: "(P \<squnion> Q) is \<^bold>H"
    using Inf_H1_H2_closed[of "{P, Q}"] assms(3,4)
    by simp
  show ?thesis
    by (simp only: RA_A_absorb[OF assms(1) assms(3)]
        RA_A_absorb[OF assms(2) assms(4)]
        RA_A_absorb[OF choice_PBMH choice_design],
        simp only: conj_pred_def[symmetric] RA_conj)
qed

(* Paper Definition 37. *)
abbreviation achoice_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  (infixl "\<squnion>\<^sub>R\<^sub>A\<^sub>D" 70)
where "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q \<equiv> P \<squnion> Q"

lemma RAD_angelic_choice:
  "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

(* Paper Theorem 19. *)
(* P \<squnion> Q = RA \<circ> A ( \<not>P_f^f \<or> \<not>Q_f^f \<turnstile> (\<not>P_f^f \<Rightarrow> P_f^t) \<and> (\<not>Q_f^f \<Rightarrow> Q_f^t)) *)
theorem RAD_angelic_choice_design:
  assumes "P is RAD" "Q is RAD"
  shows "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q =
     (RA \<circ> A) (((\<not> (P \<^sub>f)\<^sup>f) \<or> (\<not> (Q \<^sub>f)\<^sup>f)) \<turnstile>
              (((\<not> (P \<^sub>f)\<^sup>f) \<longrightarrow> (P \<^sub>f)\<^sup>t) \<and>
              ((\<not> (Q \<^sub>f)\<^sup>f) \<longrightarrow> (Q \<^sub>f)\<^sup>t)))"
proof -
  let ?DP = "(\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t"
  let ?DQ = "(\<not> (Q \<^sub>f)\<^sup>f) \<turnstile> (Q \<^sub>f)\<^sup>t"
  have "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q =
      (RA \<circ> A) ?DP \<squnion> (RA \<circ> A) ?DQ"
    using arg_cong2[where f=inf,
        OF RAD_design_form'[OF assms(1)] RAD_design_form'[OF assms(2)]] .
  also have "... = (RA \<circ> A) (?DP \<squnion> ?DQ)"
    by (rule RA_A_angelic_choice[OF
          RAD_design_PBMH[OF assms(1)] RAD_design_PBMH[OF assms(2)]
          rad_wait_false_design_is_H rad_wait_false_design_is_H])
  also have "... = (RA \<circ> A)
        (((\<not> (P \<^sub>f)\<^sup>f) \<or> (\<not> (Q \<^sub>f)\<^sup>f)) \<turnstile>
         (((\<not> (P \<^sub>f)\<^sup>f) \<longrightarrow> (P \<^sub>f)\<^sup>t) \<and>
          ((\<not> (Q \<^sub>f)\<^sup>f) \<longrightarrow> (Q \<^sub>f)\<^sup>t)))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  finally show ?thesis .
qed

lemma RAD_angelic_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q is RAD"
proof -
  let ?D =
    "((\<not> (P \<^sub>f)\<^sup>f) \<or> (\<not> (Q \<^sub>f)\<^sup>f)) \<turnstile>
      (((\<not> (P \<^sub>f)\<^sup>f) \<longrightarrow> (P \<^sub>f)\<^sup>t) \<and>
       ((\<not> (Q \<^sub>f)\<^sup>f) \<longrightarrow> (Q \<^sub>f)\<^sup>t))"
  have "(RA \<circ> A) ?D is RAD"
    by rad_closure
  then show ?thesis
    by (simp only: RAD_angelic_choice_design[OF assms])
qed

(* Paper Theorem 20 / Thesis Theorem T.5.4.2. *)
theorem RAD_angelic_choice_CSP:
  "ac2p (p2ac P \<squnion>\<^sub>R\<^sub>A\<^sub>D p2ac Q) = P \<squnion> Q"
proof -
  have distribute:
      "ac2p (p2ac P \<and> p2ac Q) =
       (ac2p (p2ac P) \<and> ac2p (p2ac Q))"
    unfolding comp_apply
    apply (subst ac2p_conj)
      apply (rule rad_p2ac_PBMH_ades)+
    by (simp add:  fun_eq_iff conj_pred_def)
  show ?thesis
    apply (simp only: RAD_angelic_choice distribute rad_ac2p_p2ac_inverse')
    by (simp only: conj_pred_def)
qed

(* Paper Theorem 21 / Thesis Theorem T.5.4.3. *)
theorem RAD_angelic_choice_CSP_refine:
  assumes "P is RAD" "Q is RAD"
  shows "P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q \<sqsubseteq> p2ac (ac2p P \<squnion> ac2p Q)"
proof -
  have P_round: "P \<sqsubseteq> p2ac (ac2p P)"
    by (rule rad_p2ac_ac2p_refine'[OF RAD_is_PBMH_ades[OF assms(1)]])
  have Q_round: "Q \<sqsubseteq> p2ac (ac2p Q)"
    by (rule rad_p2ac_ac2p_refine'[OF RAD_is_PBMH_ades[OF assms(2)]])
  have "(P \<and> Q) \<sqsubseteq>
      (p2ac (ac2p P) \<and> p2ac (ac2p Q))"
    by (rule pred_ba.inf_mono[OF P_round Q_round])
  also have "... \<sqsubseteq>
      p2ac (ac2p P \<and> ac2p Q)"
    by (rule rad_p2ac_conj)
  finally show ?thesis
    apply (simp only: RAD_angelic_choice)
    by (simp only: conj_pred_def)
qed

subsection \<open>Demonic Choice\<close>

lemma RA_A_demonic_choice:
  "(RA \<circ> A) P \<sqinter> (RA \<circ> A) Q = (RA \<circ> A) (P \<sqinter> Q)"
  by (simp only: angelic_design_demonic comp_apply A_disj RA_disj)

(* Paper Definition 38. *)
abbreviation dchoice_RAD ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  (infixl "\<sqinter>\<^sub>R\<^sub>A\<^sub>D" 65)
where "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q \<equiv> P \<sqinter> Q"

lemma RAD_demonic_choice:
  "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

(* Paper Theorem 22 / Thesis Theorem T.5.4.4. *)
theorem RAD_demonic_choice_design:
  assumes "P is RAD" "Q is RAD"
  shows "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q =
    (RA \<circ> A) (((\<not> (P \<^sub>f)\<^sup>f) \<and> (\<not> (Q \<^sub>f)\<^sup>f)) \<turnstile>
      ((P \<^sub>f)\<^sup>t \<or> (Q \<^sub>f)\<^sup>t))"
proof -
  let ?DP = "(\<not> (P \<^sub>f)\<^sup>f) \<turnstile> (P \<^sub>f)\<^sup>t"
  let ?DQ = "(\<not> (Q \<^sub>f)\<^sup>f) \<turnstile> (Q \<^sub>f)\<^sup>t"
  have "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q =
      (RA \<circ> A) ?DP \<sqinter> (RA \<circ> A) ?DQ"
    using arg_cong2[where f=sup,
        OF RAD_design_form'[OF assms(1)] RAD_design_form'[OF assms(2)]] .
  also have "... = (RA \<circ> A) (?DP \<sqinter> ?DQ)"
    by (rule RA_A_demonic_choice)
  also have "... = (RA \<circ> A)
      (((\<not> (P \<^sub>f)\<^sup>f) \<and> (\<not> (Q \<^sub>f)\<^sup>f)) \<turnstile>
        ((P \<^sub>f)\<^sup>t \<or> (Q \<^sub>f)\<^sup>t))"
    apply (rule arg_cong[where f="RA \<circ> A"])
    by (simp only: angelic_design_demonic design_union)
  finally show ?thesis .
qed

lemma RAD_demonic_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q is RAD"
proof -
  let ?D =
    "((\<not> (P \<^sub>f)\<^sup>f) \<and> (\<not> (Q \<^sub>f)\<^sup>f)) \<turnstile>
      ((P \<^sub>f)\<^sup>t \<or> (Q \<^sub>f)\<^sup>t)"
  have "(RA \<circ> A) ?D is RAD"
    by rad_closure
  then show ?thesis
    by (simp only: RAD_demonic_choice_design[OF assms])
qed

(* Paper Theorem 23 / Thesis Theorem T.5.4.5. *)
theorem RAD_demonic_choice_CSP_distrib:
  "p2ac (ac2p P \<sqinter> ac2p Q) =
   p2ac (ac2p P) \<sqinter>\<^sub>R\<^sub>A\<^sub>D p2ac (ac2p Q)"
  by (rule rad_p2ac_disj[simplified disj_pred_def])

(* Paper Lemma 7 / Thesis Lemma L.5.4.1. *)
lemma RAD_demonic_choice_CSP_A2:
  assumes "P is RAD" "Q is RAD"
    and "P is A2" "Q is A2"
  shows "p2ac (ac2p P \<sqinter> ac2p Q) = P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q"
  by (simp only: RAD_demonic_choice_CSP_distrib
      rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

(* Paper Theorem 24 / Thesis Theorem T.5.4.6. *)
theorem RAD_demonic_choice_CSP:
  "ac2p (p2ac P \<sqinter>\<^sub>R\<^sub>A\<^sub>D p2ac Q) = P \<sqinter> Q"
  by (simp only: rad_ac2p_disj[simplified disj_pred_def]
      rad_ac2p_p2ac_inverse')

(* Paper Section 6.4.2: angelic and demonic choice distribute over each other. *)
(* P \<squnion> (Q \<Sqinter> R) = (P \<squnion> Q) \<sqinter> (P \<squnion> R) *)
lemma RAD_angelic_demonic_distrib:
  "P \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) =
   (P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (P \<squnion>\<^sub>R\<^sub>A\<^sub>D R)"
  by (rule inf_sup_distrib1)

(* P \<sqinter> (Q \<squnion> R) = (P \<sqinter> Q) \<squnion> (P \<sqinter> R) *)
lemma RAD_demonic_angelic_distrib:
  "P \<sqinter>\<^sub>R\<^sub>A\<^sub>D (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R) =
   (P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P \<sqinter>\<^sub>R\<^sub>A\<^sub>D R)"
  by (rule sup_inf_distrib1)

subsection \<open>Chaos\<close>

(* Paper Definition 39. *)
definition Chaos_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Chaos\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Chaos_RAD = (RA \<circ> A) (false \<turnstile> ac_non_empty)"

lemma Chaos_RAD':
  "Chaos\<^sub>R\<^sub>A\<^sub>D = (RA \<circ> A) (false \<turnstile> true)"
  by (simp only: Chaos_RAD_def design_false_pre)

(* Chaos_RAD is the RAD image of true. *)
lemma Chaos_RAD_RAD: "Chaos\<^sub>R\<^sub>A\<^sub>D = RAD true"
  by (simp only: Chaos_RAD' RAD_design_form comp_apply
      rad_wait_false_true subst_pred(1) pred_ba.compl_top_eq)

lemma bottom_RAD_is_Chaos:
  "(\<^bold>\<bottom>\<^sub>R\<^sub>A\<^sub>D ::
      ('t::trace, 'e) reactive_angelic_design) = Chaos\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: Chaos_RAD_RAD)

lemma Chaos_RAD_RA: "Chaos\<^sub>R\<^sub>A\<^sub>D = RA true"
  apply (simp only: Chaos_RAD' design_false_pre comp_apply)
  apply (subst RA_A')
   apply (simp add: Healthy_def' H1_H2_comp comp_apply H1_def H2_true)
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma Chaos_RAD_is_RAD [closure]: "Chaos\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Chaos_RAD_def
  by rad_closure

(* Paper Theorem 25. *)
theorem Chaos_RAD_angelic_choice_unit:
  assumes "P is RAD"
  shows "Chaos\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P = P"
proof -
  have P_RA: "RA P = P"
    by (rule Healthy_if[OF RAD_is_RA[OF assms]])
  show ?thesis
    apply (simp only: RAD_angelic_choice Chaos_RAD_RA)
    apply (subst P_RA[symmetric])
    apply (simp add: RA_conj[symmetric])
    by (rule P_RA)
qed

(* The dual law of Paper Theorem 25. *)
lemma Chaos_RAD_demonic_choice_zero:
  assumes "P is RAD"
  shows "Chaos\<^sub>R\<^sub>A\<^sub>D \<sqinter>\<^sub>R\<^sub>A\<^sub>D P = Chaos\<^sub>R\<^sub>A\<^sub>D"
proof -
  have P_RA: "RA P = P"
    by (rule Healthy_if[OF RAD_is_RA[OF assms]])
  show ?thesis
    apply (simp only: RAD_demonic_choice Chaos_RAD_RA)
    apply (subst P_RA[symmetric])
    by (simp add: RA_disj[symmetric])
qed

(* RAD Chaos is the image of RD Chaos: Chaos_RAD = p2ac \<bottom>RD *)
lemma Chaos_RAD_p2ac:
  "(Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) = p2ac \<^bold>\<bottom>\<^sub>R\<^sub>D"
proof (rule ref_antisym)
  show "Chaos\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> p2ac (\<^bold>\<bottom>\<^sub>R\<^sub>D :: ('t, 'e set) rp_hrel)"
    unfolding Chaos_RAD_RAD by (rule bottom_RAD_lower[OF rad_p2ac_RD_closure[OF bottom_RD_is_RD]])
  have ne: "(ac_non_empty \<and> RAD true) = (RAD true :: ('t, 'e) reactive_angelic_design)"
    by (simp only: RAD_def comp_apply RA_ac_non_empty_absorb)
  have "RAD ac_non_empty \<sqsubseteq> RAD (ac_non_empty \<and> RAD true :: ('t, 'e) reactive_angelic_design)"
    by (rule RAD_mono) pred_auto
  then show "p2ac (\<^bold>\<bottom>\<^sub>R\<^sub>D :: ('t, 'e set) rp_hrel) \<sqsubseteq> Chaos\<^sub>R\<^sub>A\<^sub>D"
    by (simp only: rad_p2ac_RD p2ac_true ne RAD_idem Chaos_RAD_RAD)
qed

(* Chaos keeps a waiting prior and otherwise offers any choice set that extends
   the trace:
     Chaos_RAD = \<exists>s'\<in>ac'. (\<not>(ok \<and> wait) \<and> tr \<le> tr') \<or> (ok \<and> wait \<and> ok' \<and> s' = s) *)
lemma Chaos_RAD_eval:
  "(Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) (ades_obs ok0 s0 ok' Z) \<longleftrightarrow>
    (\<exists>s'\<in>Z. (\<not> (ok0 \<and> rad_wait\<^sub>v s0) \<and> rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s') \<or>
      (ok0 \<and> rad_wait\<^sub>v s0 \<and> ok' \<and> s' = s0))"
  by (cases ok0; cases ok'; simp add: Chaos_RAD_p2ac rad_p2ac_obs bottom_RD_eval)

(* Miracle has no started observation:
     \<top>RAD = \<exists>s'\<in>ac'. (\<not>ok \<and> tr \<le> tr') \<or> (ok \<and> wait \<and> ok' \<and> s' = s) *)
lemma top_RAD_eval:
  "(\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) (ades_obs ok0 s0 ok' Z) \<longleftrightarrow>
    (\<exists>s'\<in>Z. (\<not> ok0 \<and> rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s') \<or> (ok0 \<and> rad_wait\<^sub>v s0 \<and> ok' \<and> s' = s0))"
proof -
  have "(\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D :: ('t, 'e) reactive_angelic_design) = p2ac \<^bold>\<top>\<^sub>R\<^sub>D"
    by (simp only: rad_p2ac_RD p2ac_false)
  then show ?thesis
    by (cases ok0; cases ok'; simp add: rad_p2ac_obs top_RD_eval)
qed

(* As for RD, RAD fixes the unstarted and waiting priors, so we compare RAD
   processes at the active priors only *)
lemma RAD_eq_active:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is RAD" "Q is RAD"
      and "\<And>s0 ok' Z. \<not> rad_wait\<^sub>v s0 \<Longrightarrow>
        P (ades_obs True s0 ok' Z) \<longleftrightarrow> Q (ades_obs True s0 ok' Z)"
  shows "P = Q"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' Z
  have bounds: "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D (ades_obs ok0 s0 ok' Z) \<Longrightarrow> X (ades_obs ok0 s0 ok' Z)"
      "X (ades_obs ok0 s0 ok' Z) \<Longrightarrow> Chaos\<^sub>R\<^sub>A\<^sub>D (ades_obs ok0 s0 ok' Z)"
    if "X is RAD" for X :: "('t, 'e) reactive_angelic_design"
    using top_RAD_upper[OF that] bottom_RAD_lower[OF that]
    unfolding Chaos_RAD_RAD pred_refine_iff by blast+
  show "P (ades_obs ok0 s0 ok' Z) = Q (ades_obs ok0 s0 ok' Z)"
  proof (cases "ok0 \<and> \<not> rad_wait\<^sub>v s0")
    case True
    then show ?thesis
      using assms(3)[of s0 ok' Z] by simp
  next
    (* elsewhere P and Q lie between Chaos and Miracle, which agree there *)
    case False
    then have "Chaos\<^sub>R\<^sub>A\<^sub>D (ades_obs ok0 s0 ok' Z) \<longleftrightarrow> \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D (ades_obs ok0 s0 ok' Z)"
      by (cases ok0) (simp_all add: Chaos_RAD_eval top_RAD_eval)
    then show ?thesis
      using bounds[OF assms(1)] bounds[OF assms(2)] by blast
  qed
qed

subsection \<open>Choice\<close>

(* Paper Definition 40. *)
definition Choice_RAD :: "('t::trace, 'e) reactive_angelic_design" ("Choice\<^sub>R\<^sub>A\<^sub>D") where
[pred]: "Choice_RAD = (RA \<circ> A) (true \<turnstile> ac_non_empty)"

lemma Choice_RAD_alt:
  "Choice\<^sub>R\<^sub>A\<^sub>D = (RA \<circ> A) (true \<turnstile> true)"
  apply (simp only: Choice_RAD_def comp_apply)
  apply (rule arg_cong[where f=RA])
  by (simp add: A_design_form ac_non_empty_def PBMH_def pbmh_step_def
      fun_eq_iff; pred_auto)

lemma Choice_RAD_is_RAD [closure]: "Choice\<^sub>R\<^sub>A\<^sub>D is RAD"
  unfolding Choice_RAD_def
  by rad_closure

lemma Choice_RAD_RA: "Choice\<^sub>R\<^sub>A\<^sub>D = RA (true \<turnstile> true)"
  apply (simp only: Choice_RAD_alt)
  by (rule RA_A_absorb_design_true[OF true_PBMH_ades];
      simp add: unrest)

(* The wait-conditional design form of Choice_RAD under RA1. *)
lemma Choice_RAD_design:
  "Choice\<^sub>R\<^sub>A\<^sub>D =
   RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         true))"
  by (simp only: Choice_RAD_RA RA_true_design RA2_true)

(* Choice_RAD can only fail to stabilise when it has not started. *)
lemma Choice_RAD_wf_ok_false: "(Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f = RA2 (RA1 (\<not> ok\<^sup><))"
proof -
  have design_norm:
      "((\<not> (ok\<^sup>> \<^sub>f)\<^sup>f) \<turnstile> (ok\<^sup>> \<^sub>f)\<^sup>t) = (true \<turnstile> true)"
    by (simp add: rad_wait_false_def usubst usubst_eval; pred_auto)
  have disj_norm: "((\<not> ok\<^sup><) \<or> (ok\<^sup>> \<^sub>f)\<^sup>f) = (\<not> ok\<^sup><)"
    by (simp add: rad_wait_false_def usubst usubst_eval; pred_auto)
  have "((rad_wait_false \<circ> RA \<circ> A) (true \<turnstile> true))\<^sup>f =
      (RA2 \<circ> RA1 \<circ> PBMH_ades) ((\<not> ok\<^sup><) \<or> (ok\<^sup>> \<^sub>f)\<^sup>f)"
    using RA_design_wf_ok_false[of "ok\<^sup>>"]
    by (simp only: design_norm)
  then show ?thesis
    by (simp only: Choice_RAD_alt disj_norm comp_apply PBMH_ades_not_ok_expr)
qed

lemma Choice_RAD_wf_ok_false_subst:
  "(Choice\<^sub>R\<^sub>A\<^sub>D \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk> = false"
proof -
  have not_true: "(\<not> (True)\<^sub>e :: ('t::trace, 'e) reactive_angelic_design) = false"
    by pred_auto
  show ?thesis
    apply (simp only: Choice_RAD_wf_ok_false RA2_ok_in_subst RA1_ok_in_subst)
    apply (simp add: usubst usubst_eval)
    by (simp only: not_true RA1_false RA2_false)
qed

(* Paper Theorem 26. *)
theorem Choice_RAD_angelic_choice:
  assumes "P is RAD"
  shows "Choice\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P = (RA \<circ> A) (true \<turnstile> (P \<^sub>f)\<^sup>t)"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  let ?Z = "(\<not> ok\<^sup><) \<or> ?F \<or> ?T"
  have T_form: "?T = RA2 (RA1 (PBMH_ades ?Z))"
    using arg_cong[where f="\<lambda>R. (R \<^sub>f)\<^sup>t",
        OF RAD_design_form'[OF assms]]
    by (simp only: comp_apply RA_design_wf_ok_true')
  have "Choice\<^sub>R\<^sub>A\<^sub>D \<squnion>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> true) \<squnion> (RA \<circ> A) ?DP"
    using arg_cong2[where f=inf,
        OF Choice_RAD_alt RAD_design_form'[OF assms]] .
  also have "... = (RA \<circ> A) ((true \<turnstile> true) \<squnion> ?DP)"
    apply (rule RA_A_angelic_choice)
       apply (simp add: Healthy_def' PBMH_ades_def fun_eq_iff; pred_auto)
      apply (rule RAD_design_PBMH[OF assms])
     apply (rule design_is_H1_H2; simp add: unrest)
    by (rule rad_wait_false_design_is_H)
  also have "... = (RA \<circ> A) (true \<turnstile> ?Z)"
    apply (rule arg_cong[where f="RA \<circ> A"])
    apply (simp only: design_inf)
    by pred_auto
  also have "... = (RA \<circ> A) (true \<turnstile> ?T)"
    apply (rule RA_A_true_design_post)
       apply (rule design_is_H1_H2; simp add: unrest)
      apply (rule design_is_H1_H2; simp add: unrest)
     apply (rule T_form[symmetric])
    by (rule Healthy_if[OF RAD_wf_ok_true_PBMH[OF assms]])
  finally show ?thesis .
qed

(* Paper Theorem 27. *)
theorem Choice_RAD_demonic_choice:
  assumes "P is RAD"
  shows "Choice\<^sub>R\<^sub>A\<^sub>D \<sqinter>\<^sub>R\<^sub>A\<^sub>D P =
    (RA \<circ> A) ((\<not> (P \<^sub>f)\<^sup>f) \<turnstile> ac_non_empty)"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  let ?DP = "(\<not> ?F) \<turnstile> ?T"
  have "Choice\<^sub>R\<^sub>A\<^sub>D \<sqinter>\<^sub>R\<^sub>A\<^sub>D P =
      (RA \<circ> A) (true \<turnstile> true) \<sqinter> (RA \<circ> A) ?DP"
    using arg_cong2[where f=sup,
        OF Choice_RAD_alt RAD_design_form'[OF assms]] .
  also have "... = (RA \<circ> A) ((true \<turnstile> true) \<sqinter> ?DP)"
    by (rule RA_A_demonic_choice)
  also have "... = (RA \<circ> A) ((\<not> ?F) \<turnstile> ac_non_empty)"
    apply (simp only: comp_apply)
    apply (rule arg_cong[where f=RA])
    by (simp add: angelic_design_demonic design_union A_design_form
        ac_non_empty_def PBMH_def pbmh_step_def fun_eq_iff; pred_auto)
  finally show ?thesis .
qed

end
