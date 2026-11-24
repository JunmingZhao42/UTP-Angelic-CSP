section \<open>PBMH Healthiness\<close>

theory utp_ades_pbmh
  imports utp_ades_ops
begin

subsection \<open>PBMH\<close>

lemma pbmh_step_idem: "pbmh_step ;; pbmh_step = pbmh_step"
  by (pred_auto)

lemma PBMH_idem: "PBMH (PBMH P) = PBMH P"
  by (simp add: PBMH_def seqr_assoc pbmh_step_idem)

lemma PBMH_Idempotent [closure]: "Idempotent PBMH"
  by (simp add: Idempotent_def PBMH_idem)

lemma PBMH_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> PBMH P \<sqsubseteq> PBMH Q"
  by (simp add: PBMH_def, rule seqr_mono, simp_all)

lemma PBMH_Monotonic [closure]: "Monotonic PBMH"
  by (rule MonotonicI, rule PBMH_mono)

lemma PBMH_neg_guard:
  "Q \<sqsubseteq> P \<Longrightarrow> (\<not> PBMH (\<not> Q)) \<sqsubseteq> (\<not> PBMH (\<not> P))"
  by (pred_auto)

lemma PBMH_guarded_post:
  "PBMH (P \<and> Q) \<sqsubseteq> ((\<not> PBMH (\<not> P)) \<and> PBMH Q)"
  by (pred_auto)

(* Paper Lemma 3. PBMH (ac' = \<emptyset>) = true *)
lemma PBMH_ac_empty [simp]:
  "PBMH (($ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e) = true"
  by (pred_auto)

(* Paper Lemma 15. PBMH (ac' \<noteq> \<emptyset>) = (ac' \<noteq> \<emptyset>) *)
lemma PBMH_ac_non_empty [simp]:
  "PBMH (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e) =
   (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
  by (pred_auto)

lemma PBMH_unrest_ac: "$ac\<^sup>> \<sharp> P \<Longrightarrow> PBMH P = P"
  by (simp add: PBMH_def pbmh_step_def, pred_auto)

lemma PBMH_conj_nonempty:
  "PBMH (PBMH P \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e) =
   (PBMH P \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
  by (simp add: PBMH_def pbmh_step_def, pred_auto)

lemma PBMH_disj: "PBMH (P \<or> Q) = (PBMH P \<or> PBMH Q)"
  by (simp add: PBMH_def seqr_or_distl)

lemma PBMH_healthy [closure]: "PBMH P is PBMH"
  by (simp add: Healthy_def' PBMH_idem)

lemma PBMH_conj_closure [closure]:
  assumes "P is PBMH" "Q is PBMH"
  shows "(P \<and> Q) is PBMH"
  using assms
  by (simp add: Healthy_def' PBMH_def pbmh_step_def fun_eq_iff;
      pred_auto; blast)

lemma PBMH_disj_closure [closure]:
  assumes "P is PBMH" "Q is PBMH"
  shows "(P \<or> Q) is PBMH"
  using assms by (simp add: Healthy_def' PBMH_disj)

lemma neg_PBMH_eval:
  fixes P :: "'s angelic_rel" and s :: "'s astate" and X :: "'s set"
  shows "(\<not> PBMH (\<not> P)) (s, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>) =
    (\<forall>Y \<subseteq> X. P (s, \<lparr>ac\<^sub>v = Y, \<dots> = ()\<rparr>))"
  by (simp add: PBMH_def pbmh_step_def; pred_auto; blast)

subsection \<open>PBMH and Angelic Sequential Composition\<close>

lemma pbmh_step_eval:
  "pbmh_step (b, c) \<longleftrightarrow>
    (achoices.ac\<^sub>v b \<subseteq> achoices.ac\<^sub>v c \<and>
     achoices.more b = achoices.more c)"
  by (simp add: pbmh_step_def; pred_auto)

lemma PBMH_eval:
  "PBMH P (s0, ac') \<longleftrightarrow>
    (\<exists>b. P (s0, b) \<and> pbmh_step (b, ac'))"
  by (simp add: PBMH_def; pred_auto)

(* PBMH-healthy predicates are upward closed in the angelic-choice set. *)
lemma PBMH_weaken: "P x \<Longrightarrow> PBMH P x"
  by (cases x; simp add: PBMH_def pbmh_step_def; pred_auto)

lemma PBMH_upward:
  assumes "P is PBMH" "P (s0, b)" "pbmh_step (b, c)"
  shows "P (s0, c)"
proof -
  have "PBMH P (s0, c)"
    using assms(2,3) by (auto simp add: PBMH_eval)
  then show ?thesis
    using assms(1) by (simp add: Healthy_def')
qed

lemma PBMH_ac_upward:
  assumes "P is PBMH"
    and "P (s0, achoices.ac\<^sub>v_update (\<lambda>_. A) ac')" and "A \<subseteq> B"
  shows "P (s0, achoices.ac\<^sub>v_update (\<lambda>_. B) ac')"
  apply (rule PBMH_upward[OF assms(1) assms(2)])
  by (simp add: pbmh_step_eval assms(3))

(* The angelic sequence is monotonic in its right argument on PBMH-healthy
   left arguments; monotonicity on the left is aseq_mono_left. *)
lemma aseq_mono_right:
  assumes "P is PBMH" and "Q \<sqsubseteq> R"
  shows "(P ;;\<^sub>A Q) \<sqsubseteq> (P ;;\<^sub>A R)"
  unfolding aseq_def pred_refine_iff
  apply (clarsimp split: prod.splits)
  apply (rule PBMH_ac_upward[OF assms(1)])
   apply assumption
  using assms(2)
  by (auto simp add: pred_refine_iff)

(* Thesis Section 4.4: PBMH is closed under angelic sequential
   composition. *)
lemma PBMH_aseq_closure [closure]:
  fixes P Q :: "('s, '\<alpha>, '\<beta>) angelic_rel_ext"
  assumes "P is PBMH" "Q is PBMH"
  shows "(P ;;\<^sub>A Q) is PBMH"
proof (rule Healthy_intro, rule ext)
  fix w :: "('s, '\<alpha>) astate_ext \<times> ('s, '\<beta>) achoices_ext"
  obtain s0 ac' where w_eq [simp]: "w = (s0, ac')"
    by (cases w) auto
  show "PBMH (P ;;\<^sub>A Q) w = (P ;;\<^sub>A Q) w"
  proof
    assume "PBMH (P ;;\<^sub>A Q) w"
    then obtain b where comp: "(P ;;\<^sub>A Q) (s0, b)"
        and step: "pbmh_step (b, ac')"
      by (auto simp add: PBMH_eval)
    define Sb where "Sb = {s1. Q (astate.s\<^sub>v_update (\<lambda>_. s1) s0, b)}"
    define S where "S = {s1. Q (astate.s\<^sub>v_update (\<lambda>_. s1) s0, ac')}"
    have P_at: "P (s0, achoices.ac\<^sub>v_update (\<lambda>_. Sb) b)"
      using comp by (simp add: aseq_def Sb_def)
    have S_sub: "Sb \<subseteq> S"
      unfolding Sb_def S_def
      by (auto intro: PBMH_upward[OF assms(2) _ step])
    have step': "pbmh_step
        (achoices.ac\<^sub>v_update (\<lambda>_. Sb) b,
         achoices.ac\<^sub>v_update (\<lambda>_. S) ac')"
      using S_sub step by (simp add: pbmh_step_eval)
    have "P (s0, achoices.ac\<^sub>v_update (\<lambda>_. S) ac')"
      by (rule PBMH_upward[OF assms(1) P_at step'])
    then show "(P ;;\<^sub>A Q) w"
      by (simp add: aseq_def S_def)
  next
    assume "(P ;;\<^sub>A Q) w"
    then show "PBMH (P ;;\<^sub>A Q) w"
      by (rule PBMH_weaken)
  qed
qed

lemma PBMH_state_subst:
  "arel_state_subst st_subst (PBMH P) = PBMH (arel_state_subst st_subst P)"
  apply (simp add: PBMH_def)
  apply (rule subst_seq_left)
  apply (simp add: out\<alpha>_def)
  apply (rule unrest_subst_aext)
  apply simp
  done

(* Paper Theorem 64. PBMH commutes with the H1 guard. *)
theorem PBMH_H1_commute:
  "PBMH (ok\<^sup>< \<longrightarrow> P) = (ok\<^sup>< \<longrightarrow> PBMH P)"
  by (pred_auto)

lemma H2_lift_desr:
  "H2 (\<lceil>P\<rceil>\<^sub>D) = \<lceil>P\<rceil>\<^sub>D"
  by (pred_auto)

(* Lifted-relation instance of paper Theorem 65. The full-alphabet
   commutation law is stated for PBMH_ades below. *)
theorem PBMH_H2_commute:
  "H2 (\<lceil>PBMH P\<rceil>\<^sub>D) =
   \<lceil>PBMH (\<lfloor>H2 (\<lceil>P\<rceil>\<^sub>D)\<rfloor>\<^sub>D)\<rceil>\<^sub>D"
  by (simp add: H2_lift_desr)

subsection \<open>PBMH_ades\<close>

(* PBMH_ades P = P ;; (ok' = ok \<and> \<lceil>pbmh_step\<rceil>\<^sub>D) *)
definition PBMH_ades ::
  "('\<beta>, 's achoices des_vars_ext) urel \<Rightarrow> ('\<beta>, 's achoices des_vars_ext) urel" where
[pred]: "PBMH_ades P \<equiv> P ;; (($ok\<^sup>> = $ok\<^sup><)\<^sub>e \<and> \<lceil>pbmh_step\<rceil>\<^sub>D)"

lemma PBMH_ades_lift:
  "PBMH_ades (\<lceil>P\<rceil>\<^sub>D) = \<lceil>PBMH P\<rceil>\<^sub>D"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma PBMH_ades_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> PBMH_ades P \<sqsubseteq> PBMH_ades Q"
  by (simp add: PBMH_ades_def; pred_auto; blast)

lemma PBMH_ades_Monotonic [closure]: "Monotonic PBMH_ades"
  by (rule MonotonicI, rule PBMH_ades_mono)

lemma PBMH_ades_weaken: "P w \<Longrightarrow> PBMH_ades P w"
  by (cases w; simp add: PBMH_ades_def PBMH_def pbmh_step_def;
      pred_auto)

lemma PBMH_ades_eval:
  "PBMH_ades P (s0, ac') \<longleftrightarrow>
    (\<exists>X. P (s0, des_vars.more_update
        (achoices.ac\<^sub>v_update (\<lambda>_. X)) ac') \<and>
      X \<subseteq> achoices.ac\<^sub>v (des_vars.more ac'))"
  apply (simp add: PBMH_ades_def PBMH_def pbmh_step_def Let_def)
  apply pred_auto
  subgoal for X
    by (rule exI[where x=X]; cases ac'; cases "des_vars.more ac'"; simp)
  subgoal for X
    by (rule exI[where x=X]; cases ac'; cases "des_vars.more ac'"; simp)
  done

lemma PBMH_ades_obs:
  "PBMH_ades P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<exists>Y \<subseteq> X. P (ades_obs b s0 c Y))"
  by (simp add: PBMH_ades_eval; blast)

(* PBMH_ades-healthy predicates are upward closed in the angelic-choice
   component when the design observation otherwise agrees. *)
lemma PBMH_ades_upward:
  assumes "P is PBMH_ades" and "P (s0, y)"
    and "achoices.ac\<^sub>v (des_vars.more y) \<subseteq>
      achoices.ac\<^sub>v (des_vars.more y')"
    and "ok\<^sub>v y' = ok\<^sub>v y"
  shows "P (s0, y')"
proof -
  have "PBMH_ades P (s0, y')"
    using assms(2,3,4)
    apply (simp add: PBMH_ades_eval)
    apply (rule exI[where x="achoices.ac\<^sub>v (des_vars.more y)"])
    by (cases y; cases y'; cases "des_vars.more y";
        cases "des_vars.more y'"; simp)
  then show ?thesis
    using assms(1) by (simp add: Healthy_def')
qed

lemma aseq_ades_mono_right:
  assumes "P is PBMH_ades" and "Q \<sqsubseteq> R"
  shows "(P ;;\<^sub>A\<^sub>R Q) \<sqsubseteq> (P ;;\<^sub>A\<^sub>R R)"
  unfolding aseq_ades_def pred_refine_iff
  apply (clarsimp split: prod.splits)
  apply (erule PBMH_ades_upward[OF assms(1)])
  using assms(2)
  by (auto simp add: pred_refine_iff)

(* Monotonicity of design-level angelic composition.  As for
   \<open>aseq_ades_mono_right\<close>, the left operand must be upward closed. *)
lemma angelic_design_seq_mono:
  assumes "P is PBMH_ades" "P \<sqsubseteq> P'" "Q \<sqsubseteq> Q'"
  shows "(P ;;\<^sub>A\<^sub>D Q) \<sqsubseteq> (P' ;;\<^sub>A\<^sub>D Q')"
proof -
  have PP: "\<And>s. P' s \<Longrightarrow> P s"
  proof -
    fix s assume "P' s"
    obtain a b where [simp]: "s = (a, b)" by (cases s) auto
    then show "P s"
      using assms(2) `P' s` by (simp add: pred_refine_iff)
  qed
  have QQ: "\<And>s. Q' s \<Longrightarrow> Q s"
  proof -
    fix s assume "Q' s"
    obtain a b where [simp]: "s = (a, b)" by (cases s) auto
    then show "Q s"
      using assms(3) `Q' s` by (simp add: pred_refine_iff)
  qed
  show ?thesis
    unfolding angelic_design_seq_def pred_refine_iff
    apply (clarsimp split: prod.splits)
    subgoal premises prems for a b ok0
      apply (rule exI[where x=ok0])
      apply (rule PBMH_ades_upward[OF assms(1) PP[OF prems(1)]])
        using QQ apply auto
      done
    done
qed

lemma aseq_ades_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades" "Q is PBMH_ades"
  shows "(P ;;\<^sub>A\<^sub>R Q) is PBMH_ades"
proof (rule Healthy_intro, rule ext)
  fix w :: "'a astate des_vars_ext \<times> 'a achoices des_vars_ext"
  obtain s0 ac' where w_eq [simp]: "w = (s0, ac')"
    by (cases w) auto
  show "PBMH_ades (P ;;\<^sub>A\<^sub>R Q) w = (P ;;\<^sub>A\<^sub>R Q) w"
  proof
    assume "PBMH_ades (P ;;\<^sub>A\<^sub>R Q) w"
    then obtain X where
        comp: "(P ;;\<^sub>A\<^sub>R Q) (s0, des_vars.more_update
          (achoices.ac\<^sub>v_update (\<lambda>_. X)) ac')"
        and sub: "X \<subseteq> achoices.ac\<^sub>v (des_vars.more ac')"
      by (auto simp add: PBMH_ades_eval)
    let ?mid = "des_vars.more_update
      (achoices.ac\<^sub>v_update (\<lambda>_. X)) ac'"
    let ?SX = "{s1. Q (des_vars.more_update
      (astate.s\<^sub>v_update (\<lambda>_. s1)) s0, ?mid)}"
    let ?S = "{s1. Q (des_vars.more_update
      (astate.s\<^sub>v_update (\<lambda>_. s1)) s0, ac')}"
    have P_at: "P (s0, des_vars.more_update
        (achoices.ac\<^sub>v_update (\<lambda>_. ?SX)) ?mid)"
      using comp by (simp add: aseq_ades_def)
    have S_sub: "?SX \<subseteq> ?S"
      apply (rule subsetI)
      apply (simp only: mem_Collect_eq)
      apply (erule PBMH_ades_upward[OF assms(2)])
      using sub by auto
    show "(P ;;\<^sub>A\<^sub>R Q) w"
      unfolding w_eq aseq_ades_def
      apply (simp only: prod.case)
      apply (rule PBMH_ades_upward[OF assms(1) P_at])
      using S_sub by auto
  next
    assume "(P ;;\<^sub>A\<^sub>R Q) w"
    then show "PBMH_ades (P ;;\<^sub>A\<^sub>R Q) w"
      by (rule PBMH_ades_weaken)
  qed
qed

(* The final ok observation is constant across the angelic-choice
   comprehension, so it can be pulled out of the right operand. *)
lemma aseq_ades_ok_out_split:
  assumes "P is PBMH_ades"
  shows "(P ;;\<^sub>A\<^sub>R (X \<or> (Y \<and> ok\<^sup>>))) =
    ((P ;;\<^sub>A\<^sub>R X) \<or> ((P ;;\<^sub>A\<^sub>R (X \<or> Y)) \<and> ok\<^sup>>))"
proof (rule ext)
  fix w :: "'a astate des_vars_ext \<times> 'a achoices des_vars_ext"
  obtain s0 ac' where w_eq [simp]: "w = (s0, ac')" by (cases w) auto
  have evalp: "((X \<or> (Y \<and> ok\<^sup>>)) (a, ac')) \<longleftrightarrow>
      (X (a, ac') \<or> (Y (a, ac') \<and> ok\<^sub>v ac'))" for a
    by pred_auto
  have evalo: "((Z \<and> ok\<^sup>>) (s0, ac')) \<longleftrightarrow> (Z (s0, ac') \<and> ok\<^sub>v ac')"
    for Z :: "'a angelic_design"
    by pred_auto
  show "(P ;;\<^sub>A\<^sub>R (X \<or> (Y \<and> ok\<^sup>>))) w =
      ((P ;;\<^sub>A\<^sub>R X) \<or> ((P ;;\<^sub>A\<^sub>R (X \<or> Y)) \<and> ok\<^sup>>)) w"
  proof (cases "ok\<^sub>v ac'")
    case True
    then have "(P ;;\<^sub>A\<^sub>R (X \<or> (Y \<and> ok\<^sup>>))) (s0, ac') =
        (P ;;\<^sub>A\<^sub>R (X \<or> Y)) (s0, ac')"
      by (simp add: aseq_ades_def evalp disj_pred_def; pred_auto)
    moreover have "(P ;;\<^sub>A\<^sub>R X) (s0, ac') \<Longrightarrow>
        (P ;;\<^sub>A\<^sub>R (X \<or> Y)) (s0, ac')"
      unfolding aseq_ades_def
      apply (simp only: prod.case)
      apply (erule PBMH_ades_upward[OF assms])
      by (auto simp add: disj_pred_def)
    ultimately show ?thesis
      using True
      by (auto simp add: disj_pred_def conj_pred_def evalo
          des_vars.ok_def)
  next
    case False
    then have "(P ;;\<^sub>A\<^sub>R (X \<or> (Y \<and> ok\<^sup>>))) (s0, ac') =
        (P ;;\<^sub>A\<^sub>R X) (s0, ac')"
      by (simp add: aseq_ades_def evalp disj_pred_def; pred_auto)
    then show ?thesis
      using False
      by (auto simp add: disj_pred_def conj_pred_def evalo
          des_vars.ok_def)
  qed
qed

lemma PBMH_ades_idem: "PBMH_ades (PBMH_ades P) = PBMH_ades P"
  by (simp add: PBMH_ades_def pbmh_step_def fun_eq_iff; pred_auto; blast)

lemma PBMH_ades_Idempotent [closure]: "Idempotent PBMH_ades"
  by (simp add: Idempotent_def PBMH_ades_idem)

lemma PBMH_ades_conj_closure [closure]:
  assumes "P is PBMH_ades" "Q is PBMH_ades"
  shows "(P \<and> Q) is PBMH_ades"
  using assms
  by (simp add: Healthy_def' PBMH_ades_def PBMH_def pbmh_step_def
      fun_eq_iff; pred_auto; blast)

lemma PBMH_ades_disj:
  "PBMH_ades (P \<or> Q) = (PBMH_ades P \<or> PBMH_ades Q)"
  by (simp add: PBMH_ades_def PBMH_disj fun_eq_iff; pred_auto)

lemma PBMH_ades_disj_closure [closure]:
  "\<lbrakk> P is PBMH_ades; Q is PBMH_ades \<rbrakk> \<Longrightarrow>
   (P \<or> Q) is PBMH_ades"
  by (simp add: Healthy_def' PBMH_ades_disj)

lemma PBMH_ades_conj_ok:
  "PBMH_ades (P \<and> ok\<^sup>>) = (PBMH_ades P \<and> ok\<^sup>>)"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma PBMH_ades_not_ok_expr [simp]:
  "PBMH_ades (\<not> ok\<^sup><) = (\<not> ok\<^sup><)"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma PBMH_ades_false [simp]: "PBMH_ades false = false"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def fun_eq_iff;
      pred_auto)

lemma PBMH_ades_true [simp]: "PBMH_ades true = true"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def fun_eq_iff;
      pred_auto)

lemma PBMH_ades_ok_false:
  "PBMH_ades (P\<^sup>f) = (PBMH_ades P)\<^sup>f"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma PBMH_ades_ok_true:
  "PBMH_ades (P\<^sup>t) = (PBMH_ades P)\<^sup>t"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma PBMH_ades_ok_in_subst:
  "PBMH_ades (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>) =
   (PBMH_ades P)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma false_PBMH_ades [closure]: "false is PBMH_ades"
  by (simp add: Healthy_def')

lemma true_PBMH_ades [closure]: "true is PBMH_ades"
  by (simp add: Healthy_def')

lemma ades_state_choice_is_PBMH_ades [closure]:
  "ades_state_choice is PBMH_ades"
  by (simp add: Healthy_def' PBMH_ades_def PBMH_def pbmh_step_def
      ades_state_choice_def fun_eq_iff; pred_auto; blast)

lemma PBMH_ades_design_closure:
  assumes "F is PBMH_ades" "T is PBMH_ades"
  shows "((\<not> F) \<turnstile> T) is PBMH_ades"
  using assms
  by (simp add: Healthy_def' PBMH_ades_def design_def fun_eq_iff;
      pred_auto; blast)

(* Normal form for sequential composition of angelic designs.  This is
   the design-level calculation used by thesis Theorem T.H.3.2. *)
lemma ades_design_seq:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
    "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    and "(\<not> P) is PBMH_ades" "Q is PBMH_ades"
  shows "((P \<turnstile> Q) ;;\<^sub>A\<^sub>D (R \<turnstile> S)) =
    (((\<not> ((\<not> P) ;;\<^sub>A\<^sub>R true)) \<and>
      (\<not> (Q ;;\<^sub>A\<^sub>R (\<not> R)))) \<turnstile>
     (Q ;;\<^sub>A\<^sub>R (R \<longrightarrow> S)))"
proof -
  let ?B = "(\<not> R) \<or> (S \<and> ok\<^sup>>)"
  have B_refine: "true \<sqsubseteq> ?B"
    by pred_auto
  have absorb_not_ok:
      "(\<not> ok\<^sup><) \<sqsubseteq> ((\<not> ok\<^sup><) ;;\<^sub>A\<^sub>R ?B)"
    using aseq_ades_mono_right
      [where P="\<not> ok\<^sup><" and Q=true and R="?B",
       OF _ B_refine]
    by (simp add: Healthy_def' not_ok_aseq_ades_true)
  have absorb_not_P:
      "((\<not> P) ;;\<^sub>A\<^sub>R true) \<sqsubseteq>
       ((\<not> P) ;;\<^sub>A\<^sub>R ?B)"
    by (rule aseq_ades_mono_right[OF assms(5) B_refine])
  have B_split: "(Q ;;\<^sub>A\<^sub>R ?B) =
    ((Q ;;\<^sub>A\<^sub>R (\<not> R)) \<or>
     ((Q ;;\<^sub>A\<^sub>R (R \<longrightarrow> S)) \<and> ok\<^sup>>))"
    by (simp only: aseq_ades_ok_out_split[OF assms(6)]
        impl_neg_disj[of R S, symmetric])
  show ?thesis
    apply (simp only: angelic_design_seq_ok_cases
        design_ok_out_true_subst[OF assms(1) assms(2)]
        design_ok_out_false_subst[OF assms(1)]
        design_ok_in_true_subst[OF assms(3) assms(4)]
        design_ok_false)
    apply (simp only: aseq_ades_disj_distrib)
    apply (simp only: not_ok_aseq_ades_true B_split
        pred_ba.sup.assoc pred_ba.sup.commute pred_ba.sup.left_commute)
    apply (simp only: design_as_disj pred_ba.compl_inf
        pred_ba.double_compl pred_ba.sup.assoc
        pred_ba.sup.commute pred_ba.sup.left_commute)
    using absorb_not_P absorb_not_ok
    unfolding pred_refine_iff
    by (simp add: fun_eq_iff disj_pred_def; blast)
qed

(* Thesis Theorem T.4.5.1, with control-free relation components. *)
lemma angelic_rdesign_seq:
  fixes P Q R S :: "'s angelic_rel"
  assumes "PBMH (\<not> P) = (\<not> P)" "PBMH Q = Q"
  shows "((P \<turnstile>\<^sub>r Q) ;;\<^sub>A\<^sub>D (R \<turnstile>\<^sub>r S)) =
    (((\<not> ((\<not> P) ;;\<^sub>A true)) \<and> (\<not> (Q ;;\<^sub>A (\<not> R))))
      \<turnstile>\<^sub>r (Q ;;\<^sub>A (R \<longrightarrow> S)))"
proof -
  note form = ades_design_seq[where P="\<lceil>P\<rceil>\<^sub>D" and Q="\<lceil>Q\<rceil>\<^sub>D"
      and R="\<lceil>R\<rceil>\<^sub>D" and S="\<lceil>S\<rceil>\<^sub>D"]
  show ?thesis
    using form
    by (simp add: rdesign_def unrest PBMH_ades_lift Healthy_def'
        assms aseq_ades_lift ades_lift_logic aseq_ades_lift_true)
qed

(* PBMH_ades distributes over a design with a negated precondition. *)
lemma PBMH_ades_neg_design:
  "PBMH_ades ((\<not> F) \<turnstile> T) =
   ((\<not> PBMH_ades F) \<turnstile> PBMH_ades T)"
  by (simp add: design_as_disj PBMH_ades_disj PBMH_ades_conj_ok)

(* Paper Appendix A.1, Lemma 16 *)
lemma PBMH_ades_rdesign:
  "PBMH_ades (P \<turnstile>\<^sub>r Q) =
   ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r PBMH Q)"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

(* Paper Appendix A.1, Theorems 64 and 65 on the full design alphabet. *)
lemma PBMH_ades_H1_commute:
  "(PBMH_ades \<circ> H1) P = (H1 \<circ> PBMH_ades) P"
  by (simp only: comp_apply H1_def impl_neg_disj PBMH_ades_disj
      PBMH_ades_not_ok_expr)

lemmas PBMH_ades_H1_commute' = PBMH_ades_H1_commute[simplified comp_apply]

lemma PBMH_ades_H2_commute:
  "(PBMH_ades \<circ> H2) P = (H2 \<circ> PBMH_ades) P"
  by (simp only: comp_apply H2_split PBMH_ades_disj PBMH_ades_conj_ok
      PBMH_ades_ok_false PBMH_ades_ok_true)

lemmas PBMH_ades_H2_commute' = PBMH_ades_H2_commute[simplified comp_apply]

lemma H1_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "H1 P is PBMH_ades"
  by (simp only: Healthy_def' PBMH_ades_H1_commute' Healthy_if[OF assms])

lemma PBMH_ades_H1_H2_commute:
  "(PBMH_ades \<circ> H1 \<circ> H2) P =
   (H1 \<circ> H2 \<circ> PBMH_ades) P"
  by (simp only: comp_apply PBMH_ades_H1_commute' PBMH_ades_H2_commute')

end
