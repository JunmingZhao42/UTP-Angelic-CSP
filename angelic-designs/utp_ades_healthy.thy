section \<open>Angelic Design Healthiness Conditions\<close>
(* Paper Section 5.1, Definition 17. *)

theory utp_ades_healthy
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

(* Apply PBMH to the nested angelic-choice output while carrying ok' unchanged. *)
definition PBMH_ades :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "PBMH_ades P = (\<lambda> (s0, s1).
  let ac' = des_vars.more s1
  in PBMH (\<lambda> (s, ac). let s1' = des_vars.more_update (\<lambda>_. ac) s1
    in P (s, s1')) (s0, ac'))"

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
  shows "(P ;;\<^sub>A\<^sub>D Q) \<sqsubseteq> (P ;;\<^sub>A\<^sub>D R)"
  unfolding aseq_ades_def pred_refine_iff
  apply (clarsimp split: prod.splits)
  apply (erule PBMH_ades_upward[OF assms(1)])
  using assms(2)
  by (auto simp add: pred_refine_iff)

(* Monotonicity of design-level angelic composition.  As for
   \<open>aseq_ades_mono_right\<close>, the left operand must be upward closed. *)
lemma angelic_design_seq_mono:
  assumes "P is PBMH_ades" "P \<sqsubseteq> P'" "Q \<sqsubseteq> Q'"
  shows "(P ;;\<^sub>D\<^sub>A Q) \<sqsubseteq> (P' ;;\<^sub>D\<^sub>A Q')"
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
  shows "(P ;;\<^sub>A\<^sub>D Q) is PBMH_ades"
proof (rule Healthy_intro, rule ext)
  fix w :: "'a astate des_vars_ext \<times> 'a achoices des_vars_ext"
  obtain s0 ac' where w_eq [simp]: "w = (s0, ac')"
    by (cases w) auto
  show "PBMH_ades (P ;;\<^sub>A\<^sub>D Q) w = (P ;;\<^sub>A\<^sub>D Q) w"
  proof
    assume "PBMH_ades (P ;;\<^sub>A\<^sub>D Q) w"
    then obtain X where
        comp: "(P ;;\<^sub>A\<^sub>D Q) (s0, des_vars.more_update
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
    show "(P ;;\<^sub>A\<^sub>D Q) w"
      unfolding w_eq aseq_ades_def
      apply (simp only: prod.case)
      apply (rule PBMH_ades_upward[OF assms(1) P_at])
      using S_sub by auto
  next
    assume "(P ;;\<^sub>A\<^sub>D Q) w"
    then show "PBMH_ades (P ;;\<^sub>A\<^sub>D Q) w"
      by (rule PBMH_ades_weaken)
  qed
qed

(* The final ok observation is constant across the angelic-choice
   comprehension, so it can be pulled out of the right operand. *)
lemma aseq_ades_ok_out_split:
  assumes "P is PBMH_ades"
  shows "(P ;;\<^sub>A\<^sub>D (X \<or> (Y \<and> ok\<^sup>>))) =
    ((P ;;\<^sub>A\<^sub>D X) \<or> ((P ;;\<^sub>A\<^sub>D (X \<or> Y)) \<and> ok\<^sup>>))"
proof (rule ext)
  fix w :: "'a astate des_vars_ext \<times> 'a achoices des_vars_ext"
  obtain s0 ac' where w_eq [simp]: "w = (s0, ac')" by (cases w) auto
  have evalp: "((X \<or> (Y \<and> ok\<^sup>>)) (a, ac')) \<longleftrightarrow>
      (X (a, ac') \<or> (Y (a, ac') \<and> ok\<^sub>v ac'))" for a
    by pred_auto
  have evalo: "((Z \<and> ok\<^sup>>) (s0, ac')) \<longleftrightarrow> (Z (s0, ac') \<and> ok\<^sub>v ac')"
    for Z :: "'a angelic_design"
    by pred_auto
  show "(P ;;\<^sub>A\<^sub>D (X \<or> (Y \<and> ok\<^sup>>))) w =
      ((P ;;\<^sub>A\<^sub>D X) \<or> ((P ;;\<^sub>A\<^sub>D (X \<or> Y)) \<and> ok\<^sup>>)) w"
  proof (cases "ok\<^sub>v ac'")
    case True
    then have "(P ;;\<^sub>A\<^sub>D (X \<or> (Y \<and> ok\<^sup>>))) (s0, ac') =
        (P ;;\<^sub>A\<^sub>D (X \<or> Y)) (s0, ac')"
      by (simp add: aseq_ades_def evalp disj_pred_def; pred_auto)
    moreover have "(P ;;\<^sub>A\<^sub>D X) (s0, ac') \<Longrightarrow>
        (P ;;\<^sub>A\<^sub>D (X \<or> Y)) (s0, ac')"
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
    then have "(P ;;\<^sub>A\<^sub>D (X \<or> (Y \<and> ok\<^sup>>))) (s0, ac') =
        (P ;;\<^sub>A\<^sub>D X) (s0, ac')"
      by (simp add: aseq_ades_def evalp disj_pred_def; pred_auto)
    then show ?thesis
      using False
      by (auto simp add: disj_pred_def conj_pred_def evalo
          des_vars.ok_def)
  qed
qed

lemma PBMH_ades_idem: "PBMH_ades (PBMH_ades P) = PBMH_ades P"
  by (simp add: PBMH_ades_def fun_eq_iff PBMH_idem)

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
  shows "((P \<turnstile> Q) ;;\<^sub>D\<^sub>A (R \<turnstile> S)) =
    (((\<not> ((\<not> P) ;;\<^sub>A\<^sub>D true)) \<and>
      (\<not> (Q ;;\<^sub>A\<^sub>D (\<not> R)))) \<turnstile>
     (Q ;;\<^sub>A\<^sub>D (R \<longrightarrow> S)))"
proof -
  let ?B = "(\<not> R) \<or> (S \<and> ok\<^sup>>)"
  have B_refine: "true \<sqsubseteq> ?B"
    by pred_auto
  have absorb_not_ok:
      "(\<not> ok\<^sup><) \<sqsubseteq> ((\<not> ok\<^sup><) ;;\<^sub>A\<^sub>D ?B)"
    using aseq_ades_mono_right
      [where P="\<not> ok\<^sup><" and Q=true and R="?B",
       OF _ B_refine]
    by (simp add: Healthy_def' not_ok_aseq_ades_true)
  have absorb_not_P:
      "((\<not> P) ;;\<^sub>A\<^sub>D true) \<sqsubseteq>
       ((\<not> P) ;;\<^sub>A\<^sub>D ?B)"
    by (rule aseq_ades_mono_right[OF assms(5) B_refine])
  have B_split: "(Q ;;\<^sub>A\<^sub>D ?B) =
    ((Q ;;\<^sub>A\<^sub>D (\<not> R)) \<or>
     ((Q ;;\<^sub>A\<^sub>D (R \<longrightarrow> S)) \<and> ok\<^sup>>))"
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
  shows "((P \<turnstile>\<^sub>r Q) ;;\<^sub>D\<^sub>A (R \<turnstile>\<^sub>r S)) =
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
  "A (P \<sqinter>\<^sub>D\<^sub>A Q) = (A P \<sqinter>\<^sub>D\<^sub>A A Q)"
  by (simp add: angelic_design_demonic A_disj)

(* Thesis Theorem T.4.5.12 *)
lemma A_demonic_closure:
  assumes "P is A" "Q is A"
  shows "A (P \<sqinter>\<^sub>D\<^sub>A Q) = (P \<sqinter>\<^sub>D\<^sub>A Q)"
  using assms by (simp add: A_demonic Healthy_def')

(* Thesis Theorem T.4.5.16. *)
lemma A_angelic_closure:
  assumes "P is A" "Q is A"
  shows "P \<squnion>\<^sub>D\<^sub>A Q is A"
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
      "P \<squnion>\<^sub>D\<^sub>A Q = (?Pre \<turnstile>\<^sub>r ?Post)"
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
  "P \<sqinter>\<^sub>D\<^sub>A \<bottom>\<^sub>D = \<bottom>\<^sub>D"
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
  shows "(P ;;\<^sub>D\<^sub>A Q) is PBMH_ades"
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
  shows "(P ;;\<^sub>D\<^sub>A Q) is \<^bold>H"
proof -
  let ?F = "PBMH (\<not> pre\<^sub>D P)"
  let ?T = "PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  have P_form: "P = ((\<not> ?F) \<turnstile>\<^sub>r ?T)"
    by (rule A_healthy_design_form[OF assms(1)])
  have Q_form: "Q = (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q)"
    using H1_H2_eq_rdesign[of Q] by (simp only: Healthy_if[OF assms(2)])
  have normal:
    "((\<not> ?F) \<turnstile>\<^sub>r ?T) ;;\<^sub>D\<^sub>A (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q) =
      angelic_design_seq_simplified ((\<not> ?F) \<turnstile>\<^sub>r ?T)
        (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q)"
    by (rule angelic_design_seq_eq_simplified;
        simp add: PBMH_idem PBMH_conj_nonempty)
  have "(((\<not> ?F) \<turnstile>\<^sub>r ?T) ;;\<^sub>D\<^sub>A
      (pre\<^sub>D Q \<turnstile>\<^sub>r post\<^sub>D Q)) is \<^bold>H"
    by (simp only: normal angelic_design_seq_simplified_def Healthy_def';
        simp add: H1_rdesign H2_rdesign)
  then show ?thesis by (simp only: P_form[symmetric] Q_form[symmetric])
qed

lemma angelic_design_seq_A0_closure:
  assumes "Q is A"
  shows "(P ;;\<^sub>D\<^sub>A Q) is A0"
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
  shows "(P ;;\<^sub>D\<^sub>A Q) is A"
proof -
  have Q_H: "Q is \<^bold>H"
    using A_is_H[of Q] by (simp only: Healthy_if[OF assms(2)] Healthy_def')
  have H: "(P ;;\<^sub>D\<^sub>A Q) is \<^bold>H"
    by (rule angelic_design_seq_H_closure[OF assms(1) Q_H])
  have PBMH: "(P ;;\<^sub>D\<^sub>A Q) is PBMH_ades"
    by (rule angelic_design_seq_PBMH_closure;
        rule A_is_PBMH_ades; rule assms)
  have A0: "(P ;;\<^sub>D\<^sub>A Q) is A0"
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
  shows "(Skip_AD ;;\<^sub>D\<^sub>A P) = P"
proof -
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using H1_H2_eq_rdesign[of P] by (simp only: Healthy_if[OF assms])
  have unit: "(Skip_AD ;;\<^sub>D\<^sub>A (R \<turnstile>\<^sub>r S)) = (R \<turnstile>\<^sub>r S)"
    for R S :: "'s angelic_rel"
    by (simp add: Skip_AD_def arel_to_ades_def angelic_design_seq_def fun_eq_iff;
        pred_auto)
  show ?thesis
    using unit[of "pre\<^sub>D P" "post\<^sub>D P"] by (simp only: P_form[symmetric])
qed

(* Thesis Theorems T.4.5.7 and T.4.5.8. Right identity requires a normal precondition. *)
lemma Skip_AD_seq_right_normal:
  assumes "P is A"
  shows "(P ;;\<^sub>D\<^sub>A Skip_AD) =
    ((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) \<turnstile>\<^sub>r post\<^sub>D P)"
proof -
  let ?F = "PBMH (\<not> pre\<^sub>D P)"
  let ?T = "PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  have P_form: "P = ((\<not> ?F) \<turnstile>\<^sub>r ?T)"
    by (rule A_healthy_design_form[OF assms])
  have empty: "(?T ;;\<^sub>A false) = false"
    by (simp add: aseq_def fun_eq_iff; pred_auto)
  have seq: "(P ;;\<^sub>D\<^sub>A Skip_AD) =
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
  shows "(P ;;\<^sub>D\<^sub>A Skip_AD) = P \<longleftrightarrow> (out\<alpha> \<sharp> pre\<^sub>D P)"
proof -
  have H: "P is \<^bold>H"
    using A_is_H[of P] by (simp only: Healthy_if[OF assms] Healthy_def')
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using H1_H2_eq_rdesign[of P] by (simp only: Healthy_if[OF H])
  have fixed_iff: "(P ;;\<^sub>D\<^sub>A Skip_AD) = P \<longleftrightarrow>
      (\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) = pre\<^sub>D P"
  proof
    assume fixed: "(P ;;\<^sub>D\<^sub>A Skip_AD) = P"
    show "(\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) = pre\<^sub>D P"
      using arg_cong[where f="pre\<^sub>D", OF fixed]
      by (simp only: Skip_AD_seq_right_normal[OF assms] rdesign_pre)
  next
    assume fixed: "(\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true)) = pre\<^sub>D P"
    show "(P ;;\<^sub>D\<^sub>A Skip_AD) = P"
      by (simp only: Skip_AD_seq_right_normal[OF assms] fixed P_form[symmetric])
  qed
  show ?thesis by (simp only: fixed_iff aseq_univ_pre_iff)
qed

lemma Skip_AD_seq_right_unit_iff_normal:
  assumes "P is A"
  shows "(P ;;\<^sub>D\<^sub>A Skip_AD) = P \<longleftrightarrow> P is \<^bold>N"
proof -
  have H: "P is \<^bold>H"
    using A_is_H[of P] by (simp only: Healthy_if[OF assms] Healthy_def')
  show ?thesis
    by (simp only: Skip_AD_seq_right_unit_iff[OF assms];
        blast intro: H1_H3_intro[OF H] H3_unrest_out_alpha)
qed

lemma Skip_AD_seq_right_unit:
  assumes "P is A" "P is \<^bold>N"
  shows "(P ;;\<^sub>D\<^sub>A Skip_AD) = P"
  using Skip_AD_seq_right_unit_iff_normal[OF assms(1)] assms(2) by blast

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
  the final choice set; the initial observation and both outer control
  observations are preserved.
\<close>
definition A2 :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A2 P = (\<lambda>(s0, out).
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

lemma A2_arel_to_ades:
  "A2 (arel_to_ades P) = arel_to_ades (A2_rel P)"
  by (simp add: arel_to_ades_def A2_rdesign
      A2_rel_eq_expanded A2_rel_expanded_def; pred_auto)

lemma A2_obs:
  "A2 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c {}) \<or>
     (\<exists>z\<in>X. P (ades_obs b s0 c {z})))"
  by (simp add: A2_def)

lemma A2_idem: "A2 (A2 P) = A2 P"
  by (simp add: A2_def fun_eq_iff comp_def; blast)

lemma A2_Idempotent [closure]: "Idempotent A2"
  by (simp add: Idempotent_def A2_idem)

lemma A2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A2 P \<sqsubseteq> A2 Q"
  by (auto simp add: A2_def pred_refine_iff split: prod.splits)

lemma A2_Monotonic [closure]: "Monotonic A2"
  by (rule MonotonicI, rule A2_mono)

lemma A2_empty_choice:
  "A2 P (x, \<lparr>ok\<^sub>v = b,
    \<dots> = \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>\<rparr>) =
   P (x, \<lparr>ok\<^sub>v = b,
    \<dots> = \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>\<rparr>)"
  by (simp add: A2_def)

lemma A2_healthy [closure]: "A2 P is A2"
  by (simp add: Healthy_def' A2_idem)

lemma A2_lift:
  "A2 \<lceil>P\<rceil>\<^sub>D = \<lceil>A2_rel P\<rceil>\<^sub>D"
  by (simp add: A2_def A2_rel_eq_expanded A2_rel_expanded_def
      fun_eq_iff; pred_auto)

lemma A2_def':
  "A2 P = PBMH_ades (P ;;\<^sub>A\<^sub>D \<lceil>singleton_ac\<rceil>\<^sub>D)"
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
  by (simp only: A2_def' PBMH_ades_idem)

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
  shows "(P ;;\<^sub>D\<^sub>A Q) is A2"
proof -
  have "A2 (A2 P ;;\<^sub>D\<^sub>A A2 Q) = (A2 P ;;\<^sub>D\<^sub>A A2 Q)"
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

lemma arel_indep_A3_rel:
  fixes R :: "'s angelic_rel"
  assumes "\<And>s0 a b. R (s0, a) = R (s0, b)"
  shows "R is A3_rel"
  using assms by (simp add: A3_rel_healthy'; blast)

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

lemma H_A3_intro:
  fixes P :: "'s angelic_design"
  assumes "P is \<^bold>H" "pre\<^sub>D P is A3_rel"
  shows "P is A3"
  using assms H1_H2_eq_rdesign[of P]
  by (simp add: Healthy_def' A3_def)

lemma A3_healthy_obsI:
  fixes P :: "'s angelic_design"
  assumes "P is \<^bold>H"
    "\<And>s0. \<not> P (ades_obs True s0 False {}) \<Longrightarrow>
      \<exists>z. \<not> P (ades_obs True s0 False {z})"
  shows "P is A3"
proof (rule H_A3_intro[OF assms(1)])
  have pre:
    "pre\<^sub>D P (\<lparr>s\<^sub>v = s0, \<dots> = ()\<rparr>, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>) =
      (\<not> P (ades_obs True s0 False X))"
    for s0 X
    by (pred_simp; simp add: des_vars_collapse)

  show "pre\<^sub>D P is A3_rel"
    unfolding A3_rel_healthy'
    apply (rule allI)
    subgoal for x by (cases x; simp add: pre assms(2))
    done
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

subsection \<open>Normal Angelic Designs\<close>

lemma N_preD_indep:
  fixes P :: "'s angelic_design" and s0 :: "'s astate" and a b :: "'s achoices"
  assumes "P is \<^bold>N"
  shows "pre\<^sub>D P (s0, a) = pre\<^sub>D P (s0, b)"
proof -
  have u: "$ac\<^sup>> \<sharp> pre\<^sub>D P"
    by (rule unrest_out_var; simp add: H3_unrest_out_alpha[OF assms])
  have put_P: "\<forall>s0 acr v.
      pre\<^sub>D P (s0, achoices.ac\<^sub>v_update (\<lambda>_. v) acr) = pre\<^sub>D P (s0, acr)"
    using u
    apply (subst (asm) unrest_lens)
     apply simp
    by (simp add: lens_defs achoices.ac_def case_prod_beta split_paired_All)
  have "pre\<^sub>D P (s0, b) =
      pre\<^sub>D P (s0, achoices.ac\<^sub>v_update (\<lambda>_. achoices.ac\<^sub>v b) a)"
    by (cases a; cases b; simp)
  also have "... = pre\<^sub>D P (s0, a)"
    using put_P by blast
  finally show ?thesis by (rule sym)
qed


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
  shows "((\<not> ac_non_empty) \<and> (T ;;\<^sub>A\<^sub>D Y)) =
    ((\<not> ac_non_empty) \<and> (T ;;\<^sub>A\<^sub>D Z))"
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
