section \<open>From Designs to Angelic Designs\<close>

theory utp_ades_designs
  imports utp_ades_healthy
begin

subsection \<open>Predicate Mapping\<close>

(* Paper Definition 23.
   p2ac(P)(s, A) = \<exists>z\<in>A. P(s, z) *)
definition p2ac :: "('s, 's) urel \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "p2ac P = (\<lambda> (s0, ac').
  \<exists> z \<in> achoices.ac\<^sub>v ac'. P (astate.s\<^sub>v s0, z))"

(* The second conjunction of the d2ac pre-condition:
  \<not>P^f [s/in\<alpha>_ok]; true \<equiv> \<exists>z. P(s, z) *)
definition p2ac_exist :: "('s, 's) urel \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "p2ac_exist P = (\<lambda> (s0, ac').
  \<exists> z. P (astate.s\<^sub>v s0, z))"

(* Thesis Appendix C.5.2, Lemma L.C.5.3. *)
lemma p2ac_false [simp]:
  "p2ac false = false"
  by (pred_auto)

(* Thesis Appendix C.5.2, Lemma L.C.5.2. *)
lemma p2ac_true [simp]:
  "p2ac true = (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
  by (pred_auto)

(* Thesis Theorem T.4.6.1. *) 
lemma p2ac_disj:
  "p2ac (P \<or> Q) = (p2ac P \<or> p2ac Q)"
  by (pred_auto)

(* Thesis Theorem T.4.6.2. *)
lemma p2ac_conj:
  "p2ac (P \<and> Q) x \<longrightarrow> (p2ac P \<and> p2ac Q) x"
  by (pred_auto)

(* Lift p2ac through the design shell, preserving ok and ok'.  This is the
   shallow-embedding counterpart of applying the paper's p2ac to a design. *)
definition p2ac_des :: "'s des_hrel \<Rightarrow> 's angelic_design" where
[pred]: "p2ac_des P = (\<lambda> (s0, ac').
  \<exists> z \<in> achoices.ac\<^sub>v (des_vars.more ac').
    P (\<lparr>ok\<^sub>v = ok\<^sub>v s0,
         \<dots> = astate.s\<^sub>v (des_vars.more s0)\<rparr>,
       \<lparr>ok\<^sub>v = ok\<^sub>v ac', \<dots> = z\<rparr>))"

(* Paper Theorem 72 *)
lemma p2ac_des_design:
  "(ac_non_empty \<and> p2ac_des ((\<not> P) \<turnstile>\<^sub>r Q)) =
   (ac_non_empty \<and> ((\<not> p2ac P) \<turnstile>\<^sub>r p2ac Q))"
  by (simp add: ac_non_empty_def p2ac_des_def p2ac_def
      rdesign_refinement; pred_auto)

(* Paper Appendix A.3, Lemma 26 *)
lemma PBMH_p2ac [simp]:
  "PBMH (p2ac P) = p2ac P"
  by (pred_auto)

(* Thesis Theorem T.4.6.3, in relational form. *)
lemma A2_rel_p2ac [simp]:
  "A2_rel (p2ac P) = p2ac P"
  by (simp add: A2_rel_eq_expanded, pred_auto)

subsection \<open>Design to Angelic Design\<close>

(* Paper Definition 21. *)
definition d2ac :: "'s des_hrel \<Rightarrow> 's angelic_design" where
[pred]: "d2ac P =
  ((\<not> p2ac (\<not> pre\<^sub>D P) \<and> p2ac_exist (pre\<^sub>D P)) \<turnstile>\<^sub>r p2ac (post\<^sub>D P))"

(* \<forall>z\<in>A. P(s, z)) \<and> (\<exists>z. P(s, z)) \<turnstile>\<^sub>r \<exists>z\<in>A. Q(s, z) *)
lemma d2ac_rdesign:
  "d2ac (P \<turnstile>\<^sub>r Q) = ((\<not> p2ac (\<not> P) \<and> p2ac_exist P) \<turnstile>\<^sub>r p2ac Q)"
  by (simp add: d2ac_def rdesign_refinement, pred_auto)

lemma d2ac_A0 [simp]:
  "A0 (d2ac P) = d2ac P"
  by (simp add: A0_def d2ac_def rdesign_refinement, pred_auto)

lemma d2ac_A1 [simp]:
  "A1 (d2ac P) = d2ac P"
  by (simp add: A1_def d2ac_def rdesign_refinement, pred_auto)

lemma d2ac_A [simp]:
  "A (d2ac P) = d2ac P"
  by (simp add: A_def)

lemma d2ac_A2 [simp]:
  "A2 (d2ac P) = d2ac P"
  by (simp add: A2_def d2ac_def rdesign_refinement, pred_auto)

lemma d2ac_is_A [closure]:
  "d2ac P is A"
  by (simp add: Healthy_def')

lemma d2ac_is_A2 [closure]:
  "d2ac P is A2"
  by (simp add: Healthy_def')

lemma d2ac_mono:
  assumes "P \<sqsubseteq> Q"
  shows "d2ac P \<sqsubseteq> d2ac Q"
  using design_refine_thms(1)[OF assms] design_refine_thms(2)[OF assms]
  apply (simp add: d2ac_def)
  apply (rule rdesign_refine_intro')
   apply (pred_auto; blast)
  by (pred_auto; blast)

subsection \<open>Angelic Design to Design\<close>

(* Apply PBMH to the nested angelic-choice output while carrying ok' unchanged. *)
definition PBMH_ades :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "PBMH_ades P = (\<lambda> (s0, s1).
  let ac' = des_vars.more s1
  in PBMH (\<lambda> (s, ac). let s1' = des_vars.more_update (\<lambda>_. ac) s1
    in P (s, s1')) (s0, ac'))"

lemma PBMH_ades_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> PBMH_ades P \<sqsubseteq> PBMH_ades Q"
  by (simp add: PBMH_ades_def; pred_auto; blast)

lemma PBMH_ades_Monotonic [closure]: "Monotonic PBMH_ades"
  by (rule MonotonicI, rule PBMH_ades_mono)

(* Paper Appendix A.1, Lemma 16 *)
lemma PBMH_ades_rdesign:
  "PBMH_ades (P \<turnstile>\<^sub>r Q) =
   ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r PBMH Q)"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma A1_PBMH_ades_rdesign:
  "A1 (P \<turnstile>\<^sub>r Q) = PBMH_ades (P \<turnstile>\<^sub>r Q)"
  by (simp add: PBMH_rdesign PBMH_ades_rdesign)

(* Paper Definition 17 defines A1 on designs and observes that A1 and PBMH are
   interchangeable.  In the shallow embedding, H records that an arbitrary
   predicate P is a design. *)
lemma A1_eq_PBMH_ades:
  assumes "P is \<^bold>H"
  shows "A1 P = PBMH_ades P"
proof -
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using H1_H2_eq_rdesign[of P] assms
    by (simp add: Healthy_def')
  show ?thesis
    using A1_PBMH_ades_rdesign[of "pre\<^sub>D P" "post\<^sub>D P"]
    by (simp only: P_form[symmetric])
qed

(* Paper Definition 24. *)
definition ac2p :: "'s angelic_design \<Rightarrow> 's des_hrel" where
[pred]: "ac2p P = (\<lambda> (s0, s1).
  let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                   \<dots> = StateII (des_vars.more s0)\<rparr>;
      ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                    \<dots> = \<lparr>ac\<^sub>v = {des_vars.more s1}, \<dots> = ()\<rparr>\<rparr>
  in PBMH_ades P (ades_in, ades_out))"

(* The relation-level instance of ac2p used in the paper's design proof. *)
definition ac2p_rel :: "'s angelic_rel \<Rightarrow> ('s, 's) urel" where
[pred]: "ac2p_rel P = (\<lambda> (s0, s1).
  PBMH P (StateII s0, \<lparr>ac\<^sub>v = {s1}, \<dots> = ()\<rparr>))"

(* Thesis Appendix C.5.3, Lemma L.C.5.20 (ac2p-alternative-3). *)
lemma ac2p_subset:
  "ac2p P = (\<lambda> (s0, s1). \<exists> ac.
    let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                     \<dots> = StateII (des_vars.more s0)\<rparr>;
        ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                      \<dots> = \<lparr>ac\<^sub>v = ac, \<dots> = ()\<rparr>\<rparr>
    in P (ades_in, ades_out) \<and> ac \<subseteq> {des_vars.more s1})"
  by (pred_auto)

lemma ac2p_rel_subset:
  "ac2p_rel P = (\<lambda> (s0, s1). \<exists> ac.
    P (StateII s0, \<lparr>ac\<^sub>v = ac, \<dots> = ()\<rparr>) \<and> ac \<subseteq> {s1})"
  by (pred_auto)

(* Paper Lemma 4. ac2p(P)(s,z) = \<exists> ac. P(s, ac) ∧ \<forall>y \<in> ac. y = z *)
(* My understanding: ac2p(P)(s,z) = P(s, {z}) *)
lemma ac2p_alt:
  "ac2p P = (\<lambda> (s0, s1). \<exists> ac.
    let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                     \<dots> = StateII (des_vars.more s0)\<rparr>;
        ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                      \<dots> = \<lparr>ac\<^sub>v = ac, \<dots> = ()\<rparr>\<rparr>
    in P (ades_in, ades_out) \<and> (\<forall> z \<in> ac. z = des_vars.more s1))"
  by (pred_auto)

(* Reactive-design instance of ac2p. *)
lemma ac2p_rdesign:
  "ac2p (P \<turnstile>\<^sub>r Q) = ((\<not> ac2p_rel (\<not> P)) \<turnstile>\<^sub>r ac2p_rel Q)"
  by (simp only: ac2p_subset ac2p_rel_subset; pred_auto)

(* Paper Lemma 24 *)
lemma ac2p_design:
  assumes "P is \<^bold>H"
  shows "ac2p P = ((\<not> ac2p (P\<^sup>f)) \<turnstile> ac2p (P\<^sup>t))"
  by (subst (1) Healthy_if[OF assms, symmetric];
      simp only: H1_H2_eq_design design_def ac2p_subset;
      pred_auto)
  
subsection \<open>Isomorphism and Galois Connection\<close>

lemma ac2p_d2ac_rdesign:
  "ac2p (d2ac (P \<turnstile>\<^sub>r Q)) = (P \<turnstile>\<^sub>r Q)"
  by (simp only: d2ac_rdesign ac2p_subset; pred_auto)

(* Paper Theorem 5. *)
theorem ac2p_d2ac:
  assumes "P is \<^bold>H"
  shows "ac2p (d2ac P) = P"
proof -
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using H1_H2_eq_rdesign[of P] assms
    by (simp add: Healthy_def')
  have "ac2p (d2ac P) =
      ac2p (d2ac (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P))"
    by (rule arg_cong[OF P_form])
  also have "... = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    by (rule ac2p_d2ac_rdesign)
  also have "... = P"
    using P_form by (rule sym)
  finally show ?thesis .
qed

(* Thesis Theorem T.5.3.6, specialised to the relation-level mapping. *)
lemma p2ac_ac2p_rel_refine:
  assumes "PBMH P = P"
  shows "P \<sqsubseteq> p2ac (ac2p_rel P)"
  using assms
  by (simp only: ac2p_rel_subset p2ac_def; pred_auto)

lemma ac2p_rel_feasible_unrest:
  assumes "$ac\<^sup>> \<sharp> P"
  shows "taut ((\<not> P) \<longrightarrow> p2ac_exist (\<not> ac2p_rel P))"
  using assms
  apply (simp only: ac2p_rel_subset p2ac_exist_def)
  apply (pred_auto)
  apply (rule_tac x=undefined in exI)
  by auto

lemma d2ac_ac2p_rdesign_refine:
  assumes "PBMH (\<not> P) = (\<not> P)" "PBMH Q = Q"
    and feasible: "taut (P \<longrightarrow> p2ac_exist (\<not> ac2p_rel (\<not> P)))"
  shows "(P \<turnstile>\<^sub>r Q) \<sqsubseteq> d2ac (ac2p (P \<turnstile>\<^sub>r Q))"
  apply (simp only: ac2p_rdesign d2ac_rdesign)
  apply (rule rdesign_refine_intro)
   apply (insert p2ac_ac2p_rel_refine[OF assms(1)] feasible)
   apply (pred_auto)
  apply (insert p2ac_ac2p_rel_refine[OF assms(2)])
  by (pred_auto)

(* The A0-A2 rdesign form is preserved by the round trip up to refinement. *)
lemma d2ac_ac2p_A2_rdesign_refine:
  "d2ac (ac2p ((\<not> A2_rel (\<not> P)) \<turnstile>\<^sub>r
      A2_rel (Q \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)))
    \<sqsubseteq> ((\<not> A2_rel (\<not> P)) \<turnstile>\<^sub>r
      A2_rel (Q \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
proof -
  have round_trip: "p2ac (ac2p_rel R) =
      (A2_rel R \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)" for R
    apply (simp only: p2ac_def ac2p_rel_subset A2_rel_eq_expanded
        A2_rel_expanded_def)
    apply (pred_auto)
    subgoal premises assms for s0 ac' z ac
      using assms subset_singletonD[OF assms(3)]
      by (elim disjE; simp)
    done
  show ?thesis
    apply (simp only: ac2p_rdesign d2ac_rdesign round_trip A2_rel_idem)
    apply (rule rdesign_refine_intro)
     apply (simp add: p2ac_exist_def ac2p_rel_subset
        A2_rel_eq_expanded A2_rel_expanded_def)
     apply (pred_auto; blast)
    apply (simp add: A2_rel_eq_expanded A2_rel_expanded_def)
    by (pred_auto)
qed

(* Counterexample: P_dummy \<equiv> (ac' = \<emptyset>) \<turnstile> (ac' \<noteq> \<emptyset>). *)
definition P_dummy :: "unit angelic_design" where
[pred]: "P_dummy =
  (($ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e \<turnstile>\<^sub>r
   ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"

lemma P_dummy_is_A:
  "P_dummy is A"
  by (simp add: Healthy_def' P_dummy_def A_design_form, pred_auto)

lemma P_dummy_not_normal:
  "\<not> (P_dummy is \<^bold>N)"
proof
  assume normal: "P_dummy is \<^bold>N"
  have out_unrest: "out\<alpha> \<sharp> pre\<^sub>D P_dummy"
    by (rule H3_unrest_out_alpha[OF normal])
  have "$ac\<^sup>> \<sharp> pre\<^sub>D P_dummy"
    by (rule unrest_out_var[OF _ out_unrest], simp)
  then show False
    by (simp add: P_dummy_def unrest unrest_lens; pred_auto)
qed

lemma ac2p_P_dummy:
  "ac2p P_dummy = (false \<turnstile>\<^sub>r true)"
  unfolding P_dummy_def
  apply (simp only: ac2p_rdesign ac2p_rel_subset)
  by (pred_auto)

lemma d2ac_ac2p_P_dummy:
  "d2ac (ac2p P_dummy) = true"
  apply (simp only: ac2p_P_dummy d2ac_rdesign p2ac_false p2ac_true
      p2ac_exist_def)
  by (pred_auto)

lemma P_dummy_fails_theorem6:
  "\<not> (P_dummy \<sqsubseteq> d2ac (ac2p P_dummy))"
  apply (simp only: d2ac_ac2p_P_dummy P_dummy_def)
  by (pred_auto)

(* Paper Theorem 6.
   Normality is required: it makes the precondition independent of the output choice ac'. *)
lemma d2ac_ac2p_normal:
  fixes P :: "'s angelic_design"
  assumes healthy: "P is A"
    and normal: "P is \<^bold>N"
  shows "P \<sqsubseteq> d2ac (ac2p P)"
proof -
  define pre_A :: "'s angelic_rel" where
    "pre_A \<equiv> \<not> PBMH (\<not> pre\<^sub>D P)"
  define post_A :: "'s angelic_rel" where
    "post_A \<equiv> PBMH (post\<^sub>D P) \<and>
      ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  have pre_unrest: "$ac\<^sup>> \<sharp> pre\<^sub>D P"
    by (rule unrest_out_var; simp add: H3_unrest_out_alpha[OF normal])
  have pre_A_eq: "pre_A = pre\<^sub>D P"
    using PBMH_unrest_ac[of "\<not> pre\<^sub>D P"] pre_unrest
    by (simp add: pre_A_def unrest)
  have failure_pre_unrest: "$ac\<^sup>> \<sharp> (\<not> pre_A)"
    using pre_unrest by (simp add: pre_A_eq unrest)
  have feasible: "taut (pre_A \<longrightarrow> p2ac_exist (\<not> ac2p_rel (\<not> pre_A)))"
    using ac2p_rel_feasible_unrest[OF failure_pre_unrest] by simp
  have failure_healthy: "PBMH (\<not> pre_A) = (\<not> pre_A)"
    by (rule PBMH_unrest_ac[OF failure_pre_unrest])
  have post_A_healthy: "PBMH post_A = post_A"
    by (simp add: post_A_def PBMH_conj_nonempty)
  have P_form: "P = (pre_A \<turnstile>\<^sub>r post_A)"
    using A_healthy_design_form[OF healthy]
    by (simp add: pre_A_def post_A_def)
  from d2ac_ac2p_rdesign_refine[
    OF failure_healthy post_A_healthy feasible]
  show ?thesis
    by (simp only: P_form)
qed

(* Paper Theorem 7. *)
lemma d2ac_ac2p_A2:
  fixes P :: "'s angelic_design"
  defines "Pre \<equiv> \<not> PBMH (\<not> pre\<^sub>D P)"
    and "Post \<equiv> PBMH (post\<^sub>D P)"
  assumes healthy: "P is A"
    and a2_healthy: "P is A2"
  shows "d2ac (ac2p P) \<sqsubseteq> P"
proof -
  have P_form: "P = (Pre \<turnstile>\<^sub>r
      (Post \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
    using A_healthy_design_form[OF healthy]
    by (simp add: Pre_def Post_def)
  have P_A2_form: "P = ((\<not> A2_rel (\<not> Pre)) \<turnstile>\<^sub>r
      A2_rel (Post \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
    using a2_healthy
    by (simp only: Healthy_def' P_form A2_rdesign)
  from d2ac_ac2p_A2_rdesign_refine[of Pre Post]
  show ?thesis
    by (simp only: P_A2_form)
qed

(* Paper Theorem 8.
   Normality is required in the d2d direction because of Theorem 6. *)
lemma d2ac_ac2p_A2_normal:
  assumes healthy: "P is A"
    and a2_healthy: "P is A2"
    and normal: "P is \<^bold>N"
  shows "d2ac (ac2p P) = P"
  apply (rule ref_antisym)
   apply (rule d2ac_ac2p_normal[OF healthy normal])
  by (rule d2ac_ac2p_A2[OF healthy a2_healthy])

(* Pre(s, <emptyset>) ⟹ <exists>z. Pre(s, {z}) *)
lemma d2ac_ac2p_normal_weaker:
  fixes P :: "'s angelic_design"
  assumes healthy: "P is A"
    and singleton_supported:
      "\<forall> s :: 's astate. pre\<^sub>D P
          (s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<longrightarrow>
        (\<exists> z. pre\<^sub>D P
          (s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>))"
  shows "P \<sqsubseteq> d2ac (ac2p P)"
proof -
  define pre_A :: "'s angelic_rel" where
    "pre_A \<equiv> \<not> PBMH (\<not> pre\<^sub>D P)"
  define post_A :: "'s angelic_rel" where
    "post_A \<equiv> PBMH (post\<^sub>D P) \<and>
      ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  have P_form: "P = (pre_A \<turnstile>\<^sub>r post_A)"
    using A_healthy_design_form[OF healthy]
    by (simp add: pre_A_def post_A_def)
  have pre_A_eq: "pre_A = pre\<^sub>D P"
    by (simp add: P_form)
  have singleton_supported_A:
      "\<forall>s. pre_A (s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<longrightarrow>
        (\<exists>z. pre_A (s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>))"
    using singleton_supported by (simp add: pre_A_eq)
  have pre_A_downward:
      "B \<subseteq> A \<Longrightarrow>
       pre_A (s, \<lparr>ac\<^sub>v = A, \<dots> = ()\<rparr>) \<Longrightarrow>
       pre_A (s, \<lparr>ac\<^sub>v = B, \<dots> = ()\<rparr>)"
    for s A B
    by (simp add: pre_A_def PBMH_def pbmh_step_def; pred_auto; blast)
  have failure_healthy: "PBMH (\<not> pre_A) = (\<not> pre_A)"
    by (simp add: pre_A_def PBMH_idem)
  have feasible:
      "taut (pre_A \<longrightarrow> p2ac_exist (\<not> ac2p_rel (\<not> pre_A)))"
  proof (rule tautI)
    fix x :: "'s astate \<times> 's achoices"
    obtain st cs where x_eq: "x = (st, cs)"
      by (cases x)
    obtain s where st_eq: "st = StateII s"
      by (cases st, simp add: StateII_def)
    obtain ac where cs_eq: "cs = \<lparr>ac\<^sub>v = ac, \<dots> = ()\<rparr>"
      by (cases cs, simp)
    show "(pre_A \<longrightarrow> p2ac_exist (\<not> ac2p_rel (\<not> pre_A))) x"
      unfolding impl_pred_def
    proof
      assume pre: "pre_A x"
      have pre_empty:
          "pre_A (StateII s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>)"
        using pre_A_downward[of "{}" ac "StateII s"] pre
        by (simp add: x_eq st_eq cs_eq)
      obtain z where pre_singleton:
          "pre_A (StateII s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>)"
        using singleton_supported_A[rule_format, of "StateII s"] pre_empty
        by blast
      have not_failure: "\<not> ac2p_rel (\<not> pre_A) (s, z)"
        using pre_A_downward[of _ "{z}" "StateII s"] pre_singleton
        by (simp only: ac2p_rel_subset; pred_auto; blast)
      show "p2ac_exist (\<not> ac2p_rel (\<not> pre_A)) x"
        unfolding p2ac_exist_def
        using not_failure x_eq st_eq cs_eq
        by (pred_auto; blast)
    qed
  qed
  have post_A_healthy: "PBMH post_A = post_A"
    by (simp add: post_A_def PBMH_conj_nonempty)
  from d2ac_ac2p_rdesign_refine[OF failure_healthy post_A_healthy feasible]
  show ?thesis
    by (simp only: P_form)
qed

end
