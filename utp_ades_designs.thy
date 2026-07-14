section \<open>From Designs to Angelic Designs\<close>

theory utp_ades_designs
  imports utp_ades_healthy
begin

subsection \<open>Predicate Mapping\<close>

(* Paper Definition 23; thesis Definition 102.
   p2ac(P)(s, A) = \<exists>z\<in>A. P(s, z) *)
definition p2ac :: "('s, 's) urel \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "p2ac P = (\<lambda> (s0, ac').
  \<exists> z \<in> get\<^bsub>ac\<^esub> ac'. P (get\<^bsub>s\<^esub> s0, z))"

(* The second conjunction of the d2ac pre-condition:
  \<not>P^f [s/in\<alpha>_ok]; true \<equiv> \<exists>z. P(s, z) *)
definition p2ac_exist :: "('s, 's) urel \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "p2ac_exist P = (\<lambda> (s0, ac').
  \<exists> z. P (get\<^bsub>s\<^esub> s0, z))"

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

(* Paper Appendix A.3, Lemma 26; thesis Lemma L.4.6.1. *)
lemma PBMH_p2ac [simp]:
  "PBMH (p2ac P) = p2ac P"
  by (pred_auto)

(* Thesis Theorem T.4.6.3, in relational form. *)
lemma A2_rel_p2ac [simp]:
  "A2_rel (p2ac P) = p2ac P"
  by (simp add: A2_rel_eq_expanded, pred_auto)

subsection \<open>Design to Angelic Design\<close>

(* Definition 21. *)
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
  let ac' = get\<^bsub>\<^bold>v\<^sub>D\<^esub> s1
  in PBMH (\<lambda> (s, ac). let s1' = put\<^bsub>\<^bold>v\<^sub>D\<^esub> s1 ac
    in P (s, s1')) (s0, ac'))"

(* Definition 24. *)
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

(* Lemma 4. ac2p(P)(s,z) = \<exists> ac. P(s, ac) ∧ \<forall>y \<in> ac. y = z *)
(* My understanding: ac2p(P)(s,z) = P(s, {z}) *)
lemma ac2p_alt:
  "ac2p P = (\<lambda> (s0, s1). \<exists> ac.
    let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                     \<dots> = StateII (des_vars.more s0)\<rparr>;
        ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                      \<dots> = \<lparr>ac\<^sub>v = ac, \<dots> = ()\<rparr>\<rparr>
    in P (ades_in, ades_out) \<and> (\<forall> z \<in> ac. z = des_vars.more s1))"
  by (pred_auto)

lemma ac2p_rdesign:
  "ac2p (P \<turnstile>\<^sub>r Q) = ((\<not> ac2p_rel (\<not> P)) \<turnstile>\<^sub>r ac2p_rel Q)"
  by (simp only: ac2p_subset ac2p_rel_subset; pred_auto)
  
subsection \<open>Isomorphism and Galois Connection\<close>

lemma ac2p_d2ac_rdesign:
  "ac2p (d2ac (P \<turnstile>\<^sub>r Q)) = (P \<turnstile>\<^sub>r Q)"
  by (simp only: d2ac_rdesign ac2p_subset; pred_auto)

(* Theorem 5 *)
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

(* thesis Theorem T.4.6.8.
   Normality makes the precondition independent of the output choice ac'. *)
lemma d2ac_ac2p_normal:
  fixes D :: "'s angelic_design"
  defines "P \<equiv> \<not> PBMH (\<not> pre\<^sub>D D)"
    and "Q \<equiv> PBMH (post\<^sub>D D) \<and>
      ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"
  assumes healthy: "D is A"
    and normal: "D is \<^bold>N"
  shows "D \<sqsubseteq> d2ac (ac2p D)"
proof -
  have pre_unrest: "$ac\<^sup>> \<sharp> pre\<^sub>D D"
    by (rule unrest_out_var; simp add: H3_unrest_out_alpha[OF normal])
  have P_eq: "P = pre\<^sub>D D"
    using PBMH_unrest_ac[of "\<not> pre\<^sub>D D"] pre_unrest
    by (simp add: P_def unrest)
  have failure_P_unrest: "$ac\<^sup>> \<sharp> (\<not> P)"
    using pre_unrest by (simp add: P_eq unrest)
  have feasible: "taut (P \<longrightarrow> p2ac_exist (\<not> ac2p_rel (\<not> P)))"
    using ac2p_rel_feasible_unrest[OF failure_P_unrest] by simp
  have failure_healthy: "PBMH (\<not> P) = (\<not> P)"
    by (rule PBMH_unrest_ac[OF failure_P_unrest])
  have Q_healthy: "PBMH Q = Q"
    by (simp add: Q_def PBMH_conj_nonempty)
  have D_form: "D = (P \<turnstile>\<^sub>r Q)"
    using A_healthy_design_form[OF healthy]
    by (simp add: P_def Q_def)
  from d2ac_ac2p_rdesign_refine[
    OF failure_healthy Q_healthy feasible]
  show ?thesis
    by (simp only: D_form)
qed

(* Theorem 6. But with normal designs only *)
corollary d2ac_ac2p_ndesign:
  fixes p :: "'s astate pred"
    and Q :: "'s angelic_rel"
  assumes "(p \<turnstile>\<^sub>n Q) is A"
  shows "(p \<turnstile>\<^sub>n Q) \<sqsubseteq> d2ac (ac2p (p \<turnstile>\<^sub>n Q))"
  by (rule d2ac_ac2p_normal[OF assms ndesign_H1_H3])

end
