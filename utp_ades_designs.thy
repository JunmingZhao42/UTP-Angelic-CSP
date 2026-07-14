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
  apply (pred_auto; blast)
  done

subsection \<open>Angelic Design to Design\<close>

(* Apply PBMH to the nested angelic-choice output while carrying ok' unchanged. *)
definition PBMH_ades :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "PBMH_ades P = (\<lambda> (s0, s1).
  let ac' = get\<^bsub>\<^bold>v\<^sub>D\<^esub> s1
  in PBMH (\<lambda> (s, ac). let s1' = put\<^bsub>\<^bold>v\<^sub>D\<^esub> s1 ac
    in P (s, s1')) (s0, ac'))"

(* Paper Definition 24; thesis Definition 103. The two records implement
   StateII on the input and dash on the output. *)
definition ac2p :: "'s angelic_design \<Rightarrow> 's des_hrel" where
[pred]: "ac2p P = (\<lambda> (s0, s1).
  let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                   \<dots> = StateII (des_vars.more s0)\<rparr>;
      ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                    \<dots> = \<lparr>ac\<^sub>v = {des_vars.more s1}, \<dots> = ()\<rparr>\<rparr>
  in PBMH_ades P (ades_in, ades_out))"

(* Thesis Appendix C.5.3, Lemma L.C.5.20 (ac2p-alternative-3). *)
lemma ac2p_subset:
  "ac2p P = (\<lambda> (s0, s1). \<exists> ac.
    let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                     \<dots> = StateII (des_vars.more s0)\<rparr>;
        ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                      \<dots> = \<lparr>ac\<^sub>v = ac, \<dots> = ()\<rparr>\<rparr>
    in P (ades_in, ades_out) \<and> ac \<subseteq> {des_vars.more s1})"
  by (pred_auto)

(* Thesis Lemma L.4.6.2 (ac2p-alternative-1). *)
lemma ac2p_alt:
  "ac2p P = (\<lambda> (s0, s1). \<exists> ac.
    let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                     \<dots> = StateII (des_vars.more s0)\<rparr>;
        ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                      \<dots> = \<lparr>ac\<^sub>v = ac, \<dots> = ()\<rparr>\<rparr>
    in P (ades_in, ades_out) \<and> (\<forall> z \<in> ac. z = des_vars.more s1))"
  by (pred_auto)

subsection \<open>Isomorphism and Galois Connection\<close>

lemma ac2p_d2ac_rdesign:
  fixes P Q :: "('s, 's) urel"
  shows "ac2p (d2ac (P \<turnstile>\<^sub>r Q)) = (P \<turnstile>\<^sub>r Q)"
  apply (simp only: d2ac_rdesign ac2p_subset)
  apply (pred_simp)
  apply (auto)
  done

(* Paper Theorem 5; thesis Theorem T.4.6.7. *)
theorem ac2p_d2ac:
  fixes P :: "'s des_hrel"
  assumes "P is \<^bold>H"
  shows "ac2p (d2ac P) = P"
proof -
  have P_form: "P = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    using assms by (metis H1_H2_eq_rdesign Healthy_def')
  have "ac2p (d2ac P) =
      ac2p (d2ac (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P))"
    by (rule arg_cong[OF P_form])
  also have "... = (pre\<^sub>D P \<turnstile>\<^sub>r post\<^sub>D P)"
    by (rule ac2p_d2ac_rdesign)
  also have "... = P"
    using P_form by (rule sym)
  finally show ?thesis .
qed

end
