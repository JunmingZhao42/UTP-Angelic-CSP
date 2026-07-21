section \<open>From Designs to Angelic Designs\<close>

theory utp_ades_designs
  imports utp_ades_healthy
begin

subsection \<open>Predicate Mapping\<close>

(* Paper Definition 23. *)
definition p2ac :: "'s des_hrel \<Rightarrow> 's angelic_design" where
[pred]: "p2ac P = (\<lambda> (s0, ac').
  \<exists> z \<in> achoices.ac\<^sub>v (des_vars.more ac').
    P (\<lparr>ok\<^sub>v = ok\<^sub>v s0,
         \<dots> = astate.s\<^sub>v (des_vars.more s0)\<rparr>,
       \<lparr>ok\<^sub>v = ok\<^sub>v ac', \<dots> = z\<rparr>))"

(* Relation-level specialisation via design lifting. *)
definition p2ac_rel :: "('s, 's) urel \<Rightarrow> 's angelic_rel" where
"p2ac_rel P = \<lfloor>p2ac (\<lceil>P\<rceil>\<^sub>D)\<rfloor>\<^sub>D"

lemma p2ac_rel_alt [pred]:
  "p2ac_rel P = (\<lambda> (s0, ac').
    \<exists> z \<in> achoices.ac\<^sub>v ac'. P (astate.s\<^sub>v s0, z))"
  by (simp add: p2ac_rel_def p2ac_def; pred_auto)

lemma p2ac_lift [simp]:
  "p2ac (\<lceil>P\<rceil>\<^sub>D) = \<lceil>p2ac_rel P\<rceil>\<^sub>D"
  by (simp add: p2ac_rel_def p2ac_def; pred_auto)

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
  "p2ac true = ac_non_empty"
  by (simp add: ac_non_empty_def, pred_auto)

(* Thesis Theorem T.4.6.1. *)
lemma p2ac_disj:
  "p2ac (P \<or> Q) = (p2ac P \<or> p2ac Q)"
  by (pred_auto)

(* Thesis Theorem T.4.6.2. *)
lemma p2ac_conj:
  "p2ac (P \<and> Q) x \<longrightarrow> (p2ac P \<and> p2ac Q) x"
  by (pred_auto)

lemma p2ac_rel_false [simp]:
  "p2ac_rel false = false"
  by (pred_auto)

lemma p2ac_rel_true [simp]:
  "p2ac_rel true = (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
  by (pred_auto)

lemma p2ac_rel_disj:
  "p2ac_rel (P \<or> Q) = (p2ac_rel P \<or> p2ac_rel Q)"
  by (pred_auto)

lemma p2ac_rel_conj:
  "p2ac_rel (P \<and> Q) x \<longrightarrow> (p2ac_rel P \<and> p2ac_rel Q) x"
  by (pred_auto)

(* Paper Theorem 72 *)
lemma p2ac_design:
  "(ac_non_empty \<and> p2ac ((\<not> P) \<turnstile>\<^sub>r Q)) =
   (ac_non_empty \<and> ((\<not> p2ac_rel P) \<turnstile>\<^sub>r p2ac_rel Q))"
  by (simp add: ac_non_empty_def p2ac_rel_alt
      rdesign_refinement; pred_auto)

lemma PBMH_p2ac_rel [simp]:
  "PBMH (p2ac_rel P) = p2ac_rel P"
  by (pred_auto)

(* Thesis Theorem T.4.6.3, in relational form. *)
lemma A2_rel_p2ac_rel [simp]:
  "A2_rel (p2ac_rel P) = p2ac_rel P"
  by (simp add: A2_rel_eq_expanded, pred_auto)

subsection \<open>Design to Angelic Design\<close>

(* Paper Definition 21. *)
definition d2ac :: "'s des_hrel \<Rightarrow> 's angelic_design" where
[pred]: "d2ac P =
  ((\<not> p2ac_rel (\<not> pre\<^sub>D P) \<and> p2ac_exist (pre\<^sub>D P))
    \<turnstile>\<^sub>r p2ac_rel (post\<^sub>D P))"

(* \<forall>z\<in>A. P(s, z)) \<and> (\<exists>z. P(s, z)) \<turnstile>\<^sub>r \<exists>z\<in>A. Q(s, z) *)
lemma d2ac_rdesign:
  "d2ac (P \<turnstile>\<^sub>r Q) =
   ((\<not> p2ac_rel (\<not> P) \<and> p2ac_exist P) \<turnstile>\<^sub>r p2ac_rel Q)"
  by (simp add: d2ac_def, pred_auto)

lemma d2ac_A0 [simp]:
  "A0 (d2ac P) = d2ac P"
  by (simp add: A0_def d2ac_def, pred_auto)

lemma d2ac_A1 [simp]:
  "A1 (d2ac P) = d2ac P"
  by (simp add: A1_def d2ac_def, pred_auto)

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

(* Paper Appendix A.3, Lemma 26 *)
lemma PBMH_ades_p2ac [simp]:
  "PBMH_ades (p2ac P) = p2ac P"
  by (simp add: PBMH_ades_def p2ac_def fun_eq_iff; pred_auto)

lemma PBMH_ades_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> PBMH_ades P \<sqsubseteq> PBMH_ades Q"
  by (simp add: PBMH_ades_def; pred_auto; blast)

lemma PBMH_ades_Monotonic [closure]: "Monotonic PBMH_ades"
  by (rule MonotonicI, rule PBMH_ades_mono)

lemma PBMH_ades_idem:
  "PBMH_ades (PBMH_ades P) = PBMH_ades P"
  by (simp add: PBMH_ades_def fun_eq_iff PBMH_idem)

lemma PBMH_ades_Idempotent [closure]: "Idempotent PBMH_ades"
  by (simp add: Idempotent_def PBMH_ades_idem)

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
  using A1_PBMH_ades_rdesign[of "pre\<^sub>D P" "post\<^sub>D P"]
    H1_H2_eq_rdesign[of P] assms
  by (simp add: Healthy_def')

(* Paper Definition 24. *)
definition ac2p :: "'s angelic_design \<Rightarrow> 's des_hrel" where
[pred]: "ac2p P = (\<lambda> (s0, s1).
  let ades_in = \<lparr>ok\<^sub>v = ok\<^sub>v s0,
                   \<dots> = StateII (des_vars.more s0)\<rparr>;
      ades_out = \<lparr>ok\<^sub>v = ok\<^sub>v s1,
                    \<dots> = \<lparr>ac\<^sub>v = {des_vars.more s1}, \<dots> = ()\<rparr>\<rparr>
  in PBMH_ades P (ades_in, ades_out))"

(* Paper Lemma 25 *)
lemma ac2p_PBMH_ades [simp]:
  "ac2p (PBMH_ades P) = ac2p P"
  by (simp add: ac2p_def PBMH_ades_def fun_eq_iff PBMH_idem)

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
  "ac2p_rel P = (\<lambda> (s0, s1). \<exists> A.
    P (StateII s0, \<lparr>ac\<^sub>v = A, \<dots> = ()\<rparr>) \<and> A \<subseteq> {s1})"
  by (pred_auto)

(* Paper Lemma 4. ac2p(P)(s,z) = \<exists> ac. P(s, ac) \<and> \<forall>y \<in> ac. y = z *)
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

(* Paper Lemma 24 (aka L.C.5.28) *)
lemma ac2p_design:
  assumes "P is \<^bold>H"
  shows "ac2p P = ((\<not> ac2p (P\<^sup>f)) \<turnstile> ac2p (P\<^sup>t))"
  by (subst (1) Healthy_if[OF assms, symmetric];
      simp only: H1_H2_eq_design design_def ac2p_subset;
      pred_auto)
  
subsection \<open>Isomorphism and Galois Connection\<close>

lemma ac2p_d2ac_rdesign:
  "(ac2p \<circ> d2ac) (P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
  by (simp only: comp_apply d2ac_rdesign ac2p_subset; pred_auto)

(* Paper Theorem 5. *)
theorem ac2p_d2ac:
  assumes "P is \<^bold>H"
  shows "(ac2p \<circ> d2ac) P = P"
  using ac2p_d2ac_rdesign[of "pre\<^sub>D P" "post\<^sub>D P"]
    H1_H2_eq_rdesign[of P] assms
  by (simp add: Healthy_def' comp_apply)

(* Thesis Theorem T.5.3.6, specialised to the relation-level mapping. *)
lemma p2ac_ac2p_rel_refine:
  assumes "PBMH P = P"
  shows "P \<sqsubseteq> (p2ac_rel \<circ> ac2p_rel) P"
  using assms
  by (simp only: comp_apply ac2p_rel_subset p2ac_rel_alt; pred_auto)

lemma d2ac_ac2p_rdesign_refine:
  assumes "PBMH (\<not> P) = (\<not> P)" "PBMH Q = Q"
    and feasible: "taut (P \<longrightarrow> p2ac_exist (\<not> ac2p_rel (\<not> P)))"
  shows "(P \<turnstile>\<^sub>r Q) \<sqsubseteq>
    (d2ac \<circ> ac2p) (P \<turnstile>\<^sub>r Q)"
  apply (simp only: comp_apply ac2p_rdesign d2ac_rdesign)
  apply (rule rdesign_refine_intro)
   apply (insert p2ac_ac2p_rel_refine[OF assms(1)] feasible)
   apply (pred_auto)
  apply (insert p2ac_ac2p_rel_refine[OF assms(2)])
  by (pred_auto)

(* The A0-A2 rdesign form is preserved by the round trip up to refinement. *)
lemma d2ac_ac2p_A2_rdesign_refine:
  fixes P Q :: "'s angelic_rel"
  shows "(d2ac \<circ> ac2p) ((\<not> A2_rel (\<not> P)) \<turnstile>\<^sub>r
      A2_rel (Q \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))
    \<sqsubseteq> ((\<not> A2_rel (\<not> P)) \<turnstile>\<^sub>r
      A2_rel (Q \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
proof -
  have round_trip: "(p2ac_rel \<circ> ac2p_rel) R =
      (A2_rel R \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
    for R :: "'s angelic_rel"
    apply (simp only: comp_apply p2ac_rel_alt ac2p_rel_subset A2_rel_eq_expanded
        A2_rel_expanded_def)
    apply (pred_auto)
    apply (drule subset_singletonD)
    by (elim disjE; simp)
  show ?thesis
    apply (simp only: comp_apply ac2p_rdesign d2ac_rdesign round_trip
        A2_rel_idem)
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
  have "$ac\<^sup>> \<sharp> pre\<^sub>D P_dummy"
    by (rule unrest_out_var;
        simp add: H3_unrest_out_alpha[OF normal])
  then show False
    by (simp add: P_dummy_def unrest unrest_lens; pred_auto)
qed

lemma ac2p_P_dummy:
  "ac2p P_dummy = (false \<turnstile>\<^sub>r true)"
  unfolding P_dummy_def
  apply (simp only: ac2p_rdesign ac2p_rel_subset)
  by (pred_auto)

lemma p2ac_exist_false:
  "p2ac_exist false = false"
  by (pred_auto)

lemma d2ac_bot:
  "d2ac (false \<turnstile>\<^sub>r true) = \<bottom>\<^sub>D"
  apply (simp add:d2ac_rdesign p2ac_exist_false)
  by (pred_auto)

lemma d2ac_ac2p_P_dummy:
  "(d2ac \<circ> ac2p) P_dummy = true"
  apply (simp only: comp_apply ac2p_P_dummy d2ac_rdesign
      p2ac_rel_false p2ac_rel_true
      p2ac_exist_def)
  by (pred_auto)

lemma P_dummy_fails_theorem6:
  "\<not> (P_dummy \<sqsubseteq> (d2ac \<circ> ac2p) P_dummy)"
  apply (simp only: d2ac_ac2p_P_dummy P_dummy_def)
  by (pred_auto)

(* What does P_dummy mean? *)
lemma "P_dummy = (($ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e \<turnstile>\<^sub>r false)"
  by pred_auto

lemma "ac2p_rel (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e) = true"
  unfolding ac2p_rel_def by pred_auto

definition pre_singleton_witness :: "'s angelic_design \<Rightarrow> bool" where
"pre_singleton_witness P \<longleftrightarrow>
  (\<forall>s. pre\<^sub>D P (s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<longrightarrow>
    (\<exists>z. pre\<^sub>D P (s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>)))"

(* In which cases does this work? *)
lemma "pre_singleton_witness (($ac\<^sup>> = \<guillemotleft>{}\<guillemotright> \<or> $ac\<^sup>> = \<guillemotleft>{z}\<guillemotright>)\<^sub>e \<turnstile>\<^sub>r Q)"
  unfolding pre_singleton_witness_def by pred_auto

lemma "($ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e ;;\<^sub>A true = false"
  by pred_auto

lemma "(P ;;\<^sub>A ($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e) = P"
  by pred_auto

lemma aseq_false: "P\<lbrakk>{}/ac\<^sup>>\<rbrakk> = P ;;\<^sub>A false"
  by pred_auto

text \<open> Below, some attempts at re-expressing the same condition using relational refinement. \<close>

lemma "pre_singleton_witness (P \<turnstile>\<^sub>r Q) \<longleftrightarrow> (P ;;\<^sub>A false \<sqsupseteq> (\<exists>z. P\<lbrakk>{z}/ac\<^sup>>\<rbrakk>)\<^sub>e)"
  unfolding pre_singleton_witness_def by pred_auto

lemma "pre_singleton_witness (P \<turnstile>\<^sub>r Q) \<longleftrightarrow> ((P ;;\<^sub>A false) \<sqsupseteq> (P ;; (\<exists>z. $ac\<^sup>< = {z})\<^sub>e))"
  unfolding pre_singleton_witness_def by pred_auto

lemma "pre_singleton_witness (P \<turnstile>\<^sub>r Q) \<longrightarrow> ((P ;;\<^sub>A false) \<sqsupseteq> (\<exists>ac\<^sup>> \<Zspot> P ;;\<^sub>A ($ac\<^sup>> \<noteq> {})\<^sub>e))"
  unfolding pre_singleton_witness_def by pred_auto

lemma "pre_singleton_witness (P \<turnstile>\<^sub>r Q) \<longrightarrow> ((P ;;\<^sub>A false) \<sqsupseteq> (\<exists>ac\<^sup>> \<Zspot> P ;;\<^sub>A ({$s\<^sup><} = $ac\<^sup>>)\<^sub>e))"
  unfolding pre_singleton_witness_def apply pred_auto
  by (metis (mono_tags, lifting) Collect_empty_eq singleton_conv)

(* Q: Is pre_singleton_witness the weakest predicate required to uphold the theorem? *)

(* Paper Theorem 6, with the missing singleton-witness premise. *)
lemma d2ac_ac2p:
  fixes P :: "'s angelic_design"
  assumes healthy: "P is A"
    and witness_exists: "pre_singleton_witness P"
  shows "P \<sqsubseteq> (d2ac \<circ> ac2p) P"
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
  have witness_exists_A:
      "\<forall>s. pre_A (s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<longrightarrow>
        (\<exists>z. pre_A (s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>))"
    using witness_exists by (simp add: pre_singleton_witness_def pre_A_eq)
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
    apply (rule tautI)
    apply (simp only: impl_pred_def p2ac_exist_def ac2p_rel_subset)
    apply (pred_auto)
    subgoal for s ac
      apply (frule pre_A_downward[OF empty_subsetI])
      apply (drule witness_exists_A[THEN spec, THEN mp])
      apply (elim exE)
      subgoal for z
        apply (rule exI[where x=z])
        apply (rule allI)
        subgoal for X
          apply (cases "X \<subseteq> {z}")
           apply (rule disjI1)
           apply (rule pre_A_downward; assumption)
          by (rule disjI2; assumption)
        done
      done
    done
  have post_A_healthy: "PBMH post_A = post_A"
    by (simp add: post_A_def PBMH_conj_nonempty)
  from d2ac_ac2p_rdesign_refine[OF failure_healthy post_A_healthy feasible]
  show ?thesis
    by (simp only: P_form)
qed

(* Paper Theorem 7. *)
lemma d2ac_ac2p_A2:
  fixes P :: "'s angelic_design"
  assumes healthy: "P is A"
    and a2_healthy: "P is A2"
  shows "(d2ac \<circ> ac2p) P \<sqsubseteq> P"
proof -
  define Pre :: "'s angelic_rel" where
    "Pre \<equiv> \<not> PBMH (\<not> pre\<^sub>D P)"
  define Post :: "'s angelic_rel" where
    "Post \<equiv> PBMH (post\<^sub>D P)"
  have P_form: "P = (Pre \<turnstile>\<^sub>r
      (Post \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
    using A_healthy_design_form[OF healthy]
    by (simp add: Pre_def Post_def)
  from d2ac_ac2p_A2_rdesign_refine[of Pre Post] a2_healthy
  show ?thesis
    by (simp only: Healthy_def' P_form A2_rdesign)
qed

(* Paper Theorem 8, with the corrected premise from Theorem 6. *)
lemma d2ac_ac2p_A2_eq:
  fixes P :: "'s angelic_design"
  assumes healthy: "P is A"
    and a2_healthy: "P is A2"
    and witness_exists: "pre_singleton_witness P"
  shows "(d2ac \<circ> ac2p) P = P"
  apply (rule ref_antisym)
   apply (rule d2ac_ac2p[OF healthy witness_exists])
  by (rule d2ac_ac2p_A2[OF healthy a2_healthy])

end
