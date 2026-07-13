section \<open>From Designs to Angelic Designs\<close>

theory utp_ades_designs
  imports utp_ades_healthy
begin

subsection \<open>Predicate Mapping\<close>

(* Definition 23. *)
definition p2ac ::
  "('s, 's) urel \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext"
where
[pred]: "p2ac P = (\<lambda> (s0, ac').
  \<exists> z \<in> get\<^bsub>ac\<^esub> ac'. P (get\<^bsub>s\<^esub> s0, z))"

definition p2ac_feasible ::
  "('s, 's) urel \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext"
where
[pred]: "p2ac_feasible P = (\<lambda> (s0, ac').
  \<exists> z. P (get\<^bsub>s\<^esub> s0, z))"

lemma p2ac_false [simp]:
  "p2ac false = false"
  by (pred_auto)

lemma p2ac_true [simp]:
  "p2ac true = (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
  by (pred_auto)

lemma p2ac_feasible_false [simp]:
  "p2ac_feasible false = false"
  by (pred_auto)

lemma p2ac_feasible_true [simp]:
  "p2ac_feasible true = true"
  by (pred_auto)

lemma p2ac_disj:
  "p2ac (P \<or> Q) = (p2ac P \<or> p2ac Q)"
  by (pred_auto)

lemma p2ac_conj_refine:
  "(p2ac P \<and> p2ac Q) \<sqsubseteq> p2ac (P \<and> Q)"
  by (pred_auto)

lemma p2ac_implies_feasible:
  "p2ac_feasible P \<sqsubseteq> p2ac P"
  by (pred_auto)

lemma p2ac_feasible_disj:
  "p2ac_feasible (P \<or> Q) = (p2ac_feasible P \<or> p2ac_feasible Q)"
  by (pred_auto)

lemma p2ac_feasible_conj_refine:
  "(p2ac_feasible P \<and> p2ac_feasible Q) \<sqsubseteq> p2ac_feasible (P \<and> Q)"
  by (pred_auto)

lemma PBMH_p2ac [simp]:
  "PBMH (p2ac P) = p2ac P"
  by (pred_auto)

lemma PBMH_p2ac_feasible [simp]:
  "PBMH (p2ac_feasible P) = p2ac_feasible P"
  by (pred_auto)

lemma A2_rel_p2ac [simp]:
  "A2_rel (p2ac P) = p2ac P"
  by (simp add: A2_rel_eq_expanded, pred_auto)

lemma A2_rel_p2ac_feasible [simp]:
  "A2_rel (p2ac_feasible P) = p2ac_feasible P"
  by (simp add: A2_rel_eq_expanded, pred_auto)

subsection \<open>Design Mapping\<close>

(* Definition 21. *)
definition d2ac :: "'s des_hrel \<Rightarrow> 's angelic_design" where
[pred]: "d2ac P =
  ((\<not> p2ac (\<not> pre\<^sub>D P) \<and> p2ac_feasible (pre\<^sub>D P)) \<turnstile>\<^sub>r p2ac (post\<^sub>D P))"

lemma d2ac_rdesign:
  "d2ac (P \<turnstile>\<^sub>r Q) =
   ((\<not> p2ac (\<not> P) \<and> p2ac_feasible P) \<turnstile>\<^sub>r p2ac Q)"
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

end
