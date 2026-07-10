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

lemma p2ac_disj:
  "p2ac (P \<or> Q) = (p2ac P \<or> p2ac Q)"
  by (pred_auto)

lemma p2ac_conj_refine:
  "(p2ac P \<and> p2ac Q) \<sqsubseteq> p2ac (P \<and> Q)"
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

end
