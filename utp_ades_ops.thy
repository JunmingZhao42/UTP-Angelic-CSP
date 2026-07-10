section \<open>Angelic Design Operators\<close>

theory utp_ades_ops
  imports utp_ades_core
begin

subsection \<open>Assignment\<close>

(* Definition 94. The assigned state is one available angelic choice. *)
definition assign_arel :: 
  "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "assign_arel x e = (\<lambda> (s0, ac').
  put\<^bsub>x\<^esub> (get\<^bsub>s\<^esub> s0) (e (get\<^bsub>s\<^esub> s0)) \<in> get\<^bsub>ac\<^esub> ac')"

definition assigns_ades :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's angelic_design" where
[pred]: "assigns_ades x e = arel_to_ades (assign_arel x e)"

syntax
  "_assignment_ades" :: "svid \<Rightarrow> logic \<Rightarrow> logic"  (infixr ":=\<^sub>D\<^sub>A" 62)

translations
  "_assignment_ades x e" == "CONST assigns_ades x (e)\<^sub>e"
  "_assignment_ades (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_assignment_ades (x +\<^sub>L y) e"

subsection \<open>Demonic Choice\<close>

abbreviation dchoice_ades :: "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design" (infixl "\<sqinter>\<^sub>D\<^sub>A" 65)
where "P \<sqinter>\<^sub>D\<^sub>A Q \<equiv> P \<sqinter> Q"

lemma adem_choice_def:
  fixes P Q :: "('s, '\<alpha>, '\<beta>) angelic_rel_ext"
  shows "P \<sqinter> Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

lemma dchoice_ades_form:
  fixes P Q :: "'s angelic_design"
  shows "P \<sqinter>\<^sub>D\<^sub>A Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

subsection \<open>Angelic Choice\<close>

abbreviation achoice_ades :: "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design" (infixl "\<squnion>\<^sub>D\<^sub>A" 70)
where "P \<squnion>\<^sub>D\<^sub>A Q \<equiv> P \<squnion> Q"

lemma aang_choice_def:
  fixes P Q :: "('s, '\<alpha>, '\<beta>) angelic_rel_ext"
  shows "P \<squnion> Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

lemma achoice_ades_form:
  fixes P Q :: "'s angelic_design"
  shows "P \<squnion>\<^sub>D\<^sub>A Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

subsection \<open>Angelic Relation Sequential Composition\<close>

(* Definition 19. *)
definition aseq ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext" (infixl ";;\<^sub>A" 75)
where
(* P(s0, ac'[ac := {s1 | Q(s0[s := s1], ac')}]) *)
[pred]: "P ;;\<^sub>A Q = (\<lambda> (s0, ac').
  P (s0, put\<^bsub>ac\<^esub> ac' {s1. Q (put\<^bsub>s\<^esub> s0 s1, ac')}))"

lemma aseq_true_left [simp]:
  "true ;;\<^sub>A P = true"
  by (pred_auto)

lemma aseq_false_left [simp]:
  "false ;;\<^sub>A P = false"
  by (pred_auto)

(* (s \<in> ac') ;; P = P *)
lemma aseq_state_choice_left [simp]:
  "(($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e ;;\<^sub>A P) = P"
  by (pred_auto)

lemma aseq_true_right_unrest [simp]:
  assumes "$ac\<^sup>> \<sharp> P"
  shows "P ;;\<^sub>A true = P"
  using assms by (pred_auto assms: assms)

subsection \<open>Angelic Design Sequential Composition\<close>

(* Definition 18: compose angelic designs through a hidden intermediate ok value. *)
definition angelic_design_seq_paper ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
where
[pred]: "angelic_design_seq_paper P Q = (\<lambda> (s0, ac'). \<exists> ok0.
  P (s0, put\<^bsub>ok\<^esub> (put\<^bsub>\<^bold>v\<^sub>D\<^esub> ac' (put\<^bsub>ac\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> ac')
    {s1. Q (put\<^bsub>ok\<^esub> (put\<^bsub>\<^bold>v\<^sub>D\<^esub> s0 (put\<^bsub>s\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> s0) s1)) ok0, ac')})) ok0))"

(* Thesis Theorem T.4.5.1: proof-friendly pre/postcondition form. *)
definition angelic_design_seq_t451 ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
where
[pred]: "angelic_design_seq_t451 P Q =
  ((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true) \<and> \<not> (post\<^sub>D P ;;\<^sub>A (\<not> pre\<^sub>D Q)))
   \<turnstile>\<^sub>r
   (post\<^sub>D P ;;\<^sub>A (pre\<^sub>D Q \<longrightarrow> post\<^sub>D Q)))"

abbreviation angelic_design_seq ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design" (infixl ";;\<^sub>D\<^sub>A" 75)
where "angelic_design_seq \<equiv> angelic_design_seq_t451"

abbreviation dseq_ades ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
where "dseq_ades \<equiv> angelic_design_seq_t451"

text \<open>
  TODO: prove that @{const angelic_design_seq_paper} is equivalent to
  @{const angelic_design_seq_t451} under the side conditions of thesis
  Theorem T.4.5.1.
\<close>

(* Thesis Theorem T.4.5.2: simplified form when the left precondition
   does not depend on the final angelic choices. *)
lemma angelic_design_seq_simple_form:
  assumes "$ac\<^sup>> \<sharp> pre\<^sub>D P"
  shows "P ;;\<^sub>D\<^sub>A Q =
  ((pre\<^sub>D P \<and> \<not> (post\<^sub>D P ;;\<^sub>A (\<not> pre\<^sub>D Q)))
   \<turnstile>\<^sub>r
   (post\<^sub>D P ;;\<^sub>A (pre\<^sub>D Q \<longrightarrow> post\<^sub>D Q)))"
  using assms
  by (simp add: angelic_design_seq_t451_def unrest)

end
