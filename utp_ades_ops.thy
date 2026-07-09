section \<open>Angelic Design Operators\<close>

theory utp_ades_ops
  imports utp_ades_core
begin

subsection \<open>Demonic Choice\<close>

abbreviation dchoice_ades :: "'s ades \<Rightarrow> 's ades \<Rightarrow> 's ades" (infixl "\<sqinter>\<^sub>D\<^sub>A" 65)
where "P \<sqinter>\<^sub>D\<^sub>A Q \<equiv> P \<sqinter> Q"

lemma adem_choice_def:
  fixes P Q :: "(('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel"
  shows "P \<sqinter> Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

lemma dchoice_ades_form:
  fixes P Q :: "'s ades"
  shows "P \<sqinter>\<^sub>D\<^sub>A Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

subsection \<open>Angelic Choice\<close>

abbreviation achoice_ades :: "'s ades \<Rightarrow> 's ades \<Rightarrow> 's ades" (infixl "\<squnion>\<^sub>D\<^sub>A" 70)
where "P \<squnion>\<^sub>D\<^sub>A Q \<equiv> P \<squnion> Q"

lemma aang_choice_def:
  fixes P Q :: "(('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel"
  shows "P \<squnion> Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

lemma achoice_ades_form:
  fixes P Q :: "'s ades"
  shows "P \<squnion>\<^sub>D\<^sub>A Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

subsection \<open>Angelic Sequential Composition\<close>

(* Definition 19. *)
definition aseq ::
  "(('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel \<Rightarrow>
   (('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel \<Rightarrow>
   (('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel" (infixl ";;\<^sub>A" 75)
where
(* P(s0, ac'[ac := {s1 | Q(s0[s := s1], ac')}]) *)
[pred]: "P ;;\<^sub>A Q = (\<lambda> (s\<^sub>0, ac').
  P (s\<^sub>0, put\<^bsub>ac\<^esub> ac' {s\<^sub>1. Q (put\<^bsub>s\<^esub> s\<^sub>0 s\<^sub>1, ac')}))"

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

subsection \<open>Angelic Design Sequential Composition (Definition 18)\<close>

definition dseq_ades :: "'s ades \<Rightarrow> 's ades \<Rightarrow> 's ades" (infixl ";;\<^sub>D\<^sub>A" 75)
where
[pred]: "P ;;\<^sub>D\<^sub>A Q =
  ((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true) \<and> \<not> (post\<^sub>D P ;;\<^sub>A (\<not> pre\<^sub>D Q)))
   \<turnstile>\<^sub>r
   (post\<^sub>D P ;;\<^sub>A (pre\<^sub>D Q \<longrightarrow> post\<^sub>D Q)))"

lemma dseq_ades_form:
  "P ;;\<^sub>D\<^sub>A Q =
  ((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true) \<and> \<not> (post\<^sub>D P ;;\<^sub>A (\<not> pre\<^sub>D Q)))
   \<turnstile>\<^sub>r
   (post\<^sub>D P ;;\<^sub>A (pre\<^sub>D Q \<longrightarrow> post\<^sub>D Q)))"
  by (simp add: dseq_ades_def)

end
