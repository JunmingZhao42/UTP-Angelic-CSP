section \<open>Angelic Design Core\<close>

theory utp_ades_core
  imports "UTP-Designs.utp_designs"
begin

subsection \<open>Alphabet (Definition 16)\<close>

text \<open>
  Angelic designs package ordinary program variables into an initial state @{term s}, 
  and record possible final states as a set @{term ac}.
\<close>

alphabet 's astate =
  s :: 's

alphabet 's achoices =
  ac :: "'s set"

notation achoices.more\<^sub>L ("\<^bold>v\<^sub>A")

syntax
  "_svid_ades_alpha" :: "svid" ("\<^bold>v\<^sub>A")

translations
  "_svid_ades_alpha" => "CONST achoices.more\<^sub>L"

type_synonym ('s, '\<alpha>) astate_ext       = "('s, '\<alpha>) astate_scheme"
type_synonym ('s, '\<alpha>) achoices_ext     = "('s, '\<alpha>) achoices_scheme"
type_synonym ('s, '\<alpha>, '\<beta>) ades_rel_ext =
  "(('s, '\<alpha>) astate_ext, ('s, '\<beta>) achoices_ext) des_rel"

type_synonym 's ades_rel = "('s, unit, unit) ades_rel_ext"
type_synonym 's ades     = "'s ades_rel"

text \<open>
  For example, @{term "(true \<turnstile>\<^sub>r ($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e) :: 's ades"}.
\<close>

subsection \<open>Angelic Sequential Composition (Definition 19)\<close>

text \<open>
  Angelic sequencing substitutes the final choice set of the first predicate with
  the set of intermediate states from which the second predicate can establish the
  final choice set.
\<close>

definition aseq ::
  "(('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel \<Rightarrow>
   (('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel \<Rightarrow>
   (('s, '\<alpha>) astate_scheme, ('s, '\<beta>) achoices_scheme) urel" (infixl ";;\<^sub>A" 75)
where
[pred]: "P ;;\<^sub>A Q = (\<lambda> (s\<^sub>0, ac\<^sub>F).
  P (s\<^sub>0, put\<^bsub>ac\<^esub> ac\<^sub>F {s\<^sub>1. Q (put\<^bsub>s\<^esub> s\<^sub>0 s\<^sub>1, ac\<^sub>F)}))"

lemma aseq_true_left [simp]:
  "true ;;\<^sub>A P = true"
  by (pred_auto)

lemma aseq_false_left [simp]:
  "false ;;\<^sub>A P = false"
  by (pred_auto)

lemma aseq_state_choice_left [simp]:
  "(($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e ;;\<^sub>A P) = P"
  by (pred_auto)

end
