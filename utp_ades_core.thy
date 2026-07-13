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
type_synonym ('s, '\<alpha>, '\<beta>) angelic_rel_ext =
  "(('s, '\<alpha>) astate_ext, ('s, '\<beta>) achoices_ext) urel"
type_synonym ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext =
  "(('s, '\<alpha>) astate_ext, ('s, '\<beta>) achoices_ext) des_rel"

type_synonym 's angelic_rel = "('s, unit, unit) angelic_rel_ext"
type_synonym 's angelic_design_rel = "('s, unit, unit) angelic_design_rel_ext"
type_synonym 's angelic_design = "'s angelic_design_rel"

type_synonym ('s, '\<alpha>, '\<beta>) arel_ext = "('s, '\<alpha>, '\<beta>) angelic_rel_ext"
type_synonym ('s, '\<alpha>, '\<beta>) ades_rel_ext = "('s, '\<alpha>, '\<beta>) angelic_design_rel_ext"
type_synonym 's arel = "'s angelic_rel"
type_synonym 's ades_rel = "'s angelic_design_rel"
type_synonym 's ades = "'s angelic_design"

abbreviation arel_state_subst ::
  "('s, '\<alpha>) astate_ext subst \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext"
where
  "arel_state_subst st_subst P \<equiv> (st_subst \<up>\<^sub>s \<^bold>v\<^sup><) \<dagger> P"

abbreviation ades_state_subst ::
  "('s, '\<alpha>) astate_ext subst \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext"
where
  "ades_state_subst st_subst P \<equiv> (st_subst \<up>\<^sub>s \<^bold>v\<^sub>D\<^sup><) \<dagger> P"

definition arel_to_ades ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext"
where
[pred]: "arel_to_ades P = (true \<turnstile>\<^sub>r P)"

text \<open>
  For example, @{term "arel_to_ades (($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e) :: 's angelic_design"}.
\<close>

end
