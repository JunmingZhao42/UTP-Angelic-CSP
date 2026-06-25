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

end
