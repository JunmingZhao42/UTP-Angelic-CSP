section \<open>Angelic Design Core\<close>

theory utp_ades_core
  imports "UTP-Designs.utp_designs"
begin

subsection \<open>Alphabet (Paper Definition 16)\<close>

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

(* some shortcut to modify the angelic design fields *)
lemma astate_s_v_put [simp]:
  "astate.s\<^sub>v (put\<^bsub>s\<^esub> st v) = v"
  by (simp add: astate.s_def)

lemma achoices_ac_v_put [simp]:
  "achoices.ac\<^sub>v (put\<^bsub>ac\<^esub> c cs) = cs"
  by (simp add: achoices.ac_def)

(* Paper Definition 25. *)
(* Package the ordinary variables as the state observed by an angelic predicate. *)
definition StateII :: "'s \<Rightarrow> 's astate" where
[pred]: "StateII st = \<lparr>s\<^sub>v = st, \<dots> = ()\<rparr>"

type_synonym ('s, '\<alpha>) astate_ext       = "('s, '\<alpha>) astate_scheme"
type_synonym ('s, '\<alpha>) achoices_ext     = "('s, '\<alpha>) achoices_scheme"
type_synonym ('s, '\<alpha>, '\<beta>) angelic_rel_ext =
  "(('s, '\<alpha>) astate_ext, ('s, '\<beta>) achoices_ext) urel"
type_synonym ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext =
  "(('s, '\<alpha>) astate_ext, ('s, '\<beta>) achoices_ext) des_rel"

type_synonym 's angelic_rel = "('s, unit, unit) angelic_rel_ext"
type_synonym 's angelic_design = "('s, unit, unit) angelic_design_rel_ext"

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

subsection \<open>Design support laws\<close>

(* Negation reverses refinement.  Stated on opaque predicates: at the
   point of use the arguments are healthiness images, which pred_auto
   would otherwise unfold. *)
lemma not_refine:
  fixes P Q :: "'s pred"
  assumes "P \<sqsubseteq> Q"
  shows "(\<not> Q) \<sqsubseteq> (\<not> P)"
  using assms by pred_auto

subsection \<open>PBMH\<close>

(* ac \<subseteq> ac' \<and> v' = v. *)
definition pbmh_step :: "(('s, '\<alpha>) achoices_scheme, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "pbmh_step = (($ac\<^sup>< \<subseteq> $ac\<^sup>>) \<and> $\<^bold>v\<^sub>A\<^sup>> = $\<^bold>v\<^sub>A\<^sup><)\<^sub>e"

(* Paper Definition 15. *)
definition PBMH :: "('\<beta>, ('s, '\<alpha>) achoices_scheme) urel \<Rightarrow> ('\<beta>, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "PBMH P = (P ;; pbmh_step)"

end
