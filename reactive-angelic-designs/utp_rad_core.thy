section \<open>Reactive Angelic Design Core\<close>

theory utp_rad_core
  imports "UTP-Angelic-Designs.utp_ades" "UTP-Reactive.utp_rea_core"
begin

subsection \<open>Alphabet (Paper Definition 26)\<close>

text \<open>
  A reactive angelic design has outer termination flags @{term ok} and @{term "ok\<^sup>>"}.
  Its initial state @{term s} and each state in the final choice set @{term "ac\<^sup>>"}
  contain a trace, a refusal set and a waiting flag.
\<close>

(* Paper Definition 26, with the trace generalised from event lists to
   the trace algebra of Circus_Toolkit, as in reactive designs. *)
type_synonym ('t, 'e) rad_state = "('t, 'e set) rea_vars_ext"

text \<open>The extension omits @{term ok}; its tail stores the refusal set.
  The following accessors expose the existing reactive fields on that extension.\<close>

abbreviation "rad_tr\<^sub>v" where
"rad_tr\<^sub>v x \<equiv>
  rea_vars.tr\<^sub>v \<lparr>ok\<^sub>v = False, \<dots> = x\<rparr>"
abbreviation "rad_wait\<^sub>v" where
"rad_wait\<^sub>v x \<equiv>
  rea_vars.wait\<^sub>v \<lparr>ok\<^sub>v = False, \<dots> = x\<rparr>"
abbreviation "rad_ref\<^sub>v" where
"rad_ref\<^sub>v x \<equiv>
  rea_vars.more \<lparr>ok\<^sub>v = False, \<dots> = x\<rparr>"
abbreviation "rad_tr\<^sub>v_update" where
"rad_tr\<^sub>v_update f x \<equiv>
  des_vars.more (rea_vars.tr\<^sub>v_update f \<lparr>ok\<^sub>v = False, \<dots> = x\<rparr>)"
abbreviation "rad_wait\<^sub>v_update" where
"rad_wait\<^sub>v_update f x \<equiv>
  des_vars.more (rea_vars.wait\<^sub>v_update f \<lparr>ok\<^sub>v = False, \<dots> = x\<rparr>)"

definition "rad_wait" where
"rad_wait =
  \<lparr>lens_get = rad_wait\<^sub>v,
    lens_put = (\<lambda>x v. rad_wait\<^sub>v_update (\<lambda>_. v) x)\<rparr>"
definition "rad_tr" where
"rad_tr =
  \<lparr>lens_get = rad_tr\<^sub>v,
    lens_put = (\<lambda>x v. rad_tr\<^sub>v_update (\<lambda>_. v) x)\<rparr>"

declare rad_wait_def [alpha_defs] rad_tr_def [alpha_defs]

lemma rad_state_cases [case_names state, cases type: rea_vars_ext]:
  fixes x :: "('t::trace, 'e) rea_vars_ext"
  obtains w t r where "x = rea_vars_ext w t r"
  by (induct x rule: rea_vars.ext_induct) auto

lemma rad_tr_record:
  fixes s :: "('t::trace, 'e) rea_vars_ext"
  shows "rea_vars.tr\<^sub>v \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr> = rad_tr\<^sub>v s"
  by (cases b; cases s; simp)

lemma rad_wait_record:
  fixes s :: "('t::trace, 'e) rea_vars_ext"
  shows "rea_vars.wait\<^sub>v \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr> = rad_wait\<^sub>v s"
  by (cases b; cases s; simp)

lemma rad_ref_record:
  fixes s :: "('t::trace, 'e) rea_vars_ext"
  shows "rea_vars.more \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr> = rad_ref\<^sub>v s"
  by (cases b; cases s; simp)

(* The False cases are reflexive after unfolding the accessor abbreviations. *)
declare rad_tr_record[where b=True, simp]
        rad_wait_record[where b=True, simp]
        rad_ref_record[where b=True, simp]

lemma rad_state_rebuild [simp]:
  "\<lparr>ok\<^sub>v = b, \<dots> = rad_tr\<^sub>v_update f x\<rparr> =
   rea_vars.tr\<^sub>v_update f \<lparr>ok\<^sub>v = b, \<dots> = x\<rparr>"
  "\<lparr>ok\<^sub>v = b, \<dots> = rad_wait\<^sub>v_update g x\<rparr> =
   rea_vars.wait\<^sub>v_update g \<lparr>ok\<^sub>v = b, \<dots> = x\<rparr>"
  by (cases x; simp)+

lemma rad_state_splits [alpha_splits]:
  "(\<forall>x. P x) = (\<forall>w t r. P (rea_vars_ext w t r))"
  "(\<exists>x. P x) = (\<exists>w t r. P (rea_vars_ext w t r))"
  by (auto; metis rad_state_cases)+

lemma rad_state_lenses [simp]:
  "vwb_lens rad_wait" "vwb_lens rad_tr"
  apply (unfold_locales)
  apply (simp_all add: rad_wait_def rad_tr_def)
  done

type_synonym ('t, 'e) reactive_angelic_rel =
  "('t, 'e) rad_state angelic_rel"
type_synonym ('t, 'e) reactive_angelic_design =
  "('t, 'e) rad_state angelic_design"

end
