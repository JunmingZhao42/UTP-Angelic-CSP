section \<open>Reactive Angelic Design Core\<close>

theory utp_rad_core
  imports "UTP-Angelic-Designs.utp_ades" "UTP-Reactive.utp_rea_core"
begin

subsection \<open>Alphabet (Paper Definition 26)\<close>

text \<open>
  A reactive angelic design retains the outer design observations @{term ok}
  and @{term "ok\<^sup>>"}.  Its initial state @{term s} and every state offered
  in the final angelic choice @{term ac} contain a trace, a refusal set, and a
  waiting flag.  Thus this record is the inner observation state, rather than
  a replacement for the complete reactive-process alphabet.
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

lemma rad_state_full_selectors [simp]:
  "rad_tr\<^sub>v (des_vars.more x) = rea_vars.tr\<^sub>v x"
  "rad_wait\<^sub>v (des_vars.more x) = rea_vars.wait\<^sub>v x"
  "rad_ref\<^sub>v (des_vars.more x) = rea_vars.more x"
  by (cases x; simp)+

lemma rad_state_started_selectors [simp]:
  "rea_vars.tr\<^sub>v \<lparr>ok\<^sub>v = True, \<dots> = x\<rparr> = rad_tr\<^sub>v x"
  "rea_vars.wait\<^sub>v \<lparr>ok\<^sub>v = True, \<dots> = x\<rparr> = rad_wait\<^sub>v x"
  "rea_vars.more \<lparr>ok\<^sub>v = True, \<dots> = x\<rparr> = rad_ref\<^sub>v x"
  by (cases x; simp)+

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
