section \<open>Reactive Angelic Design Alphabet Bridge\<close>

theory utp_rad_bridge
  imports utp_rad_core "UTP-Reactive.utp_rea_healths"
begin

(* todo: need to go through this file *)
subsection \<open>Observation isomorphism\<close>

text \<open>
  The reactive-process alphabet already supplies @{term ok}, @{term wait}, and
  @{term tr}.  We instantiate its open extension with the refusal set.  This
  gives the flat paper alphabet @{text "{ok, tr, ref, wait}"}, with
  @{const rea_vars.more} representing @{text ref}.
\<close>

type_synonym 'e csp_obs = "('e list, 'e set) rp"

text \<open>
  Reactive angelic designs instead package @{text "{tr, ref, wait}"} beneath
  the design continuation.  The following functions flatten and unflatten
  these two record presentations.
\<close>

definition rad_flatten :: "'e rad_state des_vars_scheme \<Rightarrow> 'e csp_obs" where
"rad_flatten x =
  \<lparr> utp_des_core.des_vars.ok\<^sub>v = ok\<^sub>v x,
    utp_rea_core.rea_vars.wait\<^sub>v =
      utp_rad_core.rad_state.wait\<^sub>v (des_vars.more x),
    utp_rea_core.rea_vars.tr\<^sub>v =
      utp_rad_core.rad_state.tr\<^sub>v (des_vars.more x),
    \<dots> = utp_rad_core.rad_state.ref\<^sub>v (des_vars.more x) \<rparr>"

definition rad_unflatten :: "'e csp_obs \<Rightarrow> 'e rad_state des_vars_scheme" where
"rad_unflatten x =
  \<lparr> utp_des_core.des_vars.ok\<^sub>v = ok\<^sub>v x,
    \<dots> = \<lparr> utp_rad_core.rad_state.tr\<^sub>v = rea_vars.tr\<^sub>v x,
          utp_rad_core.rad_state.ref\<^sub>v = rea_vars.more x,
          utp_rad_core.rad_state.wait\<^sub>v = rea_vars.wait\<^sub>v x,
          \<dots> = () \<rparr> \<rparr>"

lemma rad_unflatten_flatten [simp]: "rad_unflatten (rad_flatten x) = x"
  by (cases x; simp add: rad_flatten_def rad_unflatten_def)

lemma rad_flatten_unflatten [simp]: "rad_flatten (rad_unflatten x) = x"
  by (cases x; simp add: rad_flatten_def rad_unflatten_def)

subsection \<open>Relation and design mappings\<close>

definition rad_rel_flatten ::
  "'e rad_state des_hrel \<Rightarrow> ('e list, 'e set) rp_hrel"
where
"rad_rel_flatten P = (\<lambda> (x, y). P (rad_unflatten x, rad_unflatten y))"

definition rad_rel_unflatten ::
  "('e list, 'e set) rp_hrel \<Rightarrow> 'e rad_state des_hrel"
where
"rad_rel_unflatten P = (\<lambda> (x, y). P (rad_flatten x, rad_flatten y))"

lemma rad_rel_unflatten_flatten [simp]:
  "rad_rel_unflatten (rad_rel_flatten P) = P"
  by (simp add: rad_rel_flatten_def rad_rel_unflatten_def fun_eq_iff)

lemma rad_rel_flatten_unflatten [simp]:
  "rad_rel_flatten (rad_rel_unflatten P) = P"
  by (simp add: rad_rel_flatten_def rad_rel_unflatten_def fun_eq_iff)

text \<open>
  These are the paper-level links specialised to the reactive alphabet.  They
  reuse the generic angelic-design mappings @{const ac2p} and @{const d2ac}.
\<close>

definition rad_ac2p ::
  "'e reactive_angelic_design \<Rightarrow> ('e list, 'e set) rp_hrel"
where
"rad_ac2p P = rad_rel_flatten (ac2p P)"

definition rad_p2ac ::
  "('e list, 'e set) rp_hrel \<Rightarrow> 'e reactive_angelic_design"
where
"rad_p2ac P = d2ac (rad_rel_unflatten P)"

lemma rad_ac2p_p2ac:
  assumes "rad_rel_unflatten P is \<^bold>H"
  shows "rad_ac2p (rad_p2ac P) = P"
  by (simp add: rad_ac2p_def rad_p2ac_def ac2p_d2ac assms)

end
