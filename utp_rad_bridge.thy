section \<open>Reactive Angelic Design Alphabet Bridge\<close>

theory utp_rad_bridge
  imports utp_rad_core "UTP-Reactive.utp_rea_healths"
begin

subsection \<open>Observation isomorphism\<close>

(* CSP's flat alphabet is {ok, tr, ref, wait}; rea_vars.more stores ref. *)
type_synonym 'e csp_obs = "('e list, 'e set) rp"

(* Repackage one nested RAD observation as a flat CSP observation. *)
definition rad2csp_obs ::
  "'e rad_state des_vars_scheme \<Rightarrow> 'e csp_obs" where
[pred]: "rad2csp_obs x =
  \<lparr> utp_des_core.des_vars.ok\<^sub>v = ok\<^sub>v x,
    utp_rea_core.rea_vars.wait\<^sub>v =
      utp_rad_core.rad_state.wait\<^sub>v (des_vars.more x),
    utp_rea_core.rea_vars.tr\<^sub>v =
      utp_rad_core.rad_state.tr\<^sub>v (des_vars.more x),
    \<dots> = utp_rad_core.rad_state.ref\<^sub>v (des_vars.more x) \<rparr>"

(* Repackage one flat CSP observation as a nested RAD observation. *)
definition csp2rad_obs ::
  "'e csp_obs \<Rightarrow> 'e rad_state des_vars_scheme" where
[pred]: "csp2rad_obs x =
  \<lparr> utp_des_core.des_vars.ok\<^sub>v = ok\<^sub>v x,
    \<dots> = \<lparr> utp_rad_core.rad_state.tr\<^sub>v = rea_vars.tr\<^sub>v x,
          utp_rad_core.rad_state.ref\<^sub>v = rea_vars.more x,
          utp_rad_core.rad_state.wait\<^sub>v = rea_vars.wait\<^sub>v x,
          \<dots> = () \<rparr> \<rparr>"

(* The observation conversions are bijective. *)
lemma csp2rad_obs_inverse [simp]:
  "csp2rad_obs (rad2csp_obs x) = x"
  by (cases x; simp add: rad2csp_obs_def csp2rad_obs_def)

lemma rad2csp_obs_inverse [simp]:
  "rad2csp_obs (csp2rad_obs x) = x"
  by (cases x; simp add: rad2csp_obs_def csp2rad_obs_def)

subsection \<open>Relation and design mappings\<close>

(* Lift the observation conversions pointwise to both ends of a relation. *)
definition rad2csp_rel :: "'e rad_state des_hrel \<Rightarrow> ('e list, 'e set) rp_hrel"
where [pred]: "rad2csp_rel P = (\<lambda> (x, y). P (csp2rad_obs x, csp2rad_obs y))"

definition csp2rad_rel :: "('e list, 'e set) rp_hrel \<Rightarrow> 'e rad_state des_hrel"
where [pred]: "csp2rad_rel P = (\<lambda> (x, y). P (rad2csp_obs x, rad2csp_obs y))"

lemma csp2rad_rel_inverse [simp]:
  "csp2rad_rel (rad2csp_rel P) = P"
  by (simp add: rad2csp_rel_def csp2rad_rel_def fun_eq_iff)

lemma rad2csp_rel_inverse [simp]:
  "rad2csp_rel (csp2rad_rel P) = P"
  by (simp add: rad2csp_rel_def csp2rad_rel_def fun_eq_iff)

(* Designs distribute through the observation repackaging. *)
lemma csp2rad_rel_design:
  "csp2rad_rel ((\<not> F) \<turnstile> T) =
   ((\<not> csp2rad_rel F) \<turnstile> csp2rad_rel T)"
  by (simp add: csp2rad_rel_def design_def fun_eq_iff
      rad2csp_obs_def; pred_auto)

definition rad_ac2p :: "'e reactive_angelic_design \<Rightarrow> ('e list, 'e set) rp_hrel"
where [pred]: "rad_ac2p P = rad2csp_rel (ac2p P)"

(* Paper predicate mapping p2ac, after repackaging the observations. *)
definition rad_p2ac :: "('e list, 'e set) rp_hrel \<Rightarrow> 'e reactive_angelic_design"
where [pred]: "rad_p2ac P = p2ac (csp2rad_rel P)"

(* The design-level adapter uses d2ac rather than the paper's predicate p2ac. *)
definition rad_d2ac :: "('e list, 'e set) rp_hrel \<Rightarrow> 'e reactive_angelic_design"
where [pred]: "rad_d2ac P = d2ac (csp2rad_rel P)"

lemma rad_p2ac_PBMH_ades [closure]:
  "rad_p2ac P is PBMH_ades"
  by (simp add: Healthy_def rad_p2ac_def)

lemma rad_ac2p_d2ac:
  assumes "csp2rad_rel P is \<^bold>H"
  shows "(rad_ac2p \<circ> rad_d2ac) P = P"
  by (simp add: rad_ac2p_def rad_d2ac_def
      ac2p_d2ac[simplified comp_apply] assms)

end
