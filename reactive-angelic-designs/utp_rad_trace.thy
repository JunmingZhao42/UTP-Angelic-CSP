section \<open>Reactive Angelic Design Trace Healthiness\<close>

theory utp_rad_trace
  imports utp_rad_core "UTP-Reactive.utp_rea_healths"
begin

subsection \<open>RA1: Trace extension\<close>

(* Paper Definition 27. *)
definition rad_trace_extensions :: "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state set" where
"rad_trace_extensions s0 \<equiv>
  {s'. rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s'}"

(* Paper Definition 28. *)
(* RA1 P(ok, s, ok', ac') = P(ok, s, ok', ac'') \<and> ac'' \<noteq> {},
   where ac'' = rad_trace_extensions s \<inter> ac'. *)
definition RA1 ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA1 P \<equiv> (\<lambda> (x, z).
  let x_vars = des_vars.more x;
      z_vars = des_vars.more z;
      s0 = astate.s\<^sub>v x_vars;
      ac' = achoices.ac\<^sub>v z_vars;
      ac'' = rad_trace_extensions s0 \<inter> ac';
      z_vars' = achoices.ac\<^sub>v_update (\<lambda>_. ac'') z_vars;
      z' = des_vars.more_update (\<lambda>_. z_vars') z
  in P (x, z') \<and> ac'' \<noteq> {})"

lemma RA1_obs:
  "RA1 P (ades_obs ok0 s0 ok' ac') =
    (P (ades_obs ok0 s0 ok' (rad_trace_extensions s0 \<inter> ac')) \<and>
      rad_trace_extensions s0 \<inter> ac' \<noteq> {})"
  by (simp add: RA1_def Let_def)

lemma RA1_not_ok_eval:
  "RA1 (\<not> ok\<^sup><) (x, z) \<longleftrightarrow>
   (\<not> des_vars.ok\<^sub>v x \<and>
    rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
      achoices.ac\<^sub>v (des_vars.more z) \<noteq> {})"
  by (simp add: RA1_def Let_def; pred_auto)

lemma rad_trace_extensions_refl [simp]:
  "z \<in> rad_trace_extensions z"
  by (simp add: rad_trace_extensions_def)

lemma rad_trace_extensions_trans:
  "\<lbrakk> y \<in> rad_trace_extensions x; z \<in> rad_trace_extensions y \<rbrakk> \<Longrightarrow>
   z \<in> rad_trace_extensions x"
  by (auto simp add: rad_trace_extensions_def intro: order_trans)

lemma rad_trace_extensions_inter_absorb:
  "s1 \<in> rad_trace_extensions x \<Longrightarrow>
   rad_trace_extensions s1 \<inter> (rad_trace_extensions x \<inter> Y) =
   rad_trace_extensions s1 \<inter> Y"
  by (auto dest: rad_trace_extensions_trans)

lemma rad_trace_extensions_Int_Collect:
  "X \<inter> {s1. P s1} = {s1. s1 \<in> X \<and> P s1}"
  by auto

lemma RA1_idem: "RA1 (RA1 P) = RA1 P"
  by (simp add: RA1_def rad_trace_extensions_def fun_eq_iff; blast)

lemma RA1_Idempotent [closure]: "Idempotent RA1"
  by (simp add: Idempotent_def RA1_idem)

lemma RA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA1 P \<sqsubseteq> RA1 Q"
  by (auto simp add: RA1_def pred_refine_iff Let_def split: prod.splits)

lemma RA1_Monotonic [closure]: "Monotonic RA1"
  by (rule MonotonicI, rule RA1_mono)

lemma RA1_design_post: "RA1 (P \<turnstile> Q) = RA1 (P \<turnstile> RA1 Q)"
  by (simp add: RA1_def design_def fun_eq_iff Let_def; pred_auto; blast)

(* Thesis Theorem T.5.2.2. *)
lemma RA1_conj: "RA1 (P \<and> Q) = (RA1 P \<and> RA1 Q)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto; blast)

(* Thesis Theorem T.5.2.3. *)
lemma RA1_disj: "RA1 (P \<or> Q) = (RA1 P \<or> RA1 Q)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto; blast)

lemma RA1_conj_ok: "RA1 (P \<and> ok\<^sup>>) = (RA1 P \<and> ok\<^sup>>)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto)

lemma RA1_false: "RA1 false = false"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto)

lemma RA1_state_choice: "RA1 ades_state_choice = ades_state_choice"
  by (simp add: RA1_def ades_state_choice_def fun_eq_iff Let_def;
      pred_auto; blast intro: rad_trace_extensions_refl)

(* RA1 changes only state and choice components, so it commutes with the
   design ok substitutions. *)
lemma RA1_ok_in_subst:
  "(RA1 P)\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> = RA1 (P\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: RA1_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

lemma RA1_ok_out_subst:
  "(RA1 P)\<lbrakk>\<guillemotleft>ok'\<guillemotright>/ok\<^sup>>\<rbrakk> = RA1 (P\<lbrakk>\<guillemotleft>ok'\<guillemotright>/ok\<^sup>>\<rbrakk>)"
  by (simp add: RA1_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

lemma RA1_unrest_ok_in [unrest]:
  "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> RA1 P"
  apply (simp add: unrest_lens RA1_def Let_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma RA1_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> RA1 P"
  apply (simp add: unrest_lens RA1_def Let_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs des_more_ok_update_commute)
  done

(* Paper Lemma 23 *)
lemma RA1_design_pre:
  "RA1 (P \<turnstile> Q) = RA1 ((\<not> RA1 (\<not> P)) \<turnstile> Q)"
  by (simp add: RA1_def design_def fun_eq_iff Let_def; pred_auto; blast)

(* Paper Theorem 9. *)
theorem RA1_A0_absorb: "RA1 (A0 P) = RA1 P"
  by (simp add: RA1_def A0_def ac_non_empty_def fun_eq_iff Let_def;
      pred_auto)

(* RA1 absorbs the A0 non-emptiness requirement. *)
lemma RA1_ac_non_empty_absorb: "RA1 (ac_non_empty \<and> P) = RA1 P"
  by (simp add: RA1_def ac_non_empty_def fun_eq_iff Let_def;
      pred_auto)

(* Unlike RA1_ac_non_empty_absorb above, the conjunction here is
   outside RA1. *)
lemma RA1_ac_non_empty_conj_absorb:
  "(ac_non_empty \<and> RA1 P) = RA1 P"
  by (simp add: RA1_def ac_non_empty_def fun_eq_iff Let_def;
      pred_auto)

lemma A2_RA1_absorb:
  "A2 (RA1 (A2 P)) = RA1 (A2 P)"
  by (simp add: A2_def RA1_def fun_eq_iff Let_def comp_def; blast)

lemma RA1_A2_closure [closure]:
  assumes "P is A2"
  shows "RA1 P is A2"
  using A2_RA1_absorb[of P]
  by (simp only: Healthy_if[OF assms] Healthy_def')

(* Paper Theorem 70 *)
theorem PBMH_ades_RA1_absorb:
  "(PBMH_ades \<circ> RA1 \<circ> PBMH_ades) P = (RA1 \<circ> PBMH_ades) P"
  by (simp add: PBMH_ades_def RA1_def fun_eq_iff; pred_auto)

lemma RA1_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "RA1 P is PBMH_ades"
  using assms PBMH_ades_RA1_absorb[of P]
  by (simp add: Healthy_def')

(* Thesis Lemma L.G.1.21: RA1 only shrinks the choice set, so on a
   PBMH-healthy predicate it is a strengthening. *)
lemma RA1_refine:
  assumes "P is PBMH_ades"
  shows "P \<sqsubseteq> RA1 P"
proof (unfold pred_refine_iff, safe)
  fix v
  assume ra1: "RA1 P v"
  obtain x z where obs: "v = (x, z)" by (cases v)
  let ?ac'' = "rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
               achoices.ac\<^sub>v (des_vars.more z)"
  let ?z = "des_vars.more_update
              (\<lambda>_. achoices.ac\<^sub>v_update (\<lambda>_. ?ac'') (des_vars.more z)) z"
  have "P (x, ?z)"
    using ra1 by (simp add: obs RA1_def Let_def)
  then have "P (x, z)"
    by (rule PBMH_ades_upward[OF assms]; simp)
  then show "P v" by (simp add: obs)
qed

lemma PBMH_ades_RA1_not_ok [simp]:
  "PBMH_ades (RA1 (\<not> ok\<^sup><)) = RA1 (\<not> ok\<^sup><)"
  using PBMH_ades_RA1_absorb[of "(\<not> ok\<^sup><)"]
  by simp

subsection \<open>RA2: Trace-history independence\<close>

(* s \<oplus> {tr \<mapsto> 0} *)
definition rad_zero_trace :: "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state" where
"rad_zero_trace s0 \<equiv>
  rad_tr\<^sub>v_update (\<lambda>_. 0) s0"

(* z \<oplus> {tr \<mapsto> z.tr - s.tr} *)
definition rad_trace_difference ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state" where
"rad_trace_difference s0 z \<equiv>
  rad_tr\<^sub>v_update
    (\<lambda>_. rad_tr\<^sub>v z - rad_tr\<^sub>v s0) z"

(* { z[(z.tr-s.tr) / tr] | z \<in> ac' \<and> s.tr \<le> z.tr } *)
definition rad_normalise_choices ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state set \<Rightarrow> ('t, 'e) rad_state set" where
"rad_normalise_choices s0 ac' \<equiv>
  {rad_trace_difference s0 z | z.
    z \<in> ac' \<and>
    rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v z}"

(* Paper Definition 29. *)
(* RA2 P(ok, s, ok', ac') = P(ok, s[0/tr], ok', rad_normalise_choices s ac') *)
definition RA2 ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
where [pred]: "RA2 P \<equiv> (\<lambda> (x, z).
  let x_vars = des_vars.more x;
      z_vars = des_vars.more z;
      s0 = astate.s\<^sub>v x_vars;
      ac' = achoices.ac\<^sub>v z_vars;
      ac'' = rad_normalise_choices s0 ac';
      x_vars' = astate.s\<^sub>v_update
        (\<lambda>_. rad_zero_trace s0) x_vars;
      z_vars' = achoices.ac\<^sub>v_update (\<lambda>_. ac'') z_vars;
      x' = des_vars.more_update (\<lambda>_. x_vars') x;
      z' = des_vars.more_update (\<lambda>_. z_vars') z
  in P (x', z'))"

lemma RA2_obs':
  "RA2 P (ades_obs ok0 s0 ok' ac') =
    P (ades_obs ok0 (rad_zero_trace s0) ok' (rad_normalise_choices s0 ac'))"
  by (simp add: RA2_def Let_def)

lemma rad_normalise_choices_mono:
  "ac' \<subseteq> X \<Longrightarrow>
   rad_normalise_choices s0 ac' \<subseteq>
   rad_normalise_choices s0 X"
  by (auto simp add: rad_normalise_choices_def)

lemma rad_zero_trace_idem [simp]:
  "rad_zero_trace (rad_zero_trace s0) = rad_zero_trace s0"
  by (cases s0; simp add: rad_zero_trace_def)

lemma rad_trace_difference_zero [simp]:
  "rad_trace_difference (rad_zero_trace s0) z = z"
  by (cases s0; cases z; simp add: rad_trace_difference_def rad_zero_trace_def)

lemma rad_zero_trace_wait [simp]:
  "rad_wait\<^sub>v (rad_zero_trace s0) = rad_wait\<^sub>v s0"
  by (simp add: rad_zero_trace_def)

lemma rad_normalise_choices_zero [simp]:
  "rad_normalise_choices (rad_zero_trace s0) ac' = ac'"
  unfolding rad_normalise_choices_def
  by (simp only: rad_trace_difference_zero; auto simp: rad_zero_trace_def)

lemma rad_trace_update_self [simp]:
  "rad_tr\<^sub>v_update (\<lambda>_. rad_tr\<^sub>v z) z = z"
  by (cases z) simp

(* Prefix the original history to a normalised trace. *)
definition rad_trace_prepend ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state"
where
  "rad_trace_prepend s0 z \<equiv>
    rad_tr\<^sub>v_update (\<lambda>tr. rad_tr\<^sub>v s0 + tr) z"

(* Normalising is the inverse image of prepending the initial trace. *)
lemma rad_normalise_choices_as_prepend:
  "rad_normalise_choices s0 ac' =
   {s'. rad_trace_prepend s0 s' \<in> ac'}"
  apply (rule Set.set_eqI)
  apply (auto simp add: rad_normalise_choices_def rad_trace_prepend_def
      rad_trace_difference_def comp_def diff_add_cancel_left'
      intro!: exI[where x =
        "rad_tr\<^sub>v_update (\<lambda>tr. rad_tr\<^sub>v s0 + tr) x" for x])
  done

lemma rad_trace_difference_prepend:
  "rad_trace_difference s0 (rad_trace_prepend s0 z) = z"
  by (cases z; simp add: rad_trace_prepend_def rad_trace_difference_def)

lemma rad_normalise_choices_prepend:
  "rad_normalise_choices s0 (rad_trace_prepend s0 ` ac') = ac'"
  by (auto simp: rad_normalise_choices_as_prepend;
      metis rad_trace_difference_prepend)

lemma RA2_trace_prepend_obs:
  assumes "P is RA2"
  shows "P (ades_obs ok0 s0 ok' (rad_trace_prepend s0 ` ac')) =
    P (ades_obs ok0 (rad_zero_trace s0) ok' ac')"
  by (subst Healthy_if[OF assms, symmetric];
      simp add: RA2_obs' rad_normalise_choices_prepend)

lemma RA2_idem: "RA2 (RA2 P) = RA2 P"
  by (simp add: RA2_def rad_zero_trace_def rad_normalise_choices_def
      rad_trace_difference_def fun_eq_iff)

lemma RA2_Idempotent [closure]: "Idempotent RA2"
  by (simp add: Idempotent_def RA2_idem)

lemma RA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA2 P \<sqsubseteq> RA2 Q"
  by (auto simp add: RA2_def pred_refine_iff Let_def split: prod.splits)

lemma RA2_Monotonic [closure]: "Monotonic RA2"
  by (rule MonotonicI, rule RA2_mono)

lemma RA2_design_distrib:
  "RA2 (P \<turnstile> Q) = (RA2 P \<turnstile> RA2 Q)"
  by (simp add: RA2_def design_def fun_eq_iff; pred_auto)

(* Thesis Theorem T.5.2.6. *)
lemma RA2_conj: "RA2 (P \<and> Q) = (RA2 P \<and> RA2 Q)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

(* Thesis Theorem T.5.2.7. *)
lemma RA2_disj: "RA2 (P \<or> Q) = (RA2 P \<or> RA2 Q)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_conj_ok: "RA2 (P \<and> ok\<^sup>>) = (RA2 P \<and> ok\<^sup>>)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_not: "RA2 (\<not> P) = (\<not> RA2 P)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_true: "RA2 true = true"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_false: "RA2 false = false"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_not_ok_expr:
  "RA2 (\<not> ok\<^sup><) = (\<not> ok\<^sup><)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_impl: "RA2 (P \<longrightarrow> Q) = (RA2 P \<longrightarrow> RA2 Q)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_state_choice: "RA2 ades_state_choice = ades_state_choice"
  by (simp add: RA2_def ades_state_choice_def Let_def fun_eq_iff
      comp_def rad_normalise_choices_as_prepend[unfolded rad_trace_prepend_def] rad_zero_trace_def)

lemma RA2_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> P \<Longrightarrow> $ok\<^sup>> \<sharp> RA2 P"
  apply (simp add: unrest_lens RA2_def Let_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs des_more_ok_update_commute)
  done

lemma RA2_unrest_ok_in [unrest]:
  "$ok\<^sup>< \<sharp> P \<Longrightarrow> $ok\<^sup>< \<sharp> RA2 P"
  apply (simp add: unrest_lens RA2_def Let_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs des_more_ok_update_commute)
  done

lemma RA2_ok_in_subst:
  "(RA2 P)\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> = RA2 (P\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: RA2_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

lemma rad_normalise_choices_extensions:
  "rad_normalise_choices s0 (rad_trace_extensions s0 \<inter> ac') =
   rad_normalise_choices s0 ac'"
  by (auto simp add: rad_normalise_choices_def rad_trace_extensions_def)

lemma rad_normalise_choices_nonempty:
  "rad_normalise_choices s0 ac' \<noteq> {} \<longleftrightarrow>
   rad_trace_extensions s0 \<inter> ac' \<noteq> {}"
  by (auto simp add: rad_normalise_choices_def rad_trace_extensions_def)

lemma rad_zero_trace_extensions:
  "rad_trace_extensions (rad_zero_trace s0) \<inter>
   rad_normalise_choices s0 ac' =
   rad_normalise_choices s0 ac'"
  by (auto simp add: rad_trace_extensions_def rad_zero_trace_def
      rad_normalise_choices_def rad_trace_difference_def)

lemma rad_zero_trace_in_normalise:
  "rad_zero_trace s0 \<in> rad_normalise_choices s0 ac' \<longleftrightarrow>
   s0 \<in> ac'"
  apply (auto simp add: rad_zero_trace_def rad_normalise_choices_def
      rad_trace_difference_def)
  subgoal for z
    by (cases s0; cases z) (force dest: minus_zero_eq[rotated])
  subgoal
    by (rule exI[where x=s0], simp)
  done

(* Paper Theorem 71 *)
theorem RA1_RA2_commute: "(RA1 \<circ> RA2) P = (RA2 \<circ> RA1) P"
  by (simp add: RA1_def RA2_def fun_eq_iff
      rad_normalise_choices_extensions rad_normalise_choices_nonempty
      rad_zero_trace_extensions Let_def)

lemmas RA1_RA2_commute' = RA1_RA2_commute[simplified comp_apply]

lemma RA2_RA1_ac_non_empty_absorb:
  "(ac_non_empty \<and> (RA2 \<circ> RA1) P) = (RA2 \<circ> RA1) P"
  using RA1_ac_non_empty_conj_absorb
  by (simp only: comp_apply RA1_RA2_commute'[symmetric])

(* Thesis Lemma L.G.2.9: under RA2, requiring a non-empty choice set is
   the same as enforcing RA1. *)
lemma RA2_ac_non_empty:
  "RA2 (P \<and> ac_non_empty) = RA2 (RA1 P)"
  by (simp add: RA1_def RA2_def ac_non_empty_def fun_eq_iff
      rad_normalise_choices_extensions rad_normalise_choices_nonempty
      rad_zero_trace_extensions Let_def; pred_auto;
      auto simp add: rad_normalise_choices_def rad_trace_extensions_def)

(* Under RA2, requiring a non-empty choice set is exactly RA1 of true. *)
lemma RA2_ac_non_empty_eq: "RA2 ac_non_empty = RA1 true"
proof -
  have absorb: "(true \<and> ac_non_empty) = ac_non_empty"
    by pred_auto
  have "RA2 ac_non_empty = RA2 (RA1 true)"
    using RA2_ac_non_empty[of true] by (simp only: absorb)
  then show ?thesis
    by (simp only: RA1_RA2_commute'[symmetric] RA2_true)
qed

lemma RA1_true_absorb_lift:
  assumes "(ac_non_empty \<and> (X \<and> Y)) = (X \<and> Y)"
  shows "(RA1 true \<and> (RA2 X \<and> RA2 Y)) = (RA2 X \<and> RA2 Y)"
  using arg_cong[where f=RA2, OF assms]
  by (simp only: RA2_conj RA2_ac_non_empty_eq)

lemma RA2_RA1_true: "RA2 (RA1 true) = RA1 true"
  by (simp only: RA1_RA2_commute'[symmetric] RA2_true)

(* Conjoining RA1 true with an RA2 image enforces RA1 inside it. *)
lemma RA1_true_conj_RA2: "(RA1 true \<and> RA2 P) = RA2 (RA1 P)"
proof -
  have "RA2 (RA1 P) = (RA2 P \<and> RA2 ac_non_empty)"
    by (simp only: RA2_ac_non_empty[symmetric] RA2_conj)
  then show ?thesis
    by (simp only: RA2_ac_non_empty_eq pred_ba.inf_commute)
qed

(* Under RA1 true, a disjunct absorbed by Y on the inside is absorbed
   by the RA2 \<circ> RA1 image of Y. *)
lemma RA2_RA1_disj_absorb:
  assumes "(X \<or> Y) = Y"
  shows "(RA1 true \<and> (RA2 X \<or> RA2 (RA1 Y))) = RA2 (RA1 Y)"
  apply (simp only: pred_ba.boolean_algebra.conj_disj_distrib
      RA1_true_conj_RA2 RA1_idem)
  by (simp only: RA2_disj[symmetric] RA1_disj[symmetric] assms)

lemma RA1_RA2_ac_non_empty: "RA1 (RA2 ac_non_empty) = RA1 true"
  by (simp only: RA2_ac_non_empty_eq RA1_idem)

(* Paper Theorem 66 *)
theorem PBMH_ades_RA2_absorb:
  "(PBMH_ades \<circ> RA2 \<circ> PBMH_ades) P = (RA2 \<circ> PBMH_ades) P"
  apply (simp add: PBMH_ades_def RA2_def fun_eq_iff)
  apply pred_auto
  subgoal for ok0 tr ref wait ok' ac' X Y
    apply (rule exI[where x=Y])
    apply (intro conjI)
     apply assumption
    apply (rule subset_trans)
     apply assumption
    apply (rule rad_normalise_choices_mono)
    apply assumption
    done
  done

lemma RA2_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "RA2 P is PBMH_ades"
  using assms PBMH_ades_RA2_absorb[of P]
  by (simp add: Healthy_def')

subsection \<open>The reactive identity\<close>

(* Paper Definition 30: reactive identity. *)
definition II_Rac :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "II_Rac \<equiv> (\<lambda> (x, z).
  let s0 = astate.s\<^sub>v (des_vars.more x);
      ac' = achoices.ac\<^sub>v (des_vars.more z)
  in RA1 (\<not> ok\<^sup><) (x, z) \<or> (ok\<^sub>v z \<and> s0 \<in> ac'))"

(* Thesis Theorems T.G.3.1, T.G.3.2, and T.G.3.4. *)
lemma II_Rac_eval:
  "II_Rac (x, z) \<longleftrightarrow>
   ((\<not> des_vars.ok\<^sub>v x \<and>
     rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
       achoices.ac\<^sub>v (des_vars.more z) \<noteq> {}) \<or>
    (des_vars.ok\<^sub>v z \<and>
     astate.s\<^sub>v (des_vars.more x) \<in> achoices.ac\<^sub>v (des_vars.more z)))"
  by (simp add: II_Rac_def RA1_def Let_def; pred_auto)

lemma RA1_II_Rac: "RA1 II_Rac = II_Rac"
  apply (simp only: RA1_def II_Rac_def fun_eq_iff)
  apply (simp add: Let_def rad_trace_extensions_def SEXP_def lens_defs
      des_vars.ok_def des_vars.more\<^sub>L_def)
  apply blast
  done

lemma RA2_II_Rac: "RA2 II_Rac = II_Rac"
  by (pred_auto add: rad_zero_trace_extensions
      rad_normalise_choices_nonempty rad_zero_trace_in_normalise)

lemma II_Rac_is_RA1 [closure]: "II_Rac is RA1"
  by (rule Healthy_intro, rule RA1_II_Rac)

lemma II_Rac_is_RA2 [closure]: "II_Rac is RA2"
  by (rule Healthy_intro, rule RA2_II_Rac)

lemma PBMH_ades_II_Rac [simp]: "PBMH_ades II_Rac = II_Rac"
proof -
  have split:
    "II_Rac = (RA1 (\<not> ok\<^sup><) \<or> (ades_state_choice \<and> ok\<^sup>>))"
    by (simp add: II_Rac_def ades_state_choice_def fun_eq_iff Let_def; pred_auto)
  show ?thesis
    by (simp only: split PBMH_ades_disj PBMH_ades_RA1_not_ok
        PBMH_ades_conj_ok Healthy_if[OF ades_state_choice_is_PBMH_ades])
qed

lemma II_Rac_is_PBMH_ades [closure]: "II_Rac is PBMH_ades"
  by (rule Healthy_intro, rule PBMH_ades_II_Rac)

end
