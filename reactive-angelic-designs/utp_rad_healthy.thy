section \<open>Reactive Angelic Design Healthiness Conditions\<close>

theory utp_rad_healthy
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

subsection \<open>Wait-false substitution\<close>

abbreviation rad_wait_lens where
"rad_wait_lens \<equiv>
  rad_wait ;\<^sub>L astate.s ;\<^sub>L des_vars.more\<^sub>L"

(* P_f \<equiv> P[s\<oplus>(wait \<mapsto> false)/s] *)
definition rad_wait_false ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "rad_wait_false P \<equiv> P\<lbrakk>False/rad_wait_lens\<^sup><\<rbrakk>"

no_notation wait_f ("_\<^sub>f" [1000] 1000)

notation rad_wait_false ("_\<^sub>f" [1000] 1000)

lemma A2_wait_cond:
  "A2 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (A2 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> A2 Q)"
  by (simp add: A2_def expr_if_def fun_eq_iff)

lemma rad_wait_cond_not:
  "(\<not> (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       (Q :: ('t::trace, 'e) reactive_angelic_design))) =
   ((\<not> P) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> Q))"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_impl:
  "((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (Q :: ('t::trace, 'e) reactive_angelic_design)) \<longrightarrow>
    (R \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> S)) =
   ((P \<longrightarrow> R) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (Q \<longrightarrow> S))"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_false:
  "(false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    (Q :: ('t::trace, 'e) reactive_angelic_design)) =
   ((\<not> rad_wait_lens\<^sup><) \<and> Q)"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_conj_distrib:
  fixes C A B :: "('t::trace, 'e) reactive_angelic_design"
  shows "(C \<and> (A \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> B)) =
    ((C \<and> A) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (C \<and> B))"
  by (simp add: expr_if_def fun_eq_iff; pred_auto)

lemma rad_wait_cond_unrest_ok_out [unrest]:
  "\<lbrakk> $ok\<^sup>> \<sharp> P; $ok\<^sup>> \<sharp> Q \<rbrakk> \<Longrightarrow>
   $ok\<^sup>> \<sharp> (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q)"
  by (simp add: unrest_lens expr_if_def)

lemma rad_wait_cond_unrest_ok_in [unrest]:
  "\<lbrakk> $ok\<^sup>< \<sharp> P; $ok\<^sup>< \<sharp> Q \<rbrakk> \<Longrightarrow>
   $ok\<^sup>< \<sharp> (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q)"
  apply (simp add: unrest_lens expr_if_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma rad_wait_atom_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> ((rad_wait_lens\<^sup><) :: ('t::trace, 'e) reactive_angelic_design)"
  apply (simp add: unrest_lens)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      subst_ext_def SEXP_def lens_defs alpha_defs)
  done

lemma rad_wait_cond_ok_in_subst:
  "((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> =
   (P\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    Q\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: expr_if_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_atom_ok_in_subst [usubst]:
  "((rad_wait_lens\<^sup><) ::
    ('t::trace, 'e) reactive_angelic_design)\<lbrakk>\<guillemotleft>ok0\<guillemotright>/ok\<^sup><\<rbrakk> =
   (rad_wait_lens\<^sup><)"
  by (simp add: fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_as_state_subst:
  "rad_wait_false P =
   ades_state_subst
     (subst_upd subst_id (rad_wait ;\<^sub>L astate.s) (\<lambda>_. False)) P"
  by (simp add: rad_wait_false_def subst_app_def subst_upd_def
      subst_id_def subst_aext_def fun_eq_iff lens_defs)

lemma rad_wait_false_A_commute:
  "(rad_wait_false \<circ> A) P = (A \<circ> rad_wait_false) P"
  by (simp add: rad_wait_false_as_state_subst A_state_subst)

text \<open>
  Distribution kit for @{const rad_wait_false}: the substitution passes
  through the propositional connectives, the design turnstile, and the
  @{term "ok\<^sup>>"} substitutions, and is idempotent.  Together these discharge
  the \<open>(?D \<^sub>f) = ?D\<close> obligations of operator closure proofs by @{method simp}.
\<close>

lemma rad_wait_false_idem: "((P \<^sub>f) \<^sub>f) = P \<^sub>f"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_not: "((\<not> P) \<^sub>f) = (\<not> P \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_conj: "((P \<and> Q) \<^sub>f) = (P \<^sub>f \<and> Q \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_disj: "((P \<or> Q) \<^sub>f) = (P \<^sub>f \<or> Q \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_impl: "((P \<longrightarrow> Q) \<^sub>f) = (P \<^sub>f \<longrightarrow> Q \<^sub>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_ok_false: "((P\<^sup>f) \<^sub>f) = ((P \<^sub>f)\<^sup>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_ok_true: "((P\<^sup>t) \<^sub>f) = ((P \<^sub>f)\<^sup>t)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_ok_out: "((ok\<^sup>> :: ('t::trace, 'e) reactive_angelic_design) \<^sub>f) = ok\<^sup>>"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def; pred_auto)

lemma rad_wait_false_design: "((P \<turnstile> Q) \<^sub>f) = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by (simp add: rad_wait_false_def design_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_true: "(true \<^sub>f) = true"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_false: "(false \<^sub>f) = false"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_ac_non_empty: "(ac_non_empty \<^sub>f) = ac_non_empty"
  by (simp add: rad_wait_false_def ac_non_empty_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_RA1_commute: "((RA1 P) \<^sub>f) = RA1 (P \<^sub>f)"
  by (simp add: rad_wait_false_def RA1_def fun_eq_iff Let_def
      rad_trace_extensions_def subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs;
      pred_auto)

(* Wait-false substitution affects the initial observation of the left
   operand.  The intermediate state supplied to the right operand is chosen
   afresh by full-alphabet angelic composition. *)
lemma rad_wait_false_aseq_ades: "((P ;;\<^sub>A\<^sub>D Q) \<^sub>f) = ((P \<^sub>f) ;;\<^sub>A\<^sub>D Q)"
  by (simp add: rad_wait_false_def aseq_ades_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemmas rad_wait_false_distrib =
  rad_wait_false_design rad_wait_false_not rad_wait_false_conj
  rad_wait_false_disj rad_wait_false_impl rad_wait_false_ok_false
  rad_wait_false_ok_true rad_wait_false_idem rad_wait_false_true
  rad_wait_false_false rad_wait_false_ac_non_empty
  rad_wait_false_RA1_commute rad_wait_false_aseq_ades

lemma PBMH_ades_wait_cond:
  "PBMH_ades (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (PBMH_ades P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    PBMH_ades Q)"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def expr_if_def
      fun_eq_iff lens_defs; pred_auto; blast)

lemma rad_wait_cond_PBMH_ades_closure [closure]:
  "\<lbrakk> P is PBMH_ades; Q is PBMH_ades \<rbrakk> \<Longrightarrow>
   (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) is PBMH_ades"
  by (simp add: Healthy_def' PBMH_ades_wait_cond)

lemma RA1_wait_cond:
  "RA1 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (RA1 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 Q)"
  by (simp add: RA1_def expr_if_def fun_eq_iff Let_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA2_wait_cond:
  "RA2 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (RA2 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 Q)"
  by (simp add: RA2_def expr_if_def fun_eq_iff Let_def lens_defs
      rad_zero_trace_def rad_wait_def astate.s_def
      des_vars.more\<^sub>L_def)

lemma RA2_not_wait_conj:
  "RA2 ((\<not> rad_wait_lens\<^sup><) \<and> X) =
   ((\<not> rad_wait_lens\<^sup><) \<and> RA2 X)"
proof -
  have "RA2 ((\<not> rad_wait_lens\<^sup><) \<and> X) =
      RA2 (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> X)"
    by (simp only: rad_wait_cond_false)
  also have "... = (RA2 false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 X)"
    by (simp only: RA2_wait_cond)
  also have "... = (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 X)"
    by (simp only: RA2_false)
  also have "... = ((\<not> rad_wait_lens\<^sup><) \<and> RA2 X)"
    by (simp only: rad_wait_cond_false)
  finally show ?thesis .
qed

subsection \<open>RA3: Waiting\<close>

(* Paper Definition 31. *)
definition RA3 ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA3 P \<equiv> (II_Rac \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)"

lemma RA3_eval:
  "RA3 P (x, z) \<longleftrightarrow>
   (if rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
    then II_Rac (x, z) else P (x, z))"
  by (simp add: RA3_def expr_if_def SEXP_def lens_defs
      rad_wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA3_idem: "RA3 (RA3 P) = RA3 P"
  by (simp add: RA3_def)

lemma RA3_Idempotent [closure]: "Idempotent RA3"
  by (simp add: Idempotent_def RA3_idem)

lemma RA3_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA3 P \<sqsubseteq> RA3 Q"
  by (simp add: RA3_def, pred_auto)

lemma RA3_Monotonic [closure]: "Monotonic RA3"
  by (rule MonotonicI, rule RA3_mono)

(* Thesis Theorem T.G.3.3. *)
lemma RA3_II_Rac: "RA3 II_Rac = II_Rac"
  by (simp add: RA3_def)

lemma II_Rac_is_RA3 [closure]: "II_Rac is RA3"
  by (rule Healthy_intro, rule RA3_II_Rac)

(* Thesis Theorem T.5.2.12. *)
lemma RA3_conj: "RA3 (P \<and> Q) = (RA3 P \<and> RA3 Q)"
  by (simp add: RA3_def expr_if_def fun_eq_iff; pred_auto)

(* Thesis Theorem T.5.2.13. *)
lemma RA3_disj: "RA3 (P \<or> Q) = (RA3 P \<or> RA3 Q)"
  by (simp add: RA3_def expr_if_def fun_eq_iff; pred_auto)

lemma RA3_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "RA3 P is PBMH_ades"
  using assms
  by (simp add: Healthy_def' RA3_def PBMH_ades_wait_cond)

(* Thesis Theorem T.5.2.15. *)
lemma PBMH_ades_RA3_absorb:
  "(PBMH_ades \<circ> RA3 \<circ> PBMH_ades) P = (RA3 \<circ> PBMH_ades) P"
  using RA3_PBMH_ades_closure[of "PBMH_ades P"]
  by (simp add: Healthy_def' PBMH_ades_idem)

(* Paper Theorem 68.  The paper's theorem statement repeats
   RA3 \<circ> RA1 on both sides, but its proof establishes this commutation law. *)
theorem RA1_RA3_commute: "(RA1 \<circ> RA3) P = (RA3 \<circ> RA1) P"
  by (simp add: RA3_def RA1_wait_cond RA1_II_Rac)

(* Paper Theorem 69 *)
theorem RA2_RA3_commute: "(RA2 \<circ> RA3) P = (RA3 \<circ> RA2) P"
  by (simp add: RA3_def RA2_wait_cond RA2_II_Rac)

lemmas RA1_RA3_commute' = RA1_RA3_commute[simplified comp_apply]
lemmas RA2_RA3_commute' = RA2_RA3_commute[simplified comp_apply]

(* The three components of RA pairwise commute; cite this bundle when a
   proof only reassociates them. *)
lemmas RA_comms = RA1_RA2_commute' RA1_RA3_commute' RA2_RA3_commute'

(* Paper Lemma 19 *)
lemma RA3_wait_false_absorb: "RA3 P = (RA3 \<circ> rad_wait_false) P"
  apply (simp add: RA3_def rad_wait_false_def expr_if_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def)
  apply clarify
  subgoal for x z
    by (cases "astate.s\<^sub>v (des_vars.more x)";
        cases "des_vars.more x"; cases x;
        simp add: lens_defs rad_wait_def astate.s_def
          des_vars.more\<^sub>L_def)
  done

subsection \<open>RA\<close>

(* Paper Definition 32. *)
definition RA ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA \<equiv> RA1 \<circ> RA2 \<circ> RA3"

lemma RA_idem: "RA (RA P) = RA P"
  by (simp add: RA_def RA_comms RA1_idem RA2_idem RA3_idem)

lemma RA_Idempotent [closure]: "Idempotent RA"
  by (simp add: Idempotent_def RA_idem)

lemma RA_healthy [closure]: "RA P is RA"
  by (simp add: Healthy_def' RA_idem)

lemma RA_mono: "P \<sqsubseteq> Q \<Longrightarrow> RA P \<sqsubseteq> RA Q"
  by (simp add: RA_def RA1_mono RA2_mono RA3_mono)

lemma RA_Monotonic [closure]: "Monotonic RA"
  unfolding RA_def
  by (intro Monotonic_comp RA1_Monotonic RA2_Monotonic RA3_Monotonic)

lemma RA_is_RA2:
  assumes "P is RA"
  shows "P is RA2"
proof -
  have h: "RA1 (RA2 (RA3 P)) = P"
    using assms by (simp add: Healthy_def' RA_def)
  have "RA2 (RA1 (RA3 P)) = RA1 (RA2 (RA3 P))"
    by (rule RA1_RA2_commute'[symmetric])
  also have "... = P" by (rule h)
  finally have "RA2 (RA1 (RA3 P)) = P" .
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[where F = RA2, OF RA2_idem])
qed

lemma RA_is_RA3:
  assumes "P is RA"
  shows "P is RA3"
proof -
  have h: "RA1 (RA2 (RA3 P)) = P"
    using assms by (simp add: Healthy_def' RA_def)
  have "RA3 (RA1 (RA2 P)) = RA1 (RA3 (RA2 P))"
    by (simp only: RA1_RA3_commute'[symmetric])
  also have "... = RA1 (RA2 (RA3 P))"
    by (simp only: RA2_RA3_commute'[symmetric])
  also have "... = P" by (rule h)
  finally have "RA3 (RA1 (RA2 P)) = P" .
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[where F = RA3, OF RA3_idem])
qed

lemma RA_as_RA1_RA3_RA2: "RA P = RA1 (RA3 (RA2 P))"
  by (simp add: RA_def RA2_RA3_commute'[symmetric])

lemma RA_PBMH_ades_closure [closure]:
  assumes "P is PBMH_ades"
  shows "RA P is PBMH_ades"
  unfolding RA_def comp_apply
  by (intro RA1_PBMH_ades_closure RA2_PBMH_ades_closure
      RA3_PBMH_ades_closure assms)

lemma PBMH_ades_RA_absorb:
  "(PBMH_ades \<circ> RA \<circ> PBMH_ades) P = (RA \<circ> PBMH_ades) P"
  using RA_PBMH_ades_closure[of "PBMH_ades P"]
  by (simp add: Healthy_def' PBMH_ades_idem)

lemma RA_conj: "RA (P \<and> Q) = (RA P \<and> RA Q)"
  by (simp add: RA_def RA1_conj RA2_conj RA3_conj)

lemma RA_disj: "RA (P \<or> Q) = (RA P \<or> RA Q)"
  by (simp add: RA_def RA1_disj RA2_disj RA3_disj)

(* The components of RA commute, so RA may be recomposed in any order. *)
lemma RA_def': "RA P = RA3 (RA2 (RA1 P))"
  by (simp add: RA_def RA_comms)

lemma RA_RA2_RA1_absorb: "RA (RA2 (RA1 P)) = RA P"
  by (simp add: RA_def RA_comms RA1_idem RA2_idem)

lemma RA_cong_ac_non_empty:
  assumes "(ac_non_empty \<and> P) = (ac_non_empty \<and> Q)"
  shows "RA P = RA Q"
  using arg_cong[where f=RA1, OF assms]
  by (simp only: RA1_ac_non_empty_absorb RA_def')

lemma RA_ac_non_empty_absorb: "(ac_non_empty \<and> RA P) = RA P"
  by (simp add: RA_def comp_apply RA1_def ac_non_empty_def
      fun_eq_iff Let_def; pred_auto)

lemma RA_A1: "(RA \<circ> A) P = (RA \<circ> A1) P"
  by (simp add: RA_def A_def RA_comms RA1_A0_absorb)

(* Paper Theorem 67 *)
theorem RA_A:
  assumes "P is \<^bold>H"
  shows "(RA \<circ> A) P = (RA \<circ> PBMH_ades) P"
  by (simp add: RA_A1[simplified comp_apply]
      A1_eq_PBMH_ades[OF assms])

lemmas RA_A' = RA_A[simplified comp_apply]

lemma RA_A_absorb:
  assumes "P is PBMH_ades" "P is \<^bold>H"
  shows "(RA \<circ> A) P = RA P"
  by (simp only: comp_apply RA_A'[OF assms(2)] Healthy_if[OF assms(1)])

subsection \<open>CSPA1\<close>

(* Paper definition 33. *)
definition CSPA1 :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "CSPA1 P \<equiv> (P \<or> RA1 (\<not> ok\<^sup><))"

lemma CSPA1_obs:
  "CSPA1 P (ades_obs ok0 s0 ok' X) =
    (P (ades_obs ok0 s0 ok' X) \<or>
      (\<not> ok0 \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}))"
  by (simp add: CSPA1_def RA1_not_ok_eval; pred_auto)

lemma CSPA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA1 P \<sqsubseteq> CSPA1 Q"
  by (simp add: CSPA1_def, pred_auto)

lemma CSPA1_Monotonic [closure]: "Monotonic CSPA1"
  by (rule MonotonicI, rule CSPA1_mono)

(* Thesis Theorem T.G.5.1. *)
lemma CSPA1_idem: "CSPA1 (CSPA1 P) = CSPA1 P"
  by (simp add: CSPA1_def fun_eq_iff; pred_auto)

lemma CSPA1_Idempotent [closure]: "Idempotent CSPA1"
  by (simp add: Idempotent_def CSPA1_idem)

(* Thesis Theorem T.5.2.19. *)
lemma CSPA1_PBMH_ades_closure:
  assumes "PBMH_ades P = P"
  shows "PBMH_ades (CSPA1 P) = CSPA1 P"
  by (simp add: CSPA1_def PBMH_ades_disj assms)

(* Paper Theorem 10. *)
theorem RA1_CSPA1: "(RA1 \<circ> CSPA1) P = (RA1 \<circ> H1) P"
  apply (simp add: CSPA1_def H1_def RA1_def Let_def)
  apply pred_auto
  done

(* Thesis Theorem T.5.2.18. *)
lemma CSPA1_RA1: "(CSPA1 \<circ> RA1) P = (RA1 \<circ> H1) P"
proof -
  have "(CSPA1 \<circ> RA1) P = (RA1 \<circ> CSPA1) P"
    by (simp add: CSPA1_def RA1_disj RA1_idem)
  also have "... = (RA1 \<circ> H1) P"
    by (rule RA1_CSPA1)
  finally show ?thesis .
qed

(* Thesis Theorem T.G.5.4. *)
lemma RA1_CSPA1_commute: "(RA1 \<circ> CSPA1) P = (CSPA1 \<circ> RA1) P"
  by (simp add: RA1_CSPA1[simplified comp_apply]
      CSPA1_RA1[simplified comp_apply])

lemma CSPA1_RA2_commute: "CSPA1 (RA2 P) = RA2 (CSPA1 P)"
  by (rule ades_obs_ext;
      simp add: CSPA1_obs RA2_obs' rad_normalise_choices_nonempty
        rad_zero_trace_extensions)

lemma CSPA1_RA3_commute: "CSPA1 (RA3 P) = RA3 (CSPA1 P)"
  by (rule ades_obs_ext;
      simp add: CSPA1_obs RA3_eval II_Rac_eval rad_trace_extensions_def;
      blast)

lemma RA_CSPA1: "(RA \<circ> CSPA1) P = (RA \<circ> H1) P"
  by (simp add: RA_def RA_comms RA1_CSPA1[simplified comp_apply])

subsection \<open>CSPA2\<close>

(* Paper Definition 34. *)
definition CSPA2 :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
where [pred]: "CSPA2 P \<equiv> H2 P"

lemma CSPA2_Monotonic [closure]: "Monotonic CSPA2"
  unfolding CSPA2_def
  by (rule Continuous_Monotonic[OF H2_Continuous])

lemma CSPA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA2 P \<sqsubseteq> CSPA2 Q"
  using CSPA2_Monotonic by (auto simp add: Monotonic_refine)

lemma CSPA2_idem: "CSPA2 (CSPA2 P) = CSPA2 P"
  by (simp add: CSPA2_def H2_idem)

lemma CSPA2_Idempotent [closure]: "Idempotent CSPA2"
  by (simp add: Idempotent_def CSPA2_idem)

lemma CSPA2_PBMH_ades_closure:
  assumes "PBMH_ades P = P"
  shows "PBMH_ades (CSPA2 P) = CSPA2 P"
  by (simp only: CSPA2_def H2_split PBMH_ades_disj PBMH_ades_conj_ok
      PBMH_ades_ok_false PBMH_ades_ok_true assms)

lemma rad_wait_false_H1_CSPA2_commute:
  "(rad_wait_false \<circ> H1 \<circ> CSPA2) P =
   (H1 \<circ> CSPA2 \<circ> rad_wait_false) P"
  by (simp add: CSPA2_def rad_wait_false_def H1_def H2_split fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemma CSPA2_not_ok:
  "CSPA2 ((\<not> ok\<^sup><) :: ('t::trace, 'e) reactive_angelic_design) = (\<not> ok\<^sup><)"
  by (simp add: CSPA2_def H2_split fun_eq_iff; pred_auto)

lemma CSPA2_RA1_commute: "CSPA2 (RA1 P) = RA1 (CSPA2 P)"
  by (simp add: CSPA2_def H2_split RA1_def fun_eq_iff Let_def; pred_auto; blast)

lemma CSPA2_RA2_commute: "CSPA2 (RA2 P) = RA2 (CSPA2 P)"
  by (rule ades_obs_ext; simp add: CSPA2_def H2_obs RA2_obs')

lemma CSPA2_RA3_commute: "CSPA2 (RA3 P) = RA3 (CSPA2 P)"
  by (simp add: CSPA2_def H2_split RA3_def II_Rac_def RA1_def expr_if_def
      fun_eq_iff Let_def; pred_auto; blast)

lemma CSPA2_CSPA1_commute: "CSPA2 (CSPA1 P) = CSPA1 (CSPA2 P)"
  by (simp only: CSPA1_def CSPA2_def H2_disj
      CSPA2_RA1_commute[unfolded CSPA2_def] CSPA2_not_ok[unfolded CSPA2_def])

end
