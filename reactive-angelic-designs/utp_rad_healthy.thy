section \<open>Reactive Angelic Design Healthiness Conditions\<close>

theory utp_rad_healthy
  imports utp_rad_core "UTP-Reactive.utp_rea_healths"
begin

subsection \<open>RA1: Trace extension\<close>

(* Paper Definition 27. *)
definition rad_trace_extensions :: "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state set" where
"rad_trace_extensions x =
  {z. rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v z}"

(* Paper Definition 28. *)
(* RA1(P)(x, A) = P(x, rad_trace_extension(x) \<inter> A) ∧ A' \<noteq> \<emptyset> *)
definition RA1 ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA1 P = (\<lambda> (x, y).
  let x_state = des_vars.more x;
      y_choices = des_vars.more y;
      s0 = astate.s\<^sub>v x_state;
      A = achoices.ac\<^sub>v y_choices;
      A' = rad_trace_extensions s0 \<inter> A;
      y_choices' = achoices.ac\<^sub>v_update (\<lambda>_. A') y_choices;
      y' = des_vars.more_update (\<lambda>_. y_choices') y
  in P (x, y') \<and> A' \<noteq> {})"

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
  "(RA1 P)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> = RA1 (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: RA1_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

(* A design ignores its postcondition when it has not started, so a
   not-started disjunct under RA1 is redundant. *)
lemma design_true_RA1_not_ok:
  "(true \<turnstile> RA1 ((\<not> ok\<^sup><) \<or> X)) = (true \<turnstile> RA1 X)"
proof -
  have inner:
      "((\<not> ok\<^sup><) \<or> X)\<lbrakk>True/ok\<^sup><\<rbrakk> = X\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp add: usubst usubst_eval; pred_auto)
  have "(true \<turnstile> RA1 ((\<not> ok\<^sup><) \<or> X)) =
      (true\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile>
       (RA1 ((\<not> ok\<^sup><) \<or> X))\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (rule sym, rule design_subst_ok)
  also have "... =
      (true\<lbrakk>True/ok\<^sup><\<rbrakk> \<turnstile> (RA1 X)\<lbrakk>True/ok\<^sup><\<rbrakk>)"
    by (simp only: RA1_ok_in_subst inner)
  also have "... = (true \<turnstile> RA1 X)"
    by (rule design_subst_ok)
  finally show ?thesis .
qed

(* H1 discards the not-started behaviour that RA1 adds to a design,
   leaving RA1 enforced on both components. *)
lemma H1_RA1_design_gen:
  "H1 (RA1 (P \<turnstile> Q)) = ((\<not> RA1 (\<not> P)) \<turnstile> RA1 Q)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto)

lemma H1_RA1_design: "H1 (RA1 (true \<turnstile> X)) = (true \<turnstile> RA1 X)"
  by (simp only: H1_RA1_design_gen pred_ba.compl_top_eq RA1_false
      pred_ba.compl_bot_eq)

lemma RA1_ok_out_subst:
  "(RA1 P)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk> = RA1 (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup>>\<rbrakk>)"
  by (simp add: RA1_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

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

(* The extra RA1 that H1 leaves on the components of an RA1-healthy
   design is reabsorbed by RA1. *)
lemma RA1_H1_RA1_design:
  "RA1 (H1 (RA1 (P \<turnstile> Q))) = RA1 (P \<turnstile> Q)"
  by (simp only: H1_RA1_design_gen RA1_design_post[symmetric]
      RA1_design_pre[symmetric])

lemma RA1_Idempotent [closure]: "Idempotent RA1"
  by (simp add: Idempotent_def RA1_idem)

lemma RA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA1 P \<sqsubseteq> RA1 Q"
  by (auto simp add: RA1_def pred_refine_iff Let_def split: prod.splits)

lemma RA1_Monotonic [closure]: "Monotonic RA1"
  by (rule MonotonicI, rule RA1_mono)

(* Paper Theorem 9. *)
theorem RA1_A0_absorb: "RA1 (A0 P) = RA1 P"
  by (simp add: RA1_def A0_def ac_non_empty_def fun_eq_iff Let_def;
      pred_auto)

(* RA1 absorbs the A0 non-emptiness requirement. *)
lemma RA1_ac_non_empty_absorb: "RA1 (ac_non_empty \<and> P) = RA1 P"
  by (simp add: RA1_def ac_non_empty_def fun_eq_iff Let_def;
      pred_auto)

(* Arguments of RA1 may be rewritten under the non-emptiness
   assumption. *)
lemma RA1_cong_ac_non_empty:
  assumes "(ac_non_empty \<and> P) = (ac_non_empty \<and> Q)"
  shows "RA1 P = RA1 Q"
  using arg_cong[where f=RA1, OF assms]
  by (simp only: RA1_ac_non_empty_absorb)

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
  fix s
  assume ra1: "RA1 P s"
  obtain x y where s: "s = (x, y)" by (cases s)
  let ?A' = "rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
             achoices.ac\<^sub>v (des_vars.more y)"
  let ?y = "des_vars.more_update
              (\<lambda>_. achoices.ac\<^sub>v_update (\<lambda>_. ?A') (des_vars.more y)) y"
  have "P (x, ?y)"
    using ra1 by (simp add: s RA1_def Let_def)
  then have "P (x, y)"
    by (rule PBMH_ades_upward[OF assms]; simp)
  then show "P s" by (simp add: s)
qed

lemma PBMH_ades_RA1_not_ok [simp]:
  "PBMH_ades (RA1 (\<not> ok\<^sup><)) = RA1 (\<not> ok\<^sup><)"
  using PBMH_ades_RA1_absorb[of "(\<not> ok\<^sup><)"]
  by simp

(* Paper Example 11.  RA1 and PBMH_ades do not commute in general;
   PBMH_ades is the lifting of the paper's PBMH through the outer design
   record. *)
definition rad_ac_empty :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "rad_ac_empty = (\<lambda> (x, y).
  achoices.ac\<^sub>v (des_vars.more y) = {})"

lemma PBMH_ades_ac_empty [simp]: "PBMH_ades rad_ac_empty = true"
  by (simp add: PBMH_ades_def rad_ac_empty_def; pred_auto)

lemma RA1_ac_empty [simp]: "RA1 rad_ac_empty = false"
  by (simp add: RA1_def rad_ac_empty_def fun_eq_iff; pred_auto)

lemma RA1_PBMH_ades_ac_empty: "RA1 (PBMH_ades rad_ac_empty) = RA1 true"
  by simp

lemma PBMH_ades_RA1_ac_empty: "PBMH_ades (RA1 rad_ac_empty) = false"
  by (simp add: PBMH_ades_def; pred_auto)

lemma RA1_PBMH_ades_not_commute:
  "RA1 (PBMH_ades rad_ac_empty) \<noteq> PBMH_ades (RA1 rad_ac_empty)"
  by (simp only: RA1_PBMH_ades_ac_empty PBMH_ades_RA1_ac_empty;
      simp add: RA1_def rad_trace_extensions_def fun_eq_iff; pred_auto)

(* Thesis Lemma L.G.1.29: an aborted first process followed by anything
   yields the aborted behaviour. *)
lemma RA1_not_ok_aseq_absorb:
  "(RA1 (\<not> ok\<^sup><) ;;\<^sub>A\<^sub>D RA1 true) = RA1 (\<not> ok\<^sup><)"
  apply (simp add: RA1_def aseq_ades_def fun_eq_iff Let_def)
  apply pred_auto
   apply (blast dest: rad_trace_extensions_trans)
  apply (blast intro: rad_trace_extensions_refl)
  done

(* Thesis Lemma L.G.1.16: composition preserves RA1 healthiness. *)
lemma RA1_aseq_absorb:
  "RA1 (RA1 P ;;\<^sub>A\<^sub>D RA1 Q) = (RA1 P ;;\<^sub>A\<^sub>D RA1 Q)"
  apply (simp add: RA1_def aseq_ades_def fun_eq_iff Let_def)
  apply (simp add: rad_trace_extensions_Int_Collect
      rad_trace_extensions_inter_absorb cong: conj_cong)
  apply (auto dest: rad_trace_extensions_trans)
  done

subsection \<open>RA2: Trace-history independence\<close>

(* s \<oplus> {tr ↦ 0} *)
definition rad_zero_trace :: "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state" where
"rad_zero_trace s0 =
  rad_state.tr\<^sub>v_update (\<lambda>_. 0) s0"

(* z \<oplus> {tr ↦ z.tr - s.tr} *)
definition rad_trace_difference ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state" where
"rad_trace_difference s0 z =
  rad_state.tr\<^sub>v_update
    (\<lambda>_. rad_state.tr\<^sub>v z - rad_state.tr\<^sub>v s0) z"

(* { z[(z.tr-s.tr) / tr] | z \<in> ac' ∧ s.tr \<le> z.tr } *)
definition rad_normalise_choices ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state set \<Rightarrow> ('t, 'e) rad_state set" where
"rad_normalise_choices s0 ac' =
  {rad_trace_difference s0 z | z.
    z \<in> ac' \<and>
    rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z}"

lemma rad_normalise_choices_mono:
  "choices \<subseteq> choices' \<Longrightarrow>
   rad_normalise_choices s0 choices \<subseteq>
   rad_normalise_choices s0 choices'"
  by (auto simp add: rad_normalise_choices_def)

lemma rad_trace_update_self [simp]:
  "rad_state.tr\<^sub>v_update (\<lambda>_. rad_state.tr\<^sub>v z) z = z"
  by (cases z) simp

(* Normalising is the inverse image of prepending the initial trace. *)
lemma rad_normalise_choices_as_prepend:
  "rad_normalise_choices s0 X =
   {m. rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m \<in> X}"
  apply (rule Set.set_eqI)
  apply (auto simp add: rad_normalise_choices_def
      rad_trace_difference_def comp_def diff_add_cancel_left'
      intro!: exI[where x =
        "rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) x" for x])
  done

lemma rad_trace_append_assoc:
  "(\<lambda>x. t + (u + x)) = ((+) (t + u))" for t :: "'t::trace"
  by (auto simp add: fun_eq_iff add.assoc)

(* Paper Definition 29. *)
(* RA2(P)(s,ac') = P(s[0/tr], rad_normalise_choices(s, ac')) *)
definition RA2 ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
where [pred]: "RA2 P = (\<lambda> (x, y).
  let x_state = des_vars.more x;
      y_choices = des_vars.more y;
      s0 = astate.s\<^sub>v x_state;
      ac' = achoices.ac\<^sub>v y_choices;
      ac'' = rad_normalise_choices s0 ac';
      x_state' = astate.s\<^sub>v_update
        (\<lambda>_. rad_zero_trace s0) x_state;
      y_choices' = achoices.ac\<^sub>v_update (\<lambda>_. ac'') y_choices;
      x' = des_vars.more_update (\<lambda>_. x_state') x;
      y' = des_vars.more_update (\<lambda>_. y_choices') y
  in P (x', y'))"

lemma RA2_idem: "RA2 (RA2 P) = RA2 P"
  by (simp add: RA2_def rad_zero_trace_def rad_normalise_choices_def
      rad_trace_difference_def fun_eq_iff)

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
      comp_def rad_normalise_choices_as_prepend rad_zero_trace_def)

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
  "(RA2 P)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> = RA2 (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: RA2_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

lemma RA2_Idempotent [closure]: "Idempotent RA2"
  by (simp add: Idempotent_def RA2_idem)

lemma rad_normalise_choices_extensions:
  "rad_normalise_choices s0 (rad_trace_extensions s0 \<inter> choices) =
   rad_normalise_choices s0 choices"
  by (auto simp add: rad_normalise_choices_def rad_trace_extensions_def)

lemma rad_normalise_choices_nonempty:
  "rad_normalise_choices s0 choices \<noteq> {} \<longleftrightarrow>
   rad_trace_extensions s0 \<inter> choices \<noteq> {}"
  by (auto simp add: rad_normalise_choices_def rad_trace_extensions_def)

lemma rad_zero_trace_extensions:
  "rad_trace_extensions (rad_zero_trace s0) \<inter>
   rad_normalise_choices s0 choices =
   rad_normalise_choices s0 choices"
  by (auto simp add: rad_trace_extensions_def rad_zero_trace_def
      rad_normalise_choices_def rad_trace_difference_def)

lemma rad_zero_trace_in_normalise:
  "rad_zero_trace s0 \<in> rad_normalise_choices s0 choices \<longleftrightarrow>
   s0 \<in> choices"
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

(* Conjoining RA1 true with an RA2 image enforces RA1 inside it. *)
lemma RA1_true_conj_RA2: "(RA1 true \<and> RA2 P) = RA2 (RA1 P)"
proof -
  have "RA2 (RA1 P) = (RA2 P \<and> RA2 ac_non_empty)"
    by (simp only: RA2_ac_non_empty[symmetric] RA2_conj)
  then show ?thesis
    by (simp only: RA2_ac_non_empty_eq pred_ba.inf_commute)
qed

(* Under RA1 true, a disjunct absorbed by B on the inside is absorbed
   by the RA2 \<circ> RA1 image of B. *)
lemma RA2_RA1_disj_absorb:
  assumes "(X \<or> Y) = Y"
  shows "(RA1 true \<and> (RA2 X \<or> RA2 (RA1 Y))) = RA2 (RA1 Y)"
proof -
  have "(RA1 true \<and> (RA2 X \<or> RA2 (RA1 Y))) =
      ((RA1 true \<and> RA2 X) \<or> (RA1 true \<and> RA2 (RA1 Y)))"
    by (simp only: pred_ba.boolean_algebra.conj_disj_distrib)
  also have "... = (RA2 (RA1 X) \<or> RA2 (RA1 Y))"
    by (simp only: RA1_true_conj_RA2 RA1_idem)
  also have "... = RA2 (RA1 (X \<or> Y))"
    by (simp only: RA2_disj[symmetric] RA1_disj[symmetric])
  finally show ?thesis
    by (simp only: assms)
qed

lemma RA1_RA2_ac_non_empty: "RA1 (RA2 ac_non_empty) = RA1 true"
proof -
  have absorb: "RA1 ac_non_empty = RA1 true"
    by (rule RA1_cong_ac_non_empty, pred_auto)
  have "RA1 (RA2 ac_non_empty) = RA2 (RA1 true)"
    by (simp only: RA1_RA2_commute' absorb)
  also have "... = RA1 (RA2 true)"
    by (rule RA1_RA2_commute'[symmetric])
  finally show ?thesis
    by (simp only: RA2_true)
qed

(* Thesis Theorem T.G.2.4: RA2 distributes through full-alphabet angelic
   composition when the right operand is already RA2-normalised. *)
lemma RA2_aseq_distrib:
  "RA2 (P ;;\<^sub>A\<^sub>D RA2 Q) = (RA2 P ;;\<^sub>A\<^sub>D RA2 Q)"
  by (simp add: RA2_def aseq_ades_def Let_def fun_eq_iff comp_def
      rad_normalise_choices_as_prepend rad_zero_trace_def
      rad_trace_append_assoc)

(* A reusable form of the RA2 transport used by reactive sequential
   composition: commute RA1 and RA2 on both operands in one step. *)
lemma RA2_RA1_aseq_distrib:
  "RA2 (RA1 P ;;\<^sub>A\<^sub>D RA2 (RA1 Q)) =
   (RA1 (RA2 P) ;;\<^sub>A\<^sub>D RA1 (RA2 Q))"
proof -
  have "RA2 (RA1 P ;;\<^sub>A\<^sub>D RA2 (RA1 Q)) =
      (RA2 (RA1 P) ;;\<^sub>A\<^sub>D RA2 (RA1 Q))"
    by (rule RA2_aseq_distrib)
  also have "... =
      (RA1 (RA2 P) ;;\<^sub>A\<^sub>D RA1 (RA2 Q))"
    by (simp only: RA1_RA2_commute'[symmetric])
  finally show ?thesis .
qed

(* Paper Theorem 66 *)
theorem PBMH_ades_RA2_absorb:
  "(PBMH_ades \<circ> RA2 \<circ> PBMH_ades) P = (RA2 \<circ> PBMH_ades) P"
  apply (simp add: PBMH_ades_def RA2_def fun_eq_iff)
  apply pred_auto
  subgoal for ok tr ref wait ok' ac ac' ac''
    apply (rule exI[where x=ac''])
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

lemma RA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA2 P \<sqsubseteq> RA2 Q"
  by (auto simp add: RA2_def pred_refine_iff Let_def split: prod.splits)

lemma RA2_Monotonic [closure]: "Monotonic RA2"
  by (rule MonotonicI, rule RA2_mono)

subsection \<open>The reactive identity\<close>

(* Paper Definition 30. Rac identity *)
definition II_Rac :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "II_Rac = (\<lambda> (x, y).
  let s0 = astate.s\<^sub>v (des_vars.more x);
      A = achoices.ac\<^sub>v (des_vars.more y)
  in RA1 (\<not> ok\<^sup><) (x, y) \<or> (ok\<^sub>v y \<and> s0 \<in> A))"

(* Thesis Theorems T.G.3.1, T.G.3.2, and T.G.3.4. *)
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
      "II_Rac =
       (RA1 (\<not> ok\<^sup><) \<or>
        (\<lambda> (x, y). ok\<^sub>v y \<and>
          astate.s\<^sub>v (des_vars.more x) \<in>
          achoices.ac\<^sub>v (des_vars.more y)))"
    by (simp add: II_Rac_def fun_eq_iff Let_def; pred_auto)
  have state_healthy:
      "PBMH_ades (\<lambda> (x, y). ok\<^sub>v y \<and>
          astate.s\<^sub>v (des_vars.more x) \<in>
          achoices.ac\<^sub>v (des_vars.more y)) =
       (\<lambda> (x, y). ok\<^sub>v y \<and>
          astate.s\<^sub>v (des_vars.more x) \<in>
          achoices.ac\<^sub>v (des_vars.more y))"
    by (simp add: PBMH_ades_def PBMH_def pbmh_step_def fun_eq_iff;
        pred_auto; blast)
  show ?thesis
    by (simp add: split PBMH_ades_disj state_healthy)
qed

lemma II_Rac_is_PBMH_ades [closure]: "II_Rac is PBMH_ades"
  by (rule Healthy_intro, rule PBMH_ades_II_Rac)

subsection \<open>Wait-false substitution\<close>

abbreviation rad_wait_lens where
"rad_wait_lens \<equiv>
  rad_state.wait ;\<^sub>L astate.s ;\<^sub>L des_vars.more\<^sub>L"

(* P_f \<equiv> P[s\<oplus>(wait ↦ false)/s] *)
definition rad_wait_false ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "rad_wait_false P = P\<lbrakk>False/rad_wait_lens\<^sup><\<rbrakk>"

notation rad_wait_false ("_\<^sub>wf" [1000] 1000)

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
  "((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> =
   (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    Q\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: expr_if_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_atom_ok_in_subst [usubst]:
  "((rad_wait_lens\<^sup><) ::
    ('t::trace, 'e) reactive_angelic_design)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> =
   (rad_wait_lens\<^sup><)"
  by (simp add: fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_as_state_subst:
  "rad_wait_false P =
   ades_state_subst
     (subst_upd subst_id (rad_state.wait ;\<^sub>L astate.s) (\<lambda>_. False)) P"
  by (simp add: rad_wait_false_def subst_app_def subst_upd_def
      subst_id_def subst_aext_def fun_eq_iff lens_defs)

lemma rad_wait_false_A_commute:
  "(rad_wait_false \<circ> A) P = (A \<circ> rad_wait_false) P"
  by (simp add: rad_wait_false_as_state_subst A_state_subst)

lemma rad_wait_false_H1_H2_commute:
  "(rad_wait_false \<circ> H1 \<circ> H2) P =
   (H1 \<circ> H2 \<circ> rad_wait_false) P"
  by (simp add: rad_wait_false_def H1_def H2_split fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

text \<open>
  Distribution kit for @{const rad_wait_false}: the substitution passes
  through the propositional connectives, the design turnstile, and the
  @{term "ok\<^sup>>"} substitutions, and is idempotent.  Together these discharge
  the \<open>(?D \<^sub>wf) = ?D\<close> obligations of operator closure proofs by @{method simp}.
\<close>

lemma rad_wait_false_idem: "((P \<^sub>wf) \<^sub>wf) = P \<^sub>wf"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_not: "((\<not> P) \<^sub>wf) = (\<not> P \<^sub>wf)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_conj:
  "((P \<and> Q) \<^sub>wf) = (P \<^sub>wf \<and> Q \<^sub>wf)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_disj:
  "((P \<or> Q) \<^sub>wf) = (P \<^sub>wf \<or> Q \<^sub>wf)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_impl:
  "((P \<longrightarrow> Q) \<^sub>wf) = (P \<^sub>wf \<longrightarrow> Q \<^sub>wf)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_ok_false:
  "((P\<^sup>f) \<^sub>wf) = ((P \<^sub>wf)\<^sup>f)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_ok_true:
  "((P\<^sup>t) \<^sub>wf) = ((P \<^sub>wf)\<^sup>t)"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs)

lemma rad_wait_false_ok_out:
  "((ok\<^sup>> :: ('t::trace, 'e) reactive_angelic_design) \<^sub>wf) = ok\<^sup>>"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def; pred_auto)

lemma rad_wait_false_design:
  "((P \<turnstile> Q) \<^sub>wf) = ((P \<^sub>wf) \<turnstile> (Q \<^sub>wf))"
  by (simp add: rad_wait_false_def design_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_true: "(true \<^sub>wf) = true"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_false: "(false \<^sub>wf) = false"
  by (simp add: rad_wait_false_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def; pred_auto)

lemma rad_wait_false_ac_non_empty: "(ac_non_empty \<^sub>wf) = ac_non_empty"
  by (simp add: rad_wait_false_def ac_non_empty_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs; pred_auto)

lemma rad_wait_false_RA1_commute:
  "((RA1 P) \<^sub>wf) = RA1 (P \<^sub>wf)"
  by (simp add: rad_wait_false_def RA1_def fun_eq_iff Let_def
      rad_trace_extensions_def subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs;
      pred_auto)

(* Wait-false substitution affects the initial observation of the left
   operand.  The intermediate state supplied to the right operand is chosen
   afresh by full-alphabet angelic composition. *)
lemma rad_wait_false_aseq_ades:
  "((P ;;\<^sub>A\<^sub>D Q) \<^sub>wf) = ((P \<^sub>wf) ;;\<^sub>A\<^sub>D Q)"
  by (simp add: rad_wait_false_def aseq_ades_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemmas rad_wait_false_distrib =
  rad_wait_false_design rad_wait_false_not rad_wait_false_conj
  rad_wait_false_disj rad_wait_false_impl rad_wait_false_ok_false
  rad_wait_false_ok_true rad_wait_false_idem rad_wait_false_true
  rad_wait_false_false rad_wait_false_ac_non_empty
  rad_wait_false_RA1_commute rad_wait_false_aseq_ades

lemma rad_wait_false_design_is_H [closure]:
  "((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t) is \<^bold>H"
  by (rule design_is_H1_H2; pred_auto)

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

subsection \<open>RA3: Waiting\<close>

(* Paper Definition 31. *)
definition RA3 ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA3 P = (II_Rac \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)"

lemma RA1_wait_cond:
  "RA1 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (RA1 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 Q)"
  by (simp add: RA1_def expr_if_def fun_eq_iff Let_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA2_wait_cond:
  "RA2 (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (RA2 P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 Q)"
  by (simp add: RA2_def expr_if_def fun_eq_iff Let_def lens_defs
      rad_zero_trace_def rad_state.wait_def astate.s_def
      des_vars.more\<^sub>L_def)

lemma II_Rac_design:
  "II_Rac = RA1 (true \<turnstile> ades_state_choice)"
  by (simp add: II_Rac_def RA1_def design_def ades_state_choice_def
      fun_eq_iff Let_def SEXP_def lens_defs des_vars.ok_def;
      pred_auto; blast intro: rad_trace_extensions_refl)

lemma design_wait_cond:
  "((P \<turnstile> Q) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (R \<turnstile> S)) =
   ((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> R) \<turnstile>
    (Q \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> S))"
  by (simp add: design_def expr_if_def fun_eq_iff; pred_auto)

(* Thesis Lemma L.G.4.1: under RA1, RA3 turns a design into wait
   conditionals over its components. *)
lemma RA1_RA3_design:
  "RA1 (RA3 (P \<turnstile> Q)) =
   RA1 ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P) \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
proof -
  have "RA1 (RA3 (P \<turnstile> Q)) =
    (RA1 II_Rac \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 (P \<turnstile> Q))"
    by (simp only: RA3_def RA1_wait_cond)
  also have "... =
    (RA1 (true \<turnstile> ades_state_choice) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 (P \<turnstile> Q))"
    by (simp only: II_Rac_design RA1_idem)
  also have "... =
    RA1 ((true \<turnstile> ades_state_choice) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
         (P \<turnstile> Q))"
    by (simp only: RA1_wait_cond)
  also have "... =
    RA1 ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P) \<turnstile>
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q))"
    by (simp only: design_wait_cond)
  finally show ?thesis .
qed

lemma RA3_idem: "RA3 (RA3 P) = RA3 P"
  by (simp add: RA3_def)

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

lemma RA3_Idempotent [closure]: "Idempotent RA3"
  by (simp add: Idempotent_def RA3_idem)

(* Paper Theorem 68.  The paper's theorem statement repeats
   RA3 \<circ> RA1 on both sides, but its proof establishes this commutation law. *)
lemma RA1_RA3_commute: "(RA1 \<circ> RA3) P = (RA3 \<circ> RA1) P"
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
  subgoal for a b
    by (cases "astate.s\<^sub>v (des_vars.more a)";
        cases "des_vars.more a"; cases a;
        simp add: lens_defs rad_state.wait_def astate.s_def
          des_vars.more\<^sub>L_def)
  done

lemma RA3_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA3 P \<sqsubseteq> RA3 Q"
  by (simp add: RA3_def, pred_auto)

lemma RA3_Monotonic [closure]: "Monotonic RA3"
  by (rule MonotonicI, rule RA3_mono)

subsection \<open>RA\<close>

(* Paper Definition 32. *)
definition RA ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA = RA1 \<circ> RA2 \<circ> RA3"

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
lemma RA_alt_def: "RA P = RA3 (RA2 (RA1 P))"
  by (simp add: RA_def RA_comms)

lemma RA_design_components:
  "RA (P \<turnstile> Q) = RA ((\<not> RA1 (\<not> P)) \<turnstile> RA1 Q)"
proof -
  have "RA1 (P \<turnstile> Q) =
      RA1 ((\<not> RA1 (\<not> P)) \<turnstile> Q)"
    by (rule RA1_design_pre)
  also have "... =
      RA1 ((\<not> RA1 (\<not> P)) \<turnstile> RA1 Q)"
    by (rule RA1_design_post)
  finally show ?thesis
    by (simp only: RA_alt_def)
qed

(* Mapping an RA-healthy design through H1 and back through RA1 is the
   identity: RA is RA1-healthy, so RA1 reabsorbs what H1 adds. *)
lemma RA1_H1_RA_design:
  "RA1 (H1 (RA (P \<turnstile> Q))) = RA (P \<turnstile> Q)"
proof -
  have step: "RA (P \<turnstile> Q) =
      RA1 ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 P) \<turnstile>
           (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 Q))"
    by (simp only: RA_as_RA1_RA3_RA2 RA2_design_distrib RA1_RA3_design)
  show ?thesis
    by (simp only: step RA1_H1_RA1_design)
qed

(* The wait-conditional normal form of a reactive angelic design with a
   true precondition. *)
lemma RA_true_design:
  "RA (true \<turnstile> Post) =
   RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 Post))"
proof -
  have "RA (true \<turnstile> Post) = RA1 (RA3 (true \<turnstile> RA2 Post))"
    by (simp only: RA_as_RA1_RA3_RA2 RA2_design_distrib RA2_true)
  then show ?thesis
    by (simp only: RA1_RA3_design expr_if_idem)
qed

lemma RA_cong_ac_non_empty:
  assumes "(ac_non_empty \<and> P) = (ac_non_empty \<and> Q)"
  shows "RA P = RA Q"
  using arg_cong[where f=RA1, OF assms]
  by (simp only: RA1_ac_non_empty_absorb RA_alt_def)

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
proof -
  have "(RA \<circ> A) P = (RA \<circ> PBMH_ades) P"
    by (rule RA_A[OF assms(2)])
  also have "... = RA P"
    using assms(1) by (simp only: comp_apply Healthy_def')
  finally show ?thesis .
qed

(* RA_A_absorb specialised to designs: PBMH components and freshness of
   the final ok suffice for the design to satisfy the absorption
   premises. *)
lemma RA_A_absorb_design:
  assumes "(\<not> F) is PBMH_ades" "T is PBMH_ades"
    and "$ok\<^sup>> \<sharp> F" "$ok\<^sup>> \<sharp> T"
  shows "(RA \<circ> A) (F \<turnstile> T) = RA (F \<turnstile> T)"
proof -
  have "(F \<turnstile> T) is PBMH_ades"
    using PBMH_ades_design_closure[OF assms(1,2)]
    by (simp only: pred_ba.double_compl)
  then show ?thesis
    by (rule RA_A_absorb[OF _ design_is_H1_H2[OF assms(3,4)]])
qed

(* The common special case of a true precondition. *)
lemma RA_A_absorb_design_true:
  assumes "T is PBMH_ades" and "$ok\<^sup>> \<sharp> T"
  shows "(RA \<circ> A) (true \<turnstile> T) = RA (true \<turnstile> T)"
  by (rule RA_A_absorb_design[OF _ assms(1) _ assms(2)];
      simp add: pred_ba.compl_top_eq false_PBMH_ades unrest)

lemma RA_A_angelic_choice:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is PBMH_ades" "Q is PBMH_ades"
      "P is \<^bold>H" "Q is \<^bold>H"
  shows
    "(RA \<circ> A) P \<squnion> (RA \<circ> A) Q =
     (RA \<circ> A) (P \<squnion> Q)"
proof -
  have choice_PBMH: "(P \<squnion> Q) is PBMH_ades"
    using PBMH_ades_conj_closure[OF assms(1,2)]
    by (simp only: angelic_design_angelic)
  have choice_design: "(P \<squnion> Q) is \<^bold>H"
    using Inf_H1_H2_closed[of "{P, Q}"] assms(3,4)
    by simp
  show ?thesis
    by (simp only: RA_A_absorb[OF assms(1) assms(3)]
        RA_A_absorb[OF assms(2) assms(4)]
        RA_A_absorb[OF choice_PBMH choice_design],
        simp only: conj_pred_def[symmetric] RA_conj)
qed

lemma RA_A_demonic_choice:
  "(RA \<circ> A) P \<sqinter> (RA \<circ> A) Q = (RA \<circ> A) (P \<sqinter> Q)"
  by (simp only: angelic_design_demonic comp_apply A_disj RA_disj)

lemma RA_wait_false_ok_subst:
  "((rad_wait_false \<circ> RA) P) \<lbrakk>\<guillemotleft>ok_val\<guillemotright>/ok\<^sup>>\<rbrakk> =
   (RA2 \<circ> RA1)
     ((P \<^sub>wf) \<lbrakk>\<guillemotleft>ok_val\<guillemotright>/ok\<^sup>>\<rbrakk>)"
  apply (simp add: RA_def RA3_def rad_wait_false_def RA1_def RA2_def
      expr_if_def fun_eq_iff Let_def subst_app_def subst_upd_def
      subst_id_def SEXP_def)
  apply clarify
  subgoal for a b
    by (cases "astate.s\<^sub>v (des_vars.more a)";
        cases "des_vars.more a"; cases a;
        cases "des_vars.more b"; cases b;
        auto simp add: lens_defs des_vars.ok_def rad_state.wait_def astate.s_def
          des_vars.more\<^sub>L_def rad_trace_extensions_def
          rad_zero_trace_def rad_normalise_choices_def
          rad_trace_difference_def conj_commute conj_left_commute)
  done

lemmas RA_wait_false_ok_subst' =
  RA_wait_false_ok_subst[simplified comp_apply]

(* Paper Lemma 20 *)
(* (rad_wait_false (RA (A
     (\<not> (P \<^sub>wf)^f \<turnstile> (P \<^sub>wf)^t))))^f =
   RA2 \<circ> RA1 \<circ> PBMH (\<not> ok ∨ (P \<^sub>wf)^f) *)
lemma RA_design_wf_ok_false:
  "((rad_wait_false \<circ> RA \<circ> A)
      ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t))\<^sup>f =
   (RA2 \<circ> RA1 \<circ> PBMH_ades)
     ((\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f)"
proof -
  have pbmh_design:
    "(rad_wait_false
        (PBMH_ades ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)))\<^sup>f =
     PBMH_ades ((\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f)"
    apply (simp add: rad_wait_false_def PBMH_ades_def design_def fun_eq_iff
        subst_app_def subst_upd_def subst_id_def SEXP_def Let_def)
    apply (simp add: PBMH_def pbmh_step_def)
    apply pred_auto
    done
  show ?thesis
    unfolding comp_apply
    apply (subst RA_A')
     apply (rule design_is_H1_H2)
      apply pred_auto
     apply pred_auto
    apply (simp only: RA_wait_false_ok_subst' pbmh_design)
    done
qed

lemmas RA_design_wf_ok_false' = RA_design_wf_ok_false[simplified comp_apply]

(* Paper Lemma 21 *)
(* (RA \<circ> A(\<not>P^f_f \<turnstile> P^t_f))^t_f = RA2 \<circ> RA1 \<circ> PBMH(\<not>ok ∨ P^f_f ∨ P^t_f) *)
lemma RA_design_wf_ok_true:
  "((rad_wait_false \<circ> RA \<circ> A)
      ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t))\<^sup>t =
   (RA2 \<circ> RA1 \<circ> PBMH_ades)
     ((\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f \<or> (P \<^sub>wf)\<^sup>t)"
  unfolding comp_apply
  apply (subst RA_A')
   apply (rule design_is_H1_H2; pred_auto)
  apply (simp only: RA_wait_false_ok_subst')
  apply (rule arg_cong[where f=RA2])
  apply (rule arg_cong[where f=RA1])
  by (simp add: rad_wait_false_def PBMH_ades_def design_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def Let_def
      PBMH_def pbmh_step_def; pred_auto)

lemmas RA_design_wf_ok_true' = RA_design_wf_ok_true[simplified comp_apply]

(* Paper Lemma 22 *)
lemma RA_design_post:
  "RA (P \<turnstile> Q) = RA (P \<turnstile> (RA2 \<circ> RA1) Q)"
proof -
  have ra12_design:
      "RA2 (RA1 (P \<turnstile> Q)) =
       RA2 (RA1 (P \<turnstile> RA2 (RA1 Q)))"
    by (simp only: RA1_RA2_commute'[symmetric, of "P \<turnstile> Q"]
        RA2_design_distrib[of P Q]
        RA1_design_post[of "RA2 P" "RA2 Q"]
        RA1_RA2_commute'[of Q]
        RA1_RA2_commute'[symmetric, of "P \<turnstile> RA2 (RA1 Q)"]
        RA2_design_distrib[of P "RA2 (RA1 Q)"] RA2_idem[of "RA1 Q"])
  show ?thesis
    unfolding RA_def comp_apply
    by (simp only: RA_comms ra12_design)
qed

(* Under (RA \<circ> A) with a true precondition, a postcondition may be
   replaced by its RA2 \<circ> RA1 \<circ> PBMH_ades normalisation. *)
lemma RA_A_true_design_post:
  assumes "(true \<turnstile> Z) is \<^bold>H" and "(true \<turnstile> T) is \<^bold>H"
    and "RA2 (RA1 (PBMH_ades Z)) = T" and "PBMH_ades T = T"
  shows "(RA \<circ> A) (true \<turnstile> Z) = (RA \<circ> A) (true \<turnstile> T)"
proof -
  have push: "PBMH_ades (true \<turnstile> X) = (true \<turnstile> PBMH_ades X)" for X
    by (simp add: design_as_disj PBMH_ades_disj PBMH_ades_conj_ok)
  have "RA (A (true \<turnstile> Z)) = RA (true \<turnstile> PBMH_ades Z)"
    by (simp only: RA_A'[OF assms(1)] push)
  also have "... = RA (true \<turnstile> RA2 (RA1 (PBMH_ades Z)))"
    by (rule RA_design_post[simplified comp_apply])
  also have "... = RA (A (true \<turnstile> T))"
    by (simp only: assms(3) RA_A'[OF assms(2)] push assms(4))
  finally show ?thesis
    by (simp only: comp_apply)
qed

lemma RA_RA2_RA1_absorb: "RA (RA2 (RA1 P)) = RA P"
  by (simp add: RA_def RA_comms RA1_idem RA2_idem)

lemma PBMH_ades_RA2_RA1_absorb:
  "PBMH_ades (RA2 (RA1 (PBMH_ades P))) = RA2 (RA1 (PBMH_ades P))"
  using RA2_PBMH_ades_closure[OF RA1_PBMH_ades_closure[OF
      Healthy_Idempotent[OF PBMH_ades_Idempotent]]]
  by (simp add: Healthy_def')

lemma RA_RA2_RA1_PBMH_ades_conj_ok:
  "RA (RA2 (RA1 (PBMH_ades P)) \<and> ok\<^sup>>) =
   RA (PBMH_ades (P \<and> ok\<^sup>>))"
proof -
  have "RA (RA2 (RA1 (PBMH_ades P)) \<and> ok\<^sup>>) =
        RA (RA2 (RA1 (PBMH_ades P \<and> ok\<^sup>>)))"
    by (simp only: RA1_conj_ok RA2_conj_ok)
  also have "... = RA (RA2 (RA1 (PBMH_ades (P \<and> ok\<^sup>>))))"
    by (simp only: PBMH_ades_conj_ok)
  also have "... = RA (PBMH_ades (P \<and> ok\<^sup>>))"
    by (simp only: RA_RA2_RA1_absorb)
  finally show ?thesis .
qed

lemma RA_design_PBMH_normalise:
  "RA (PBMH_ades
      ((\<not> RA2 (RA1 (PBMH_ades ((\<not> ok\<^sup><) \<or> F)))) \<turnstile>
        RA2 (RA1 (PBMH_ades
          ((\<not> ok\<^sup><) \<or> F \<or> T))))) =
   RA (PBMH_ades ((\<not> F) \<turnstile> T))"
proof -
  let ?X = "(\<not> ok\<^sup><) \<or> F"
  let ?Z = "(\<not> ok\<^sup><) \<or> F \<or> T"
  let ?U = "RA2 (RA1 (PBMH_ades ?X))"
  let ?V = "RA2 (RA1 (PBMH_ades ?Z))"
  have U_healthy: "PBMH_ades ?U = ?U"
    by (simp only: PBMH_ades_RA2_RA1_absorb)
  have V_healthy: "PBMH_ades ?V = ?V"
    by (simp only: PBMH_ades_RA2_RA1_absorb)
  have absorb:
      "((\<not> ok\<^sup><) \<or> ?X \<or> (?Z \<and> ok\<^sup>>)) =
       ((\<not> ok\<^sup><) \<or> F \<or> (T \<and> ok\<^sup>>))"
    by pred_auto
  have "RA (PBMH_ades ((\<not> ?U) \<turnstile> ?V)) =
        RA (PBMH_ades
          ((\<not> ok\<^sup><) \<or> ?U \<or> (?V \<and> ok\<^sup>>)))"
    by (simp add: design_as_disj)
  also have "... = RA
      (PBMH_ades (\<not> ok\<^sup><) \<or> PBMH_ades ?U \<or>
        PBMH_ades (?V \<and> ok\<^sup>>))"
    by (simp only: PBMH_ades_disj)
  also have "... = RA
      ((\<not> ok\<^sup><) \<or> ?U \<or> (?V \<and> ok\<^sup>>))"
    by (simp only: PBMH_ades_not_ok_expr PBMH_ades_conj_ok
        U_healthy V_healthy)
  also have "... =
      (RA (\<not> ok\<^sup><) \<or> RA (PBMH_ades ?X) \<or>
        RA (PBMH_ades (?Z \<and> ok\<^sup>>)))"
    by (simp only: RA_disj RA_RA2_RA1_absorb[of "PBMH_ades ?X"]
        RA_RA2_RA1_PBMH_ades_conj_ok[of ?Z])
  also have "... = RA (PBMH_ades
      ((\<not> ok\<^sup><) \<or> ?X \<or> (?Z \<and> ok\<^sup>>)))"
    by (simp only: RA_disj PBMH_ades_disj PBMH_ades_not_ok_expr
        PBMH_ades_conj_ok)
  also have "... = RA (PBMH_ades
      ((\<not> ok\<^sup><) \<or> F \<or> (T \<and> ok\<^sup>>)))"
    by (simp only: absorb)
  also have "... = RA (PBMH_ades ((\<not> F) \<turnstile> T))"
    by (simp add: design_as_disj)
  finally show ?thesis .
qed

(* Thesis Theorem T.G.4.5. *)
lemma RA_design_form_idem:
  "(RA \<circ> A)
      ((\<not> (rad_wait_false
          ((RA \<circ> A)
            ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)))\<^sup>f) \<turnstile>
        (rad_wait_false
          ((RA \<circ> A)
            ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)))\<^sup>t) =
   (RA \<circ> A)
     ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  show ?thesis
    unfolding comp_apply
    apply (subst RA_A'[OF rad_wait_false_design_is_H])
    apply (simp only: RA_design_wf_ok_false'
        RA_design_wf_ok_true')
    apply (subst RA_design_PBMH_normalise)
    by (rule RA_A'[OF rad_wait_false_design_is_H, symmetric])
qed

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

end
