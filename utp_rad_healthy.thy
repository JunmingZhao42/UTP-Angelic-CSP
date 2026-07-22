section \<open>Reactive Angelic Healthiness Conditions\<close>

theory utp_rad_healthy
  imports utp_rad_core "UTP-Reactive.utp_rea_healths"
begin

subsection \<open>RA1: Trace extension\<close>

(* Paper Definition 27. *)
definition rad_trace_extensions :: "'e rad_state \<Rightarrow> 'e rad_state set" where
"rad_trace_extensions x =
  {z. rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v z}"

(* Paper Definition 28. *)
(* RA1(P)(x, A) = P(x, rad_trace_extension(x) \<inter> A) ∧ A' \<noteq> \<emptyset> *)
definition RA1 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
[pred]: "RA1 P = (\<lambda> (x, y).
  let x_state = des_vars.more x;
      y_choices = des_vars.more y;
      s0 = astate.s\<^sub>v x_state;
      A = achoices.ac\<^sub>v y_choices;
      A' = rad_trace_extensions s0 \<inter> A;
      y_choices' = achoices.ac\<^sub>v_update (\<lambda>_. A') y_choices;
      y' = des_vars.more_update (\<lambda>_. y_choices') y
  in P (x, y') \<and> A' \<noteq> {})"

lemma RA1_idem: "RA1 (RA1 P) = RA1 P"
  by (simp add: RA1_def rad_trace_extensions_def fun_eq_iff; blast)

lemma RA1_design_post:
  "RA1 (P \<turnstile> Q) = RA1 (P \<turnstile> RA1 Q)"
  by (simp add: RA1_def design_def fun_eq_iff Let_def; pred_auto; blast)

(* Thesis Theorem T.5.2.2. *)
lemma RA1_conj:
  "RA1 (P \<and> Q) = (RA1 P \<and> RA1 Q)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto; blast)

(* Thesis Theorem T.5.2.3. *)
lemma RA1_disj:
  "RA1 (P \<or> Q) = (RA1 P \<or> RA1 Q)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto; blast)

lemma RA1_conj_ok:
  "RA1 (P \<and> ok\<^sup>>) = (RA1 P \<and> ok\<^sup>>)"
  by (simp add: RA1_def fun_eq_iff Let_def; pred_auto)

(* Paper Lemma 23 *)
lemma RA1_design_pre:
  "RA1 (P \<turnstile> Q) = RA1 ((\<not> RA1 (\<not> P)) \<turnstile> Q)"
  by (simp add: RA1_def design_def fun_eq_iff Let_def; pred_auto; blast)

lemma RA1_Idempotent [closure]: "Idempotent RA1"
  by (simp add: Idempotent_def RA1_idem)

lemma RA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA1 P \<sqsubseteq> RA1 Q"
  by (auto simp add: RA1_def pred_refine_iff Let_def split: prod.splits)

lemma RA1_Monotonic [closure]:
  "Monotonic RA1"
  by (rule MonotonicI, rule RA1_mono)

(* Paper Theorem 9. *)
lemma RA1_A0: "RA1 (A0 P) = RA1 P"
  by (simp add: RA1_def A0_def ac_non_empty_def fun_eq_iff Let_def;
      pred_auto)

(* RA1 absorbs the A0 non-emptiness requirement. *)
lemma RA1_ac_non_empty_absorb:
  "RA1 (ac_non_empty \<and> P) = RA1 P"
  by (simp add: RA1_def ac_non_empty_def fun_eq_iff Let_def;
      pred_auto)

(* Paper Example 11.  PBMH_ades is the lifting of the paper's PBMH through
   the outer design record. *)
definition rad_ac_empty :: "'e reactive_angelic_design" where
[pred]: "rad_ac_empty = (\<lambda> (x, y).
  achoices.ac\<^sub>v (des_vars.more y) = {})"

lemma PBMH_ades_ac_empty [simp]:
  "PBMH_ades rad_ac_empty = true"
  by (simp add: PBMH_ades_def rad_ac_empty_def; pred_auto)

lemma RA1_ac_empty [simp]:
  "RA1 rad_ac_empty = false"
  by (simp add: RA1_def rad_ac_empty_def fun_eq_iff; pred_auto)

lemma RA1_PBMH_ades_ac_empty:
  "RA1 (PBMH_ades rad_ac_empty) = RA1 true"
  by simp

lemma PBMH_ades_RA1_ac_empty:
  "PBMH_ades (RA1 rad_ac_empty) = false"
  by (simp add: PBMH_ades_def; pred_auto)

lemma RA1_PBMH_ades_not_commute:
  "RA1 (PBMH_ades rad_ac_empty) \<noteq>
   PBMH_ades (RA1 rad_ac_empty)"
  by (simp only: RA1_PBMH_ades_ac_empty PBMH_ades_RA1_ac_empty;
      simp add: RA1_def rad_trace_extensions_def fun_eq_iff; pred_auto)

(* Paper Theorem 70 *)
lemma PBMH_ades_RA1_PBMH_ades:
  "(PBMH_ades \<circ> RA1 \<circ> PBMH_ades) P = (RA1 \<circ> PBMH_ades) P"
  by (simp add: PBMH_ades_def RA1_def fun_eq_iff; pred_auto)

lemma RA1_PBMH_ades_healthy [closure]:
  assumes "P is PBMH_ades"
  shows "RA1 P is PBMH_ades"
  using assms PBMH_ades_RA1_PBMH_ades[of P]
  by (simp add: Healthy_def')

lemma PBMH_ades_disj:
  "PBMH_ades (P \<or> Q) = (PBMH_ades P \<or> PBMH_ades Q)"
  apply (simp add: PBMH_ades_def PBMH_disj fun_eq_iff)
  apply pred_auto
  done

lemma PBMH_ades_conj_ok:
  "PBMH_ades (P \<and> ok\<^sup>>) = (PBMH_ades P \<and> ok\<^sup>>)"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma PBMH_ades_not_ok [simp]:
  "PBMH_ades (\<lambda> (x, y). \<not> ok\<^sub>v x) =
   (\<lambda> (x, y). \<not> ok\<^sub>v x)"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

lemma PBMH_ades_RA1_not_ok [simp]:
  "PBMH_ades (RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x)) =
   RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x)"
  using PBMH_ades_RA1_PBMH_ades[
      of "(\<lambda> (x, y). \<not> ok\<^sub>v x)"]
  by simp

lemma PBMH_ades_H1_H2:
  "(PBMH_ades \<circ> H1 \<circ> H2) P =
   (H1 \<circ> H2 \<circ> PBMH_ades) P"
  by (simp add: PBMH_ades_def H1_def H2_split fun_eq_iff;
      pred_auto; blast)

subsection \<open>RA2: Trace-history independence\<close>

(* s \<oplus> {tr ↦ []} *)
definition rad_zero_trace :: "'e rad_state \<Rightarrow> 'e rad_state" where
"rad_zero_trace s\<^sub>0 =
  rad_state.tr\<^sub>v_update (\<lambda>_. []) s\<^sub>0"

(* z \<oplus> {tr ↦ z.tr - s.tr} *)
definition rad_trace_difference ::
  "'e rad_state \<Rightarrow> 'e rad_state \<Rightarrow> 'e rad_state" where
"rad_trace_difference s\<^sub>0 z =
  rad_state.tr\<^sub>v_update
    (\<lambda>_. rad_state.tr\<^sub>v z - rad_state.tr\<^sub>v s\<^sub>0) z"

(* { z[(z.tr-s.tr) / tr] | z \<in> ac' ∧ s.tr \<le> z.tr } *)
definition rad_normalise_choices ::
  "'e rad_state \<Rightarrow> 'e rad_state set \<Rightarrow> 'e rad_state set" where
"rad_normalise_choices s\<^sub>0 ac' =
  {rad_trace_difference s\<^sub>0 z | z.
    z \<in> ac' \<and>
    rad_state.tr\<^sub>v s\<^sub>0 \<le> rad_state.tr\<^sub>v z}"

lemma rad_normalise_choices_mono:
  "choices \<subseteq> choices' \<Longrightarrow>
   rad_normalise_choices s0 choices \<subseteq>
   rad_normalise_choices s0 choices'"
  by (auto simp add: rad_normalise_choices_def)

(* Paper Definition 29. *)
(* RA2(P)(s,ac') = P(s[[]/tr], rad_normalise_choices(s, ac')) *)
definition RA2 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where [pred]: "RA2 P = (\<lambda> (x, y).
  let x_state = des_vars.more x;
      y_choices = des_vars.more y;
      s\<^sub>0 = astate.s\<^sub>v x_state;
      ac' = achoices.ac\<^sub>v y_choices;
      ac'' = rad_normalise_choices s\<^sub>0 ac';
      x_state' = astate.s\<^sub>v_update
        (\<lambda>_. rad_zero_trace s\<^sub>0) x_state;
      y_choices' = achoices.ac\<^sub>v_update (\<lambda>_. ac'') y_choices;
      x' = des_vars.more_update (\<lambda>_. x_state') x;
      y' = des_vars.more_update (\<lambda>_. y_choices') y
  in P (x', y'))"

lemma RA2_idem: "RA2 (RA2 P) = RA2 P"
  by (simp add: RA2_def rad_zero_trace_def rad_normalise_choices_def
      rad_trace_difference_def fun_eq_iff)

lemma RA2_design:
  "RA2 (P \<turnstile> Q) = (RA2 P \<turnstile> RA2 Q)"
  by (simp add: RA2_def design_def fun_eq_iff; pred_auto)

(* Thesis Theorem T.5.2.6. *)
lemma RA2_conj:
  "RA2 (P \<and> Q) = (RA2 P \<and> RA2 Q)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

(* Thesis Theorem T.5.2.7. *)
lemma RA2_disj:
  "RA2 (P \<or> Q) = (RA2 P \<or> RA2 Q)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

lemma RA2_conj_ok:
  "RA2 (P \<and> ok\<^sup>>) = (RA2 P \<and> ok\<^sup>>)"
  by (simp add: RA2_def fun_eq_iff Let_def; pred_auto)

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
    apply (cases s0; cases z)
    apply (simp_all add: less_eq_list_def minus_list_def)
    subgoal premises assms for tr ref wait tr'
    proof -
      have prefix_length: "length tr \<le> length tr'"
        by (rule prefix_imp_length_lteq[OF assms(3)])
      have length_eq: "length tr = length tr'"
        by (rule order_antisym[OF prefix_length assms(1)])
      have "tr = tr'"
        by (rule prefix_length_eq[OF length_eq assms(3)])
      then show ?thesis
        using assms(2) by simp
    qed
    done
  subgoal
    by (rule exI[where x=s0], simp)
  done

(* Paper Theorem 71 *)
lemma RA1_RA2_commute:
  "(RA1 \<circ> RA2) P = (RA2 \<circ> RA1) P"
  by (simp add: RA1_def RA2_def fun_eq_iff
      rad_normalise_choices_extensions rad_normalise_choices_nonempty
      rad_zero_trace_extensions Let_def)

(* Paper Theorem 66 *)
lemma PBMH_ades_RA2_PBMH_ades:
  "(PBMH_ades \<circ> RA2 \<circ> PBMH_ades) P =
   (RA2 \<circ> PBMH_ades) P"
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

lemma RA2_PBMH_ades_healthy [closure]:
  assumes "P is PBMH_ades"
  shows "RA2 P is PBMH_ades"
  using assms PBMH_ades_RA2_PBMH_ades[of P]
  by (simp add: Healthy_def')

lemma RA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA2 P \<sqsubseteq> RA2 Q"
  by (auto simp add: RA2_def pred_refine_iff Let_def split: prod.splits)

lemma RA2_Monotonic [closure]:
  "Monotonic RA2"
  by (rule MonotonicI, rule RA2_mono)

subsection \<open>RA3. Reactive identity and waiting\<close>

(* Paper Definition 30. Rac identity *)
definition II_Rac :: "'e reactive_angelic_design" where
[pred]: "II_Rac = (\<lambda> (x, y).
  let s0 = astate.s\<^sub>v (des_vars.more x);
      A = achoices.ac\<^sub>v (des_vars.more y)
  in RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x) (x, y) \<or> (ok\<^sub>v y \<and> s0 \<in> A))"

(* Thesis Theorems T.G.3.1, T.G.3.2, and T.G.3.4. *)
lemma RA1_II_Rac:
  "RA1 II_Rac = II_Rac"
  apply (simp only: RA1_def II_Rac_def fun_eq_iff)
  apply (simp add: Let_def rad_trace_extensions_def
      des_vars.ok_def des_vars.more\<^sub>L_def)
  apply blast
  done

lemma RA2_II_Rac:
  "RA2 II_Rac = II_Rac"
  apply (simp only: RA2_def II_Rac_def fun_eq_iff)
  apply (simp add: Let_def RA1_def rad_zero_trace_extensions
      rad_normalise_choices_nonempty rad_zero_trace_in_normalise
      des_vars.ok_def des_vars.more\<^sub>L_def)
  done

lemma II_Rac_RA1_healthy [closure]:
  "II_Rac is RA1"
  by (simp add: Healthy_def RA1_II_Rac)

lemma II_Rac_RA2_healthy [closure]:
  "II_Rac is RA2"
  by (simp add: Healthy_def RA2_II_Rac)

lemma PBMH_ades_II_Rac [simp]:
  "PBMH_ades II_Rac = II_Rac"
proof -
  have split:
      "II_Rac =
       (RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x) \<or>
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

lemma II_Rac_PBMH_ades_healthy [closure]:
  "II_Rac is PBMH_ades"
  by (simp add: Healthy_def)

abbreviation rad_wait_lens where
"rad_wait_lens \<equiv>
  rad_state.wait ;\<^sub>L astate.s ;\<^sub>L des_vars.more\<^sub>L"

(* P_f \<equiv> P[s\<oplus>(wait ↦ false)/s] *)
definition rad_wait_false ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
[pred]: "rad_wait_false P = P\<lbrakk>False/rad_wait_lens\<^sup><\<rbrakk>"

notation rad_wait_false ("_\<^sub>wf" [1000] 1000)

lemma rad_wait_false_as_state_subst:
  "rad_wait_false P =
   ades_state_subst
     (subst_upd subst_id (rad_state.wait ;\<^sub>L astate.s) (\<lambda>_. False)) P"
  by (simp add: rad_wait_false_def subst_app_def subst_upd_def
      subst_id_def subst_aext_def fun_eq_iff lens_defs)

lemma rad_wait_false_A:
  "(rad_wait_false \<circ> A) P = (A \<circ> rad_wait_false) P"
  by (simp add: rad_wait_false_as_state_subst A_state_subst)

lemma rad_wait_false_H1_H2:
  "(rad_wait_false \<circ> H1 \<circ> H2) P =
   (H1 \<circ> H2 \<circ> rad_wait_false) P"
  by (simp add: rad_wait_false_def H1_def H2_split fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def lens_defs;
      pred_auto)

lemma rad_wait_false_design_healthy [closure]:
  "((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t) is \<^bold>H"
  by (rule design_is_H1_H2; pred_auto)

lemma PBMH_ades_wait_cond:
  "PBMH_ades (P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) =
   (PBMH_ades P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    PBMH_ades Q)"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def expr_if_def
      fun_eq_iff lens_defs; pred_auto; blast)

(* Paper Definition 31. *)
definition RA3 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
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

lemma RA3_idem:
  "RA3 (RA3 P) = RA3 P"
  by (simp add: RA3_def)

(* Thesis Theorem T.G.3.3. *)
lemma RA3_II_Rac:
  "RA3 II_Rac = II_Rac"
  by (simp add: RA3_def)

lemma II_Rac_RA3_healthy [closure]:
  "II_Rac is RA3"
  by (simp add: Healthy_def' RA3_II_Rac)

(* Thesis Theorem T.5.2.12. *)
lemma RA3_conj:
  "RA3 (P \<and> Q) = (RA3 P \<and> RA3 Q)"
  by (simp add: RA3_def expr_if_def fun_eq_iff; pred_auto)

(* Thesis Theorem T.5.2.13. *)
lemma RA3_disj:
  "RA3 (P \<or> Q) = (RA3 P \<or> RA3 Q)"
  by (simp add: RA3_def expr_if_def fun_eq_iff; pred_auto)

lemma RA3_PBMH_ades_healthy [closure]:
  assumes "P is PBMH_ades"
  shows "RA3 P is PBMH_ades"
  using assms
  by (simp add: Healthy_def' RA3_def PBMH_ades_wait_cond)

(* Thesis Theorem T.5.2.15. *)
lemma PBMH_ades_RA3_PBMH_ades:
  "(PBMH_ades \<circ> RA3 \<circ> PBMH_ades) P =
   (RA3 \<circ> PBMH_ades) P"
  using RA3_PBMH_ades_healthy[of "PBMH_ades P"]
  by (simp add: Healthy_def' PBMH_ades_idem)

lemma RA3_Idempotent [closure]:
  "Idempotent RA3"
  by (simp add: Idempotent_def RA3_idem)

(* Paper Theorem 68.  The paper's theorem statement repeats
   RA3 \<circ> RA1 on both sides, but its proof establishes this commutation law. *)
lemma RA1_RA3_commute:
  "(RA1 \<circ> RA3) P = (RA3 \<circ> RA1) P"
  by (simp add: RA3_def RA1_wait_cond RA1_II_Rac)

(* Paper Theorem 69 *)
lemma RA2_RA3_commute:
  "(RA2 \<circ> RA3) P = (RA3 \<circ> RA2) P"
  by (simp add: RA3_def RA2_wait_cond RA2_II_Rac)

(* Paper Lemma 19 *)
lemma RA3_wait_false:
  "RA3 P = (RA3 \<circ> rad_wait_false) P"
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

lemma RA3_Monotonic [closure]:
  "Monotonic RA3"
  by (rule MonotonicI, rule RA3_mono)

subsection \<open>RA\<close>

(* Paper Definition 32. *)
definition RA ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
[pred]: "RA = RA1 \<circ> RA2 \<circ> RA3"

lemma RA_PBMH_ades_healthy [closure]:
  assumes "P is PBMH_ades"
  shows "RA P is PBMH_ades"
  unfolding RA_def comp_apply
  by (intro RA1_PBMH_ades_healthy RA2_PBMH_ades_healthy
      RA3_PBMH_ades_healthy assms)

lemma PBMH_ades_RA_PBMH_ades:
  "(PBMH_ades \<circ> RA \<circ> PBMH_ades) P =
   (RA \<circ> PBMH_ades) P"
  using RA_PBMH_ades_healthy[of "PBMH_ades P"]
  by (simp add: Healthy_def' PBMH_ades_idem)

lemma RA_conj:
  "RA (P \<and> Q) = (RA P \<and> RA Q)"
  by (simp add: RA_def RA1_conj RA2_conj RA3_conj)

lemma RA_disj:
  "RA (P \<or> Q) = (RA P \<or> RA Q)"
  by (simp add: RA_def RA1_disj RA2_disj RA3_disj)

(* The components of RA commute, so RA may be recomposed in any order. *)
lemma RA_alt_def:
  "RA P = RA3 (RA2 (RA1 P))"
  by (simp add: RA_def
      RA1_RA2_commute[simplified comp_apply]
      RA1_RA3_commute[simplified comp_apply]
      RA2_RA3_commute[simplified comp_apply])

lemma RA_design_components:
  "RA (P \<turnstile> Q) =
   RA ((\<not> RA1 (\<not> P)) \<turnstile> RA1 Q)"
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

lemma RA_cong_ac_non_empty:
  assumes "(ac_non_empty \<and> P) = (ac_non_empty \<and> Q)"
  shows "RA P = RA Q"
  using arg_cong[where f=RA1, OF assms]
  by (simp only: RA1_ac_non_empty_absorb RA_alt_def)

lemma RA_A1:
  "(RA \<circ> A) P = (RA \<circ> A1) P"
  by (simp add: RA_def A_def
      RA1_RA2_commute[simplified comp_apply]
      RA1_RA3_commute[simplified comp_apply]
      RA2_RA3_commute[simplified comp_apply] RA1_A0)

(* Paper Theorem 67 *)
lemma RA_A:
  assumes "P is \<^bold>H"
  shows "(RA \<circ> A) P = (RA \<circ> PBMH_ades) P"
  by (simp add: RA_A1[simplified comp_apply]
      A1_eq_PBMH_ades[OF assms])

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

(* Paper Lemma 20 *)
(* (rad_wait_false (RA (A
     (\<not> (P \<^sub>wf)^f \<turnstile> (P \<^sub>wf)^t))))^f =
   RA2 \<circ> RA1 \<circ> PBMH (\<not> ok ∨ (P \<^sub>wf)^f) *)
lemma RA_design_wait_false:
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
    apply (subst RA_A[simplified comp_apply])
     apply (rule design_is_H1_H2)
      apply pred_auto
     apply pred_auto
    apply (simp only: RA_wait_false_ok_subst[simplified comp_apply] pbmh_design)
    done
qed

(* Paper Lemma 21 *)
(* (RA \<circ> A(\<not>P^f_f \<turnstile> P^t_f))^t_f = RA2 \<circ> RA1 \<circ> PBMH(\<not>ok ∨ P^f_f ∨ P^t_f) *)
lemma RA_design_wait_false_ok_true:
  "((rad_wait_false \<circ> RA \<circ> A)
      ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t))\<^sup>t =
   (RA2 \<circ> RA1 \<circ> PBMH_ades)
     ((\<not> ok\<^sup><) \<or> (P \<^sub>wf)\<^sup>f \<or> (P \<^sub>wf)\<^sup>t)"
  unfolding comp_apply
  apply (subst RA_A[simplified comp_apply])
   apply (rule design_is_H1_H2; pred_auto)
  apply (simp only: RA_wait_false_ok_subst[simplified comp_apply])
  apply (rule arg_cong[where f=RA2])
  apply (rule arg_cong[where f=RA1])
  by (simp add: rad_wait_false_def PBMH_ades_def design_def fun_eq_iff
      subst_app_def subst_upd_def subst_id_def SEXP_def Let_def
      PBMH_def pbmh_step_def; pred_auto)

(* Paper Lemma 22 *)
lemma RA_design_post:
  "RA (P \<turnstile> Q) = RA (P \<turnstile> (RA2 \<circ> RA1) Q)"
proof -
  have ra12_design:
      "RA2 (RA1 (P \<turnstile> Q)) =
       RA2 (RA1 (P \<turnstile> RA2 (RA1 Q)))"
    by (simp only: RA1_RA2_commute[simplified comp_apply, symmetric,
          of "P \<turnstile> Q"]
        RA2_design[of P Q]
        RA1_design_post[of "RA2 P" "RA2 Q"]
        RA1_RA2_commute[simplified comp_apply, of Q]
        RA1_RA2_commute[simplified comp_apply, symmetric,
          of "P \<turnstile> RA2 (RA1 Q)"]
        RA2_design[of P "RA2 (RA1 Q)"] RA2_idem[of "RA1 Q"])
  show ?thesis
    unfolding RA_def comp_apply
    by (simp only: RA1_RA2_commute[simplified comp_apply]
        RA1_RA3_commute[simplified comp_apply]
        RA2_RA3_commute[simplified comp_apply] ra12_design)
qed

lemma RA_design_as_disj:
  "(P \<turnstile> Q) =
   ((\<not> ok\<^sup><) \<or> (\<not> P) \<or> (Q \<and> ok\<^sup>>))"
  by (simp add: design_def fun_eq_iff; pred_auto)

lemma RA_RA2_RA1_absorb:
  "RA (RA2 (RA1 P)) = RA P"
  by (simp add: RA_def RA1_RA2_commute[simplified comp_apply]
      RA1_RA3_commute[simplified comp_apply]
      RA2_RA3_commute[simplified comp_apply]
      RA1_idem RA2_idem)

lemma PBMH_ades_RA2_RA1_PBMH_ades:
  "PBMH_ades (RA2 (RA1 (PBMH_ades P))) =
   RA2 (RA1 (PBMH_ades P))"
proof -
  have ra1_healthy:
      "PBMH_ades (RA1 (PBMH_ades P)) = RA1 (PBMH_ades P)"
    by (simp only:
        PBMH_ades_RA1_PBMH_ades[simplified comp_apply])
  have "PBMH_ades (RA2 (RA1 (PBMH_ades P))) =
        PBMH_ades (RA2 (PBMH_ades (RA1 (PBMH_ades P))))"
    by (simp only: ra1_healthy)
  also have "... = RA2 (PBMH_ades (RA1 (PBMH_ades P)))"
    by (simp only:
        PBMH_ades_RA2_PBMH_ades[simplified comp_apply])
  also have "... = RA2 (RA1 (PBMH_ades P))"
    by (simp only: ra1_healthy)
  finally show ?thesis .
qed

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

lemma PBMH_ades_not_ok_expr:
  "PBMH_ades (\<not> ok\<^sup><) = (\<not> ok\<^sup><)"
  by (simp add: PBMH_ades_def fun_eq_iff; pred_auto)

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
    by (simp only: PBMH_ades_RA2_RA1_PBMH_ades)
  have V_healthy: "PBMH_ades ?V = ?V"
    by (simp only: PBMH_ades_RA2_RA1_PBMH_ades)
  have absorb:
      "((\<not> ok\<^sup><) \<or> ?X \<or> (?Z \<and> ok\<^sup>>)) =
       ((\<not> ok\<^sup><) \<or> F \<or> (T \<and> ok\<^sup>>))"
    by pred_auto
  have "RA (PBMH_ades ((\<not> ?U) \<turnstile> ?V)) =
        RA (PBMH_ades
          ((\<not> ok\<^sup><) \<or> ?U \<or> (?V \<and> ok\<^sup>>)))"
    by (simp add: RA_design_as_disj)
  also have "... = RA
      (PBMH_ades (\<not> ok\<^sup><) \<or> PBMH_ades ?U \<or>
        PBMH_ades (?V \<and> ok\<^sup>>))"
    by (simp only: PBMH_ades_disj)
  also have "... = RA
      ((\<not> ok\<^sup><) \<or> PBMH_ades ?U \<or>
        (PBMH_ades ?V \<and> ok\<^sup>>))"
    by (simp only: PBMH_ades_not_ok_expr PBMH_ades_conj_ok)
  also have "... = RA
      ((\<not> ok\<^sup><) \<or> ?U \<or> (?V \<and> ok\<^sup>>))"
    by (simp only: U_healthy V_healthy)
  also have "... =
      (RA (\<not> ok\<^sup><) \<or> RA ?U \<or>
        RA (?V \<and> ok\<^sup>>))"
    by (simp only: RA_disj)
  also have "... =
      (RA (\<not> ok\<^sup><) \<or> RA (PBMH_ades ?X) \<or>
        RA (PBMH_ades (?Z \<and> ok\<^sup>>)))"
    by (simp only:
        RA_RA2_RA1_absorb[of "PBMH_ades ?X"]
        RA_RA2_RA1_PBMH_ades_conj_ok[of ?Z])
  also have "... = RA
      ((\<not> ok\<^sup><) \<or> PBMH_ades ?X \<or>
        PBMH_ades (?Z \<and> ok\<^sup>>))"
    by (simp only: RA_disj)
  also have "... = RA (PBMH_ades
      ((\<not> ok\<^sup><) \<or> ?X \<or> (?Z \<and> ok\<^sup>>)))"
    by (simp only: PBMH_ades_disj PBMH_ades_not_ok_expr)
  also have "... = RA (PBMH_ades
      ((\<not> ok\<^sup><) \<or> F \<or> (T \<and> ok\<^sup>>)))"
    by (simp only: absorb)
  also have "... = RA (PBMH_ades ((\<not> F) \<turnstile> T))"
    by (simp add: RA_design_as_disj)
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
    apply (subst RA_A[OF rad_wait_false_design_healthy,
        simplified comp_apply])
    apply (simp only:
        RA_design_wait_false[simplified comp_apply]
        RA_design_wait_false_ok_true[simplified comp_apply])
    apply (subst RA_design_PBMH_normalise)
    by (rule RA_A[OF rad_wait_false_design_healthy,
        simplified comp_apply, symmetric])
qed

lemma RA_idem:
  "RA (RA P) = RA P"
  by (simp add: RA_def RA1_RA2_commute[simplified comp_apply]
      RA1_RA3_commute[simplified comp_apply]
      RA2_RA3_commute[simplified comp_apply]
      RA1_idem RA2_idem RA3_idem)

lemma RA_Idempotent [closure]:
  "Idempotent RA"
  by (simp add: Idempotent_def RA_idem)

lemma RA_healthy [closure]:
  "RA P is RA"
  by (simp add: Healthy_def' RA_idem)

lemma RA_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA P \<sqsubseteq> RA Q"
  by (simp add: RA_def RA1_mono RA2_mono RA3_mono)

lemma RA_Monotonic [closure]:
  "Monotonic RA"
  unfolding RA_def
  by (intro Monotonic_comp RA1_Monotonic RA2_Monotonic RA3_Monotonic)

end
