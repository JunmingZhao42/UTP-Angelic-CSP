section \<open>Reactive Angelic Healthiness Conditions\<close>

theory utp_rad_healthy
  imports utp_rad_bridge
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
"RA1 P = (\<lambda> (x, y).
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

lemma RA1_Idempotent: "Idempotent RA1"
  by (simp add: Idempotent_def RA1_idem)

lemma RA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA1 P \<sqsubseteq> RA1 Q"
  by (auto simp add: RA1_def pred_refine_iff Let_def split: prod.splits)

lemma RA1_Monotonic [closure]:
  "Monotonic RA1"
  by (rule MonotonicI, rule RA1_mono)

(* Paper Theorem 9. *)
lemma RA1_A0: "RA1 (A0 P) = RA1 P"
  apply (simp add: RA1_def A0_def ac_non_empty_def fun_eq_iff)
  apply (pred_auto)
  apply (simp_all add: Let_def)
  done

(* Paper Example 11.  PBMH_ades is the lifting of the paper's PBMH through
   the outer design record. *)
definition rad_ac_empty :: "'e reactive_angelic_design" where
"rad_ac_empty = (\<lambda> (x, y).
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

(* Paper Definition 29. *)
(* RA2(P)(s,ac') = P(s[[]/tr], rad_normalise_choices(s, ac')) *)
definition RA2 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where "RA2 P = (\<lambda> (x, y).
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

lemma RA2_Idempotent: "Idempotent RA2"
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
    apply (metis prefix_length_eq prefix_imp_length_lteq order_antisym)
    done
  subgoal
    by (rule exI[where x=s0], simp)
  done

(* Thesis T.5.2.10. *)
lemma RA1_RA2_commute:
  "RA1 (RA2 P) = RA2 (RA1 P)"
  by (simp add: RA1_def RA2_def fun_eq_iff
      rad_normalise_choices_extensions rad_normalise_choices_nonempty
      rad_zero_trace_extensions Let_def)

lemma RA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA2 P \<sqsubseteq> RA2 Q"
  by (auto simp add: RA2_def pred_refine_iff Let_def split: prod.splits)

lemma RA2_Monotonic [closure]:
  "Monotonic RA2"
  by (rule MonotonicI, rule RA2_mono)

subsection \<open>RA3. Reactive identity and waiting\<close>

(* Paper Definition 30. Rac identity *)
definition II_Rac :: "'e reactive_angelic_design" where
"II_Rac = (\<lambda> (x, y).
  let s0 = astate.s\<^sub>v (des_vars.more x);
      A = achoices.ac\<^sub>v (des_vars.more y)
  in RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x) (x, y) \<or> (ok\<^sub>v y \<and> s0 \<in> A))"

(* Thesis T.G.3.1--T.G.3.4. *)
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

abbreviation rad_wait_lens where
"rad_wait_lens \<equiv>
  rad_state.wait ;\<^sub>L astate.s ;\<^sub>L des_vars.more\<^sub>L"

(* Paper Definition 31. *)
definition RA3 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design" where
"RA3 P = (II_Rac \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)"

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

lemma RA3_Idempotent:
  "Idempotent RA3"
  by (simp add: Idempotent_def RA3_idem)

(* Thesis T.5.2.16--T.5.2.17. *)
lemma RA1_RA3_commute:
  "RA1 (RA3 P) = RA3 (RA1 P)"
  by (simp add: RA3_def RA1_wait_cond RA1_II_Rac)

lemma RA2_RA3_commute:
  "RA2 (RA3 P) = RA3 (RA2 P)"
  by (simp add: RA3_def RA2_wait_cond RA2_II_Rac)

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
"RA = RA1 \<circ> RA2 \<circ> RA3"

lemma RA_idem:
  "RA (RA P) = RA P"
  by (simp add: RA_def RA1_RA2_commute RA1_RA3_commute
      RA2_RA3_commute RA1_idem RA2_idem RA3_idem)

lemma RA_Idempotent:
  "Idempotent RA"
  by (simp add: Idempotent_def RA_idem)

lemma RA_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA P \<sqsubseteq> RA Q"
  by (simp add: RA_def RA1_mono RA2_mono RA3_mono)

lemma RA_Monotonic [closure]:
  "Monotonic RA"
  unfolding RA_def
  by (intro Monotonic_comp RA1_Monotonic RA2_Monotonic RA3_Monotonic)

end
