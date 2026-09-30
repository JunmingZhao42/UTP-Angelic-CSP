section \<open>Reactive Angelic Design Parallel-by-Merge\<close>

theory utp_rad_parallel
  imports utp_rad_designs
    "UTP-Angelic-Designs.utp_ades_parallel"
begin

text \<open>
  The merge sees complete branch observations, including termination flags
  and choice sets of reactive states. Merge healthiness provides the closure kit.
  The public operator below restricts the seed to conjunctive branch ok flags
  before applying reactive merge healthiness. Waiting policies remain in M.
\<close>

type_synonym ('t, 'e) rad_merge_rel =
  "(('t, 'e) rad_state) ades_merge_rel"

subsection \<open>Simultaneous trace normalisation\<close>

definition rad_merge_input ::
  "('t::trace, 'e) rad_state astate des_vars_ext \<Rightarrow>
   ('t, 'e) rad_state astate des_vars_ext"
where
  "rad_merge_input x = des_vars.more_update
    (\<lambda>_. astate.s\<^sub>v_update
      (\<lambda>_. rad_zero_trace (astate.s\<^sub>v (des_vars.more x)))
      (des_vars.more x)) x"

definition rad_merge_output ::
  "('t::trace, 'e) rad_state \<Rightarrow>
   ('t, 'e) rad_state achoices des_vars_ext \<Rightarrow>
   ('t, 'e) rad_state achoices des_vars_ext"
where
  "rad_merge_output s0 out = des_vars.more_update
    (\<lambda>_. achoices.ac\<^sub>v_update
      (\<lambda>_. rad_normalise_choices s0 (achoices.ac\<^sub>v (des_vars.more out)))
      (des_vars.more out)) out"

lemma rad_merge_input_zero [simp]:
  "rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more (rad_merge_input x))) = 0"
  by (simp add: rad_merge_input_def rad_zero_trace_def)

lemma rad_merge_input_idem [simp]:
  "rad_merge_input (rad_merge_input x) = rad_merge_input x"
  by (cases x; simp add: rad_merge_input_def rad_zero_trace_def)

lemma rad_normalise_choices_zero:
  assumes "rad_state.tr\<^sub>v s0 = 0"
  shows "rad_normalise_choices s0 X = X"
  using assms
  by (simp add: rad_normalise_choices_def rad_trace_difference_def)

lemma rad_merge_output_zero:
  assumes "rad_state.tr\<^sub>v s0 = 0"
  shows "rad_merge_output s0 out = out"
  using assms
  by (cases out; simp add: rad_merge_output_def rad_normalise_choices_zero)

lemma rad_merge_input_identity:
  assumes "rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x)) = 0"
  shows "rad_merge_input x = x"
proof -
  have zero: "rad_zero_trace s0 = s0"
    if "rad_state.tr\<^sub>v s0 = 0" for s0
    using that by (cases s0; simp add: rad_zero_trace_def)
  show ?thesis
    using assms
    by (cases x; simp add: rad_merge_input_def zero)
qed

lemma rad_merge_output_surj:
  fixes s0 :: "('t::trace, 'e) rad_state"
  obtains out where "rad_merge_output s0 out = target"
proof -
  let ?prepend = "\<lambda>z :: ('t, 'e) rad_state. rad_state.tr\<^sub>v_update
    (\<lambda>t. rad_state.tr\<^sub>v s0 + t) z"
  let ?X = "image ?prepend (achoices.ac\<^sub>v (des_vars.more target))"
  let ?out = "des_vars.more_update (achoices.ac\<^sub>v_update (\<lambda>_. ?X)) target"
  have inj: "inj ?prepend"
  proof (rule injI)
    fix a b :: "('t, 'e) rad_state"
    assume eq: "?prepend a = ?prepend b"
    show "a = b" using eq
      by (cases a; cases b; auto dest: left_cancel_monoid_class.add_left_imp_eq)
  qed
  have "rad_normalise_choices s0 ?X =
      achoices.ac\<^sub>v (des_vars.more target)"
    by (auto simp add: rad_normalise_choices_as_prepend inj_eq[OF inj])
  then have "rad_merge_output s0 ?out = target"
    by (cases target; simp add: rad_merge_output_def)
  then show thesis by (rule that)
qed

lemma RA2_merge_eval:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "RA2 P (x,out) =
    P (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)"
  by (simp add: RA2_def rad_merge_input_def rad_merge_output_def Let_def;
      pred_auto)

definition RA2M ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "RA2M M = (\<lambda>(m,out).
    let x = mrg_prior\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x)
    in ades_merge_eval M (rad_merge_input x)
      (rad_merge_output s0 (mrg_left\<^sub>v m))
      (rad_merge_output s0 (mrg_right\<^sub>v m))
      (rad_merge_output s0 out))"

lemma RA2M_eval:
  "ades_merge_eval (RA2M M) x p q out =
    ades_merge_eval M (rad_merge_input x)
      (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) p)
      (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) q)
      (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)"
  by (simp add: RA2M_def Let_def)

lemma RA2M_zero:
  assumes "rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x)) = 0"
  shows "ades_merge_eval (RA2M M) x p q out = ades_merge_eval M x p q out"
  by (simp add: RA2M_eval rad_merge_input_identity[OF assms]
      rad_merge_output_zero[OF assms])

lemma RA2M_idem: "RA2M (RA2M M) = RA2M M"
  by (simp add: RA2M_def fun_eq_iff Let_def rad_merge_output_zero)

lemma RA2M_Idempotent [closure]: "Idempotent RA2M"
  by (simp add: Idempotent_def RA2M_idem)

lemma RA2M_mono:
  "M \<sqsubseteq> N \<Longrightarrow> RA2M M \<sqsubseteq> RA2M N"
  by (auto simp add: RA2M_def pred_refine_iff Let_def split: prod.splits)

lemma RA2M_Monotonic [closure]: "Monotonic RA2M"
  by (rule MonotonicI, rule RA2M_mono)

lemma RA2M_healthy [closure]: "RA2M M is RA2M"
  by (simp add: Healthy_def' RA2M_idem)

lemma rad_merge_input_obs [simp]:
  "rad_merge_input \<lparr>ok\<^sub>v = b, s\<^sub>v = s0, \<dots> = ()\<rparr> =
    \<lparr>ok\<^sub>v = b, s\<^sub>v = rad_zero_trace s0, \<dots> = ()\<rparr>"
  by (simp add: rad_merge_input_def)

lemma rad_merge_output_obs [simp]:
  "rad_merge_output s0 \<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr> =
    \<lparr>ok\<^sub>v = c, ac\<^sub>v = rad_normalise_choices s0 X, \<dots> = ()\<rparr>"
  by (simp add: rad_merge_output_def)

lemma RA1_obs:
  "RA1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c (rad_trace_extensions s0 \<inter> X)) \<and>
      rad_trace_extensions s0 \<inter> X \<noteq> {})"
  by (simp add: RA1_def Let_def)

lemma CSPA1_obs:
  "CSPA1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c X) \<or>
      (\<not> b \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}))"
  by (simp add: CSPA1_def RA1_not_ok_eval; pred_auto)

lemma RA3_obs:
  "RA3 P (ades_obs b s0 c X) \<longleftrightarrow>
    (if rad_state.wait\<^sub>v s0 then II_Rac (ades_obs b s0 c X)
      else P (ades_obs b s0 c X))"
  by (simp add: RA3_eval)

lemma rad_normalise_choices_subsets:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "Y \<subseteq> rad_normalise_choices s0 X"
  obtains Z where "Z \<subseteq> X" "rad_normalise_choices s0 Z = Y"
proof -
  let ?Z = "{z \<in> X. rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
    rad_trace_difference s0 z \<in> Y}"
  have sub: "?Z \<subseteq> X" by auto
  have eq: "rad_normalise_choices s0 ?Z = Y"
    using assms by (auto simp add: rad_normalise_choices_def)
  show thesis by (rule that[OF sub eq])
qed

lemma rad_normalise_choices_exists_subset:
  "(\<exists>Y \<subseteq> X. F (rad_normalise_choices s0 Y)) \<longleftrightarrow>
    (\<exists>Y \<subseteq> rad_normalise_choices s0 X. F Y)"
proof
  assume "\<exists>Y \<subseteq> X. F (rad_normalise_choices s0 Y)"
  then obtain Y where sub: "Y \<subseteq> X"
    and f: "F (rad_normalise_choices s0 Y)" by blast
  have "rad_normalise_choices s0 Y \<subseteq> rad_normalise_choices s0 X"
    by (rule rad_normalise_choices_mono[OF sub])
  then show "\<exists>Y \<subseteq> rad_normalise_choices s0 X. F Y"
    using f by blast
next
  assume "\<exists>Y \<subseteq> rad_normalise_choices s0 X. F Y"
  then obtain Y where sub: "Y \<subseteq> rad_normalise_choices s0 X"
    and f: "F Y" by blast
  obtain Z where z: "Z \<subseteq> X" "rad_normalise_choices s0 Z = Y"
    by (rule rad_normalise_choices_subsets[OF sub])
  show "\<exists>Y \<subseteq> X. F (rad_normalise_choices s0 Y)"
    using z f by blast
qed


definition RA3M ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "RA3M M = (\<lambda>(m,out).
    if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m)))
    then II_Rac (mrg_prior\<^sub>v m,out) else M (m,out))"

lemma RA3M_eval:
  "ades_merge_eval (RA3M M) x p q out =
    (if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
     then II_Rac (x,out) else ades_merge_eval M x p q out)"
  by (simp add: RA3M_def)

lemma RA3M_idem: "RA3M (RA3M M) = RA3M M"
  by (auto simp: RA3M_def fun_eq_iff)

lemma RA3M_Idempotent [closure]: "Idempotent RA3M"
  by (simp add: Idempotent_def RA3M_idem)

lemma RA3M_mono: "M \<sqsubseteq> N \<Longrightarrow> RA3M M \<sqsubseteq> RA3M N"
  by (auto simp: RA3M_def pred_refine_iff split: prod.splits)

lemma RA3M_Monotonic [closure]: "Monotonic RA3M"
  by (rule MonotonicI, rule RA3M_mono)

lemma RA3M_SymMerge: "M is SymMerge \<Longrightarrow> (RA3M M) is SymMerge"
  by (auto simp: SymMerge_ades RA3M_eval)

lemma rad_zero_trace_wait [simp]:
  "rad_state.wait\<^sub>v (rad_zero_trace s0) = rad_state.wait\<^sub>v s0"
  by (simp add: rad_zero_trace_def)

lemma RA2M_RA3M_commute:
  "RA3M (RA2M M) = RA2M (RA3M M)"
  by (rule ades_merge_ext, rule ades_obs_ext;
      simp add: RA3M_eval RA2M_eval
        II_Rac_eval rad_normalise_choices_nonempty rad_zero_trace_in_normalise
        rad_zero_trace_extensions)

lemma CSPA1_RA3_commute:
  "CSPA1 (RA3 P) = RA3 (CSPA1 P)"
  by (rule ades_obs_ext;
      auto simp add: CSPA1_obs RA3_obs II_Rac_eval split: if_splits)

lemma CSPA1_healthy_obs_iff:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "P is CSPA1 \<longleftrightarrow>
    (\<forall>s0 c X. rad_trace_extensions s0 \<inter> X \<noteq> {} \<longrightarrow>
      P (ades_obs False s0 c X))"
proof
  assume h: "P is CSPA1"
  show "\<forall>s0 c X. rad_trace_extensions s0 \<inter> X \<noteq> {} \<longrightarrow>
      P (ades_obs False s0 c X)"
    using CSPA1_obs[of P False] h by (simp only: Healthy_if; blast)
next
  assume h: "\<forall>s0 c X. rad_trace_extensions s0 \<inter> X \<noteq> {} \<longrightarrow>
      P (ades_obs False s0 c X)"
  show "P is CSPA1"
    by (rule Healthy_intro, rule ades_obs_ext; simp only: CSPA1_obs;
        insert h; auto; blast)
qed

lemma II_Rac_has_result:
  fixes x :: "('t::trace, 'e) rad_state astate des_vars_ext"
  obtains out where "II_Rac (x,out)"
proof -
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  let ?out = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s0}, \<dots> = ()\<rparr>"
  have "II_Rac (x,?out)" by (simp add: II_Rac_eval)
  then show thesis by (rule that)
qed

lemma RAD_is_CSPA1_full:
  assumes "P is RAD"
  shows "P is CSPA1"
proof -
  have c2: "CSPA1 (RA2 P) = RA2 (CSPA1 P)" for P
    by (rule ades_obs_ext;
        simp add: CSPA1_obs RA2_merge_eval rad_normalise_choices_nonempty
          rad_zero_trace_extensions)
  have "CSPA1 (RAD P) = RAD P"
    by (simp add: RAD_def RA_def RA1_CSPA1_commute[simplified comp_apply, symmetric]
        c2 CSPA1_RA3_commute CSPA1_idem)
  then show ?thesis using assms by (simp add: Healthy_def')
qed

lemma RA2M_SymMerge:
  assumes "M is SymMerge"
  shows "(RA2M M) is SymMerge"
  using assms by (auto simp add: SymMerge_ades RA2M_eval)


subsection \<open>Conjunctive-ok reactive merge\<close>

definition rad_ok_body ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "rad_ok_body M = (\<lambda>(m,out).
    RA1 (CSPA1 (H2 (PBMH_ades
      (\<lambda>(x,out). des_vars.ok\<^sub>v out =
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
        ades_merge_eval M x (mrg_left\<^sub>v m) (mrg_right\<^sub>v m) out))))
      (mrg_prior\<^sub>v m,out))"

lemma rad_ok_body_obs:
  "(\<lambda>(x,out). ades_merge_eval (rad_ok_body M) x p q out) (ades_obs b s0 c X) \<longleftrightarrow>
    (rad_trace_extensions s0 \<inter> X \<noteq> {} \<and>
     (\<not> b \<or>
      (if des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q
       then c \<and> (\<exists>Y \<subseteq> rad_trace_extensions s0 \<inter> X.
         (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs b s0 True Y))
       else (\<exists>Y \<subseteq> rad_trace_extensions s0 \<inter> X.
         (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs b s0 False Y)))))"
  by (cases b; cases c; cases "des_vars.ok\<^sub>v p"; cases "des_vars.ok\<^sub>v q";
      auto simp: rad_ok_body_def RA1_obs CSPA1_obs H2_obs PBMH_ades_obs)

lemmas rad_ok_body_eval = rad_ok_body_obs[simplified]

lemma ok_merge_extensions_subset_twice:
  assumes "E \<inter> X \<noteq> {}"
  shows "(\<exists>Y \<subseteq> E \<inter> X. E \<inter> Y \<noteq> {} \<and>
      (\<exists>Z \<subseteq> E \<inter> Y. F Z)) \<longleftrightarrow>
    (\<exists>Z \<subseteq> E \<inter> X. F Z)"
proof
  assume "\<exists>Y \<subseteq> E \<inter> X. E \<inter> Y \<noteq> {} \<and>
    (\<exists>Z \<subseteq> E \<inter> Y. F Z)"
  then obtain Y Z where "Y \<subseteq> E \<inter> X" "Z \<subseteq> E \<inter> Y" "F Z"
    by blast
  then have "Z \<subseteq> E \<inter> X" "F Z" by auto
  then show "\<exists>Z \<subseteq> E \<inter> X. F Z" by blast
next
  assume "\<exists>Z \<subseteq> E \<inter> X. F Z"
  with assms show "\<exists>Y \<subseteq> E \<inter> X. E \<inter> Y \<noteq> {} \<and>
    (\<exists>Z \<subseteq> E \<inter> Y. F Z)"
    by (intro exI[of _ "E \<inter> X"]; simp)
qed

lemma rad_ok_body_idem: "rad_ok_body (rad_ok_body M) = rad_ok_body M"
  apply (rule ades_merge_ext, rule ades_obs_ext)
  subgoal for p q b s0 c X
  proof (cases "rad_trace_extensions s0 \<inter> X = {}")
    case True
    then show ?thesis by (simp add: rad_ok_body_eval)
  next
    case False
    have flat:
      "(\<exists>Y \<subseteq> rad_trace_extensions s0 \<inter> X.
        rad_trace_extensions s0 \<inter> Y \<noteq> {} \<and>
        (\<exists>Z \<subseteq> rad_trace_extensions s0 \<inter> Y.
          (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs a s0 d Z))) =
       (\<exists>Z \<subseteq> rad_trace_extensions s0 \<inter> X.
          (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs a s0 d Z))" for a d
      by (rule ok_merge_extensions_subset_twice[OF False])
    show ?thesis
      using False
      apply (simp only: rad_ok_body_obs)
      by (simp add: flat[simplified] split: if_splits)
  qed
  done


lemma rad_normalise_choices_exists_subset_extensions:
  "(\<exists>Y. Y \<subseteq> rad_trace_extensions s0 \<and> Y \<subseteq> X \<and>
    F (rad_normalise_choices s0 Y)) =
   (\<exists>Y \<subseteq> rad_normalise_choices s0 X. F Y)"
  using rad_normalise_choices_exists_subset[of "rad_trace_extensions s0 \<inter> X" F s0]
  by (simp add: rad_normalise_choices_extensions)

lemma rad_ok_body_RA2M_commute:
  "(rad_ok_body \<circ> RA2M) M = (RA2M \<circ> rad_ok_body) M"
  unfolding comp_apply
  apply (rule ades_merge_ext, rule ades_obs_ext)
  subgoal for p q b s0 c X
    apply (cases b; cases c; cases "des_vars.ok\<^sub>v p"; cases "des_vars.ok\<^sub>v q";
      cases "rad_trace_extensions s0 \<inter> X = {}")
    apply (simp_all add: rad_ok_body_eval RA2M_eval rad_merge_output_def
      rad_normalise_choices_extensions rad_normalise_choices_nonempty
      rad_zero_trace_extensions)
    apply (rule rad_normalise_choices_exists_subset_extensions)+
    done
  done

lemmas rad_ok_body_RA2M_commute' = rad_ok_body_RA2M_commute[simplified comp_apply]

lemma rad_ok_body_RA3M_absorb:
  "RA3M (rad_ok_body (RA3M M)) = RA3M (rad_ok_body M)"
  by (rule ades_merge_ext, rule ades_obs_ext;
      simp add: RA3M_eval rad_ok_body_eval
        split: if_splits)


lemma rad_ok_body_design:
  "(\<lambda>(x,out). ades_merge_eval (rad_ok_body M) x p q out) =
    RA1 (CSPA1 (H2 (PBMH_ades
      (\<lambda>(x,out). des_vars.ok\<^sub>v out = (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<and>
        ades_merge_eval M x p q out))))"
  by (simp add: rad_ok_body_def fun_eq_iff)

definition RADOKM ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "RADOKM M = RA2M (RA3M (rad_ok_body M))"

lemmas RADOKM_form = RADOKM_def

lemma rad_ok_body_mono:
  assumes "M \<sqsubseteq> N"
  shows "rad_ok_body M \<sqsubseteq> rad_ok_body N"
  apply (rule ades_merge_refineI)
  apply (simp only: rad_ok_body_design)
  apply (rule RA1_mono, rule CSPA1_mono)
  apply (simp only: H2_def)
  apply (rule seqr_mono)
   apply (rule PBMH_ades_mono)
  using assms by (auto simp: pred_refine_iff)

lemma RADOKM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> RADOKM M \<sqsubseteq> RADOKM N"
  unfolding RADOKM_def by (intro RA2M_mono RA3M_mono rad_ok_body_mono)

lemma RADOKM_Monotonic [closure]: "Monotonic RADOKM"
  by (rule MonotonicI, rule RADOKM_mono)

lemma RADOKM_idem: "RADOKM (RADOKM M) = RADOKM M"
  by (simp only: RADOKM_form rad_ok_body_RA2M_commute'
      RA2M_RA3M_commute RA2M_idem rad_ok_body_RA3M_absorb rad_ok_body_idem)

lemma RADOKM_Idempotent [closure]: "Idempotent RADOKM"
  by (simp add: Idempotent_def RADOKM_idem)

lemma RADOKM_healthy [closure]: "RADOKM M is RADOKM"
  by (simp add: Healthy_def' RADOKM_idem)


lemma rad_ok_body_SymMerge:
  "M is SymMerge \<Longrightarrow> (rad_ok_body M) is SymMerge"
  unfolding SymMerge_ades_observations
  apply (simp only: rad_ok_body_design)
  by (auto simp: fun_eq_iff conj_commute)

lemma RADOKM_SymMerge: "M is SymMerge \<Longrightarrow> (RADOKM M) is SymMerge"
  unfolding RADOKM_def
  by (intro RA2M_SymMerge RA3M_SymMerge rad_ok_body_SymMerge)

lemma RADOKM_design:
  "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) =
    RA3 (RA1 (CSPA1 (H2 (PBMH_ades
      (\<lambda>(x,out). des_vars.ok\<^sub>v out = (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<and>
        ades_merge_eval (RA2M M) x p q out)))))"
  by (simp only: RADOKM_def RA2M_RA3M_commute[symmetric]
      rad_ok_body_RA2M_commute'[symmetric];
      simp add: RA3M_eval rad_ok_body_def RA3_eval fun_eq_iff)

lemma RADOKM_design_PBMH [closure]:
  "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is PBMH_ades"
  unfolding RADOKM_design
  apply (intro RA3_PBMH_ades_closure RA1_PBMH_ades_closure)
  unfolding Healthy_def'
  apply (rule CSPA1_PBMH_ades_closure)
  by (simp add: PBMH_ades_H2_commute' PBMH_ades_idem)

lemma RADOKM_design_H2 [closure]:
  "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is H2"
  by (simp add: RADOKM_design Healthy_def' H2_RA3_commute H2_RA1_commute
      H2_CSPA1_commute H2_idem)

lemma RADOKM_design_RA1 [closure]:
  "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is RA1"
  by (simp add: RADOKM_design Healthy_def'
      RA1_RA3_commute[simplified comp_apply] RA1_idem)

lemma RADOKM_design_CSPA1 [closure]:
  "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is CSPA1"
  by (simp add: RADOKM_design Healthy_def' CSPA1_RA3_commute
      RA1_CSPA1_commute[simplified comp_apply, symmetric] CSPA1_idem)

lemma RADOKM_design_RA3 [closure]:
  "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is RA3"
  by (simp add: RADOKM_design Healthy_def' RA3_idem)

lemma RADOKM_RA2M [closure]: "RADOKM M is RA2M"
  by (simp add: RADOKM_def RA2M_healthy)

text \<open>
  The public operator first adds the conjunctive termination constraint and then
  applies the layer healthiness operator. Its choice-set policy comes from
  the supplied merge, subject to that healthiness transformation. The seed's
  conjunction of branch ok flags need not hold globally after completion.
\<close>

abbreviation rad_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) rad_merge_rel \<Rightarrow>
   ('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t::trace, 'e) reactive_angelic_design"
where "rad_par P M Q \<equiv> P \<parallel>\<^bsub>RADOKM M\<^esub> Q"

lemma rad_par_eval:
  "rad_par P M Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and>
      ades_merge_eval (RADOKM M) x p q out)"
proof -
  have eval: "par_by_merge P N Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval N x p q out)" for N
    by (cases x; cases out;
        simp add: par_by_merge_def par_sep_def; pred_auto; blast)
  show ?thesis by (rule eval)
qed

lemma rad_par_PBMH_closure [closure]: "rad_par P M Q is PBMH_ades"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is PBMH_ades"
    for p q by (rule RADOKM_design_PBMH)
  have slices: "PBMH_ades ((\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out)) (ades_obs b s0 c X) =
      (\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) (ades_obs b s0 c X)" for p q b s0 c X
    using healthy
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: PBMH_ades_obs rad_par_eval;
        use slices[unfolded PBMH_ades_obs case_prod_conv] in \<open>blast\<close>)
qed

lemma rad_par_H2_closure [closure]: "rad_par P M Q is H2"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is H2"
    for p q by (rule RADOKM_design_H2)
  have slices: "H2 ((\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out)) (ades_obs b s0 c X) =
      (\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) (ades_obs b s0 c X)" for p q b s0 c X
    using healthy
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: H2_obs rad_par_eval;
        use slices[unfolded H2_obs case_prod_conv] in \<open>blast\<close>)
qed

lemma rad_par_RA1_closure [closure]: "rad_par P M Q is RA1"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is RA1"
    for p q by (rule RADOKM_design_RA1)
  have slices: "RA1 ((\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out)) (ades_obs b s0 c X) =
      (\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) (ades_obs b s0 c X)" for p q b s0 c X
    using healthy
    by (auto simp: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: RA1_obs rad_par_eval;
        use slices[unfolded RA1_obs case_prod_conv] in \<open>blast\<close>)
qed

lemma rad_par_RA2_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and M :: "('t, 'e) rad_merge_rel"
  assumes "P is RA2" "Q is RA2"
  shows "rad_par P M Q is RA2"
proof -
  have healthy: "RADOKM M is RA2M" by (rule RADOKM_RA2M)
  have Pnorm: "P (x,out) = P (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x out
    using fun_cong[OF Healthy_if[OF assms(1)], of "(x,out)"]
    by (simp only: RA2_merge_eval)
  have Qnorm: "Q (x,out) = Q (rad_merge_input x,
      rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x out
    using fun_cong[OF Healthy_if[OF assms(2)], of "(x,out)"]
    by (simp only: RA2_merge_eval)
  have Mnorm: "ades_merge_eval (RADOKM M) x p q out =
      ades_merge_eval (RADOKM M) (rad_merge_input x)
        (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) p)
        (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) q)
        (rad_merge_output (astate.s\<^sub>v (des_vars.more x)) out)" for x p q out
    using arg_cong[where f="\<lambda>N. ades_merge_eval N x p q out",
      OF Healthy_if[OF healthy]]
    by (simp only: RA2M_eval)
  have reindex: "(\<exists>p q. F (rad_merge_output s0 p) (rad_merge_output s0 q)) =
      (\<exists>p q. F p q)" for F and s0 :: "('t, 'e) rad_state"
    by (metis rad_merge_output_surj)
  show ?thesis
  proof (rule Healthy_intro, rule ext, clarify)
    fix x out
    show "RA2 (rad_par P M Q) (x,out) = rad_par P M Q (x,out)"
      by (simp only: RA2_merge_eval rad_par_eval;
          subst Pnorm; subst Qnorm; subst Mnorm; rule reindex[symmetric])
  qed
qed

lemma rad_par_CSPA1_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is CSPA1" "Q is CSPA1"
  shows "rad_par P M Q is CSPA1"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is CSPA1"
    for p q by (rule RADOKM_design_CSPA1)
  have P: "P (ades_obs False s0 c X)"
    if "rad_trace_extensions s0 \<inter> X \<noteq> {}" for s0 c X
    using assms(1) that by (simp add: CSPA1_healthy_obs_iff)
  have Q: "Q (ades_obs False s0 c X)"
    if "rad_trace_extensions s0 \<inter> X \<noteq> {}" for s0 c X
    using assms(2) that by (simp add: CSPA1_healthy_obs_iff)
  have merge: "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) (ades_obs False s0 c X)"
    if "rad_trace_extensions s0 \<inter> X \<noteq> {}" for p q s0 c X
    using healthy that
    by (simp add: CSPA1_healthy_obs_iff)
  show ?thesis
    unfolding CSPA1_healthy_obs_iff
  proof (intro allI impI)
    fix s0 :: "('t, 'e) rad_state" and c :: bool
      and X :: "('t, 'e) rad_state set"
    assume ne: "rad_trace_extensions s0 \<inter> X \<noteq> {}"
    show "rad_par P M Q (ades_obs False s0 c X)"
      unfolding rad_par_eval
      using P[OF ne, of c] Q[OF ne, of c]
        merge[OF ne, of "\<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr>"
          "\<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr>" c]
      by auto
  qed
qed

lemma rad_par_RA3_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is RA3" "Q is RA3"
  shows "rad_par P M Q is RA3"
proof -
  have healthy: "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is RA3"
    for p q by (rule RADOKM_design_RA3)
  have waiting: "rad_par P M Q (x,out) = II_Rac (x,out)"
    if w: "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))" for x out
  proof -
    have Pw: "P (x,p) = II_Rac (x,p)" for p
      using RA3_healthy_wait_eval[OF assms(1) w] .
    have Qw: "Q (x,q) = II_Rac (x,q)" for q
      using RA3_healthy_wait_eval[OF assms(2) w] .
    have Mw: "ades_merge_eval (RADOKM M) x p q out = II_Rac (x,out)" for p q
    proof -
      have "(\<lambda>(x,out). ades_merge_eval (RADOKM M) x p q out) is RA3"
        by (rule healthy)
      from RA3_healthy_wait_eval[OF this w]
      show ?thesis by simp
    qed
    obtain y where y: "II_Rac (x,y)" by (rule II_Rac_has_result)
    show ?thesis
      using y by (simp add: rad_par_eval Pw Qw Mw; blast)
  qed
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp add: RA3_obs waiting)
qed

lemma rad_par_RAD_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "rad_par P M Q is RAD"
proof -
  let ?W = "rad_par P M Q"
  have pb: "PBMH_ades ?W = ?W"
    using rad_par_PBMH_closure by (simp add: Healthy_def')
  have h2: "H2 ?W = ?W"
    using rad_par_H2_closure by (simp add: Healthy_def')
  have c1: "CSPA1 ?W = ?W"
    using rad_par_CSPA1_closure[OF RAD_is_CSPA1_full[OF assms(1)]
      RAD_is_CSPA1_full[OF assms(2)]] by (simp add: Healthy_def')
  have r1: "RA1 ?W = ?W"
    using rad_par_RA1_closure by (simp add: Healthy_def')
  have r2: "RA2 ?W = ?W"
    using rad_par_RA2_closure[OF RA_is_RA2[OF RAD_is_RA[OF assms(1)]]
      RA_is_RA2[OF RAD_is_RA[OF assms(2)]]] by (simp add: Healthy_def')
  have r3: "RA3 ?W = ?W"
    using rad_par_RA3_closure[OF RA_is_RA3[OF RAD_is_RA[OF assms(1)]]
      RA_is_RA3[OF RAD_is_RA[OF assms(2)]]] by (simp add: Healthy_def')
  show ?thesis
    by (simp add: Healthy_def' RAD_def RA_def CSPA2_def pb h2 c1 r1 r2 r3)
qed

lemma rad_par_normalise:
  "rad_par P (RADOKM M) Q = rad_par P M Q"
  by (simp only: RADOKM_idem)

lemma rad_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2" "M1 \<sqsubseteq> M2"
  shows "rad_par P1 M1 Q1 \<sqsubseteq> rad_par P2 M2 Q2"
  using assms(1,2) RADOKM_mono[OF assms(3)]
  by (auto simp: pred_refine_iff rad_par_eval split: prod.splits; blast)

lemma rad_par_comm:
  assumes "M is SymMerge"
  shows "rad_par P M Q = rad_par Q M P"
  by (rule par_by_merge_comm; use RADOKM_SymMerge[OF assms] in \<open>simp add: Healthy_def'\<close>)

lemma rad_par_comm_iff:
  "RADOKM M is SymMerge \<longleftrightarrow> (\<forall>P Q. rad_par P M Q = rad_par Q M P)"
  by (rule ades_par_comm_iff)

lemma rad_par_assoc:
  assumes "RADOKM M is SymMerge" "AssocMerge (RADOKM M)"
  shows "rad_par (rad_par P M Q) M R =
    rad_par P M (rad_par Q M R)"
  by (rule ades_par_assoc[OF assms])

lemma rad_par_assoc_iff:
  assumes "RADOKM M is SymMerge"
  shows "AssocMerge (RADOKM M) \<longleftrightarrow>
    (\<forall>P Q R. rad_par (rad_par P M Q) M R =
      rad_par P M (rad_par Q M R))"
  by (rule ades_par_assoc_iff[OF assms])

lemma rad_par_disj_left:
  "rad_par (P \<or> Q) M R = (rad_par P M R \<or> rad_par Q M R)"
  by (auto simp: fun_eq_iff rad_par_eval disj_pred_def split: prod.splits)

lemma rad_par_disj_right:
  "rad_par P M (Q \<or> R) = (rad_par P M Q \<or> rad_par P M R)"
  by (auto simp: fun_eq_iff rad_par_eval disj_pred_def split: prod.splits)

lemma rad_par_false_left [simp]: "rad_par false M P = false"
  by (rule par_by_merge_left_false)

lemma rad_par_false_right [simp]: "rad_par P M false = false"
  by (rule par_by_merge_right_false)

end
