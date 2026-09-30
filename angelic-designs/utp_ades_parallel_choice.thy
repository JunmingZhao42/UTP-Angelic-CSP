section \<open>Angelic Design Parallel and Choice\<close>

theory utp_ades_parallel_choice
  imports utp_ades_parallel_lifted
begin

subsection \<open>Demonic Choice\<close>

text \<open>Demonic choice is predicate disjunction. Parallel distributes over it
  in either operand, without assumptions on the operands or merge.\<close>

lemma ades_par_demonic_left_distrib:
  "ades_par (P \<sqinter>\<^sub>D\<^sub>A Q) M R =
    (ades_par P M R \<sqinter>\<^sub>D\<^sub>A ades_par Q M R)"
  by (simp only: angelic_design_demonic ades_par_disj_left)

lemma ades_par_demonic_right_distrib:
  "ades_par P M (Q \<sqinter>\<^sub>D\<^sub>A R) =
    (ades_par P M Q \<sqinter>\<^sub>D\<^sub>A ades_par P M R)"
  by (simp only: angelic_design_demonic ades_par_disj_right)

subsection \<open>Angelic Choice\<close>

text \<open>Angelic choice is predicate conjunction. Putting the choice inside
  parallel requires one pair of branch results: the left result satisfies
  P, and the right result satisfies both Q and R.

  Putting the choice outside parallel allows two separate pairs. Each
  pair has the same initial and final observations, but even the results
  chosen for P may differ. The following equations expose these witnesses.\<close>

lemma ades_par_angelic_right_eval:
  "ades_par P M (Q \<squnion>\<^sub>D\<^sub>A R) (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> R (x,q) \<and>
      ades_merge_eval M x p q out)"
  by (auto simp: ades_par_eval)

lemma ades_par_angelic_separate_eval:
  "(ades_par P M Q \<squnion>\<^sub>D\<^sub>A ades_par P M R) (x,out) \<longleftrightarrow>
    (\<exists>p q p' q'. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval M x p q out \<and>
      P (x,p') \<and> R (x,q') \<and> ades_merge_eval M x p' q' out)"
  by (auto simp: ades_par_eval; blast)

text \<open>A shared pair also supplies both separate witnesses. This proves
  implication from parallel of angelic choice to angelic choice of the
  two parallels. Refinement reverses implication, giving the direction
  below without any healthiness assumptions.\<close>

lemma ades_par_angelic_left_refine:
  "(ades_par P M R \<squnion>\<^sub>D\<^sub>A ades_par Q M R) \<sqsubseteq>
    ades_par (P \<squnion>\<^sub>D\<^sub>A Q) M R"
  by (auto simp: pred_refine_iff ades_par_eval
      conj_pred_def split: prod.splits)

lemma ades_par_angelic_right_refine:
  "(ades_par P M Q \<squnion>\<^sub>D\<^sub>A ades_par P M R) \<sqsubseteq>
    ades_par P M (Q \<squnion>\<^sub>D\<^sub>A R)"
  by (simp only: pred_refine_iff split_paired_All ades_par_angelic_right_eval
      ades_par_angelic_separate_eval; blast)

subsubsection \<open>A Sufficient Merge Condition\<close>

text \<open>We combine two alternative observations of one branch by taking the
  union of their choice sets and the disjunction of their ok flags.
  Thus p and p' are alternatives for the left branch, while q and q' are
  alternatives for the right branch. The disjunction combines alternative
  flags of the same branch. The final ok flag and choice set stay fixed.

  Every A-healthy predicate that accepts either observation accepts this
  combined observation: PBMH permits enlarging the choice set, and H2
  permits changing the output ok flag from False to True.

  The merge condition below requires two accepted pairs of branch results
  to remain accepted after this combination, with the initial and final
  observations held fixed. This is a sufficient condition for angelic
  distribution; it need not be the weakest one.\<close>

abbreviation ades_output_union ::
  "'s achoices des_vars_ext \<Rightarrow> 's achoices des_vars_ext \<Rightarrow>
   's achoices des_vars_ext"
where
  "ades_output_union p q \<equiv>
    ades_output (des_vars.ok\<^sub>v p \<or> des_vars.ok\<^sub>v q)
      (achoices.ac\<^sub>v (des_vars.more p) \<union>
       achoices.ac\<^sub>v (des_vars.more q))"

lemma A_output_union:
  assumes healthy: "P is A" and accepted: "P (x,p)"
  shows "P (x, ades_output_union p q)"
proof -
  have up: "P (ades_obs b s0 c X) \<Longrightarrow>
    P (ades_obs b s0 (c \<or> d) (X \<union> Y))" for b s0 c X d Y
    using A_obs[of P b s0 c X] A_obs[of P b s0 "c \<or> d" "X \<union> Y"]
    unfolding Healthy_if[OF healthy]
    by blast
  show ?thesis
    using up accepted
    by (cases x; cases "des_vars.more x"; cases p; cases "des_vars.more p";
        cases q; cases "des_vars.more q"; auto)
qed

definition ades_merge_union_closed :: "'s ades_merge_rel \<Rightarrow> bool" where
  "ades_merge_union_closed M \<equiv>
    (\<forall>x p q p' q' out.
      ades_merge_eval M x p q out \<longrightarrow>
      ades_merge_eval M x p' q' out \<longrightarrow>
      ades_merge_eval M x (ades_output_union p p')
        (ades_output_union q q') out)"


lemma ades_merge_union_closedD:
  assumes "ades_merge_union_closed M"
    "ades_merge_eval M x p q out" "ades_merge_eval M x p' q' out"
  shows "ades_merge_eval M x (ades_output_union p p')
    (ades_output_union q q') out"
  using assms unfolding ades_merge_union_closed_def by blast


text \<open>For fixed x, the set {out. ades_merge_eval M x p q out} contains all
  final observations permitted by one branch pair. Two pairs may have
  different such sets. The condition preserves their intersection: every
  common final observation is still permitted by the combined pair.
  It does not require the two branches, or the two output collections,
  to be equal.\<close>

lemma ades_merge_union_closed_outputs_iff:
  "ades_merge_union_closed M \<longleftrightarrow>
    (\<forall>x p q p' q'.
      {out. ades_merge_eval M x p q out} \<inter>
        {out. ades_merge_eval M x p' q' out} \<subseteq>
      {out. ades_merge_eval M x (ades_output_union p p')
        (ades_output_union q q') out})"
  unfolding ades_merge_union_closed_def by (auto simp: subset_iff)

text \<open>With A-healthy operands, combining separate witnesses preserves
  acceptance by the predicates on each branch. Union closure then preserves
  the same final observation, supplying a shared pair for the reverse
  implication. The stronger law below combines choices in both operands;
  the two one-sided distribution laws follow by repeating an operand.\<close>

lemma ades_par_angelic_distrib:
  assumes hp: "P is A" and hq: "Q is A" and hr: "R is A" and hs: "S is A"
    and merge: "ades_merge_union_closed M"
  shows "ades_par (P \<squnion>\<^sub>D\<^sub>A Q) M (R \<squnion>\<^sub>D\<^sub>A S) =
    (ades_par P M R \<squnion>\<^sub>D\<^sub>A ades_par Q M S)"
proof (rule antisym)
  show "ades_par (P \<squnion>\<^sub>D\<^sub>A Q) M (R \<squnion>\<^sub>D\<^sub>A S) \<le>
    (ades_par P M R \<squnion>\<^sub>D\<^sub>A ades_par Q M S)"
    by (auto simp: le_fun_def ades_par_eval split: prod.splits)
  show "(ades_par P M R \<squnion>\<^sub>D\<^sub>A ades_par Q M S) \<le>
    ades_par (P \<squnion>\<^sub>D\<^sub>A Q) M (R \<squnion>\<^sub>D\<^sub>A S)"
  proof (clarsimp simp: le_fun_def ades_par_eval split: prod.splits)
    fix x out p p' q q'
    assume p: "P (x,p)" and p': "Q (x,p')" and q: "R (x,q)"
      and m: "ades_merge_eval M x p q out" and q': "S (x,q')"
      and m': "ades_merge_eval M x p' q' out"
    have pp: "P (x, ades_output_union p p')"
      by (rule A_output_union[OF hp p])
    have qp: "Q (x, ades_output_union p p')"
      using A_output_union[OF hq p', of p]
      by (simp add: Un_commute disj_commute)
    have rq: "R (x, ades_output_union q q')"
      by (rule A_output_union[OF hr q])
    have sq: "S (x, ades_output_union q q')"
      using A_output_union[OF hs q', of q]
      by (simp add: Un_commute disj_commute)
    have mm: "ades_merge_eval M x (ades_output_union p p')
      (ades_output_union q q') out"
      by (rule ades_merge_union_closedD[OF merge m m'])
    show "\<exists>p. P (x,p) \<and> Q (x,p) \<and> (\<exists>q.
      R (x,q) \<and> S (x,q) \<and> ades_merge_eval M x p q out)"
      using pp qp rq sq mm by blast
  qed
qed

lemma ades_par_angelic_left_distrib:
  assumes "P is A" "Q is A" "R is A" "ades_merge_union_closed M"
  shows "ades_par (P \<squnion>\<^sub>D\<^sub>A Q) M R =
    (ades_par P M R \<squnion>\<^sub>D\<^sub>A ades_par Q M R)"
  using ades_par_angelic_distrib[OF assms(1-3,3,4)] by simp

lemma ades_par_angelic_right_distrib:
  assumes "P is A" "Q is A" "R is A" "ades_merge_union_closed M"
  shows "ades_par P M (Q \<squnion>\<^sub>D\<^sub>A R) =
    (ades_par P M Q \<squnion>\<^sub>D\<^sub>A ades_par P M R)"
  using ades_par_angelic_distrib[OF assms(1,1-4)] by simp

subsection \<open>Counterexamples\<close>

subsubsection \<open>Angelic Choice and A2\<close>

text \<open>Each Boolean-choice design satisfies A and A2, but their angelic
  choice need not satisfy A2.\<close>

lemma ades_bool_angelic_not_A2:
  "\<not> ((ades_bool_choice False \<squnion>\<^sub>D\<^sub>A ades_bool_choice True) is A2)"
proof (rule notI)
  assume h: "(ades_bool_choice False \<squnion>\<^sub>D\<^sub>A ades_bool_choice True) is A2"
  have at: "A2 (ades_bool_choice False \<squnion>\<^sub>D\<^sub>A ades_bool_choice True)
      (ades_obs True False True UNIV) =
    (ades_bool_choice False \<squnion>\<^sub>D\<^sub>A ades_bool_choice True)
      (ades_obs True False True UNIV)"
    by (simp only: Healthy_if[OF h])
  from at show False by (simp add: A2_obs ades_bool_choice_eval)
qed

subsubsection \<open>A Merge Allowing Larger Branch Sets\<close>

text \<open>The set merge lifted from Boolean XOR fails angelic distribution.
  P can offer False or True demonically. At the final set {False}, the
  separate parallel terms use False with False and True with True.
  Combining the right operands angelically requires both Boolean values.
  No nonempty left set can then keep every XOR result in {False}.
  This merge allows larger branch sets; the failure is not a consequence
  of restricting branch results to singletons.\<close>

lemma lift_merge_angelic_counterexample:
  defines "j \<equiv> (\<lambda>(m,z). z = (mrg_left\<^sub>v m \<noteq> mrg_right\<^sub>v m)) :: bool merge"
    and "P \<equiv> ades_bool_choice False \<sqinter>\<^sub>D\<^sub>A ades_bool_choice True"
    and "Q \<equiv> ades_bool_choice False"
    and "R \<equiv> ades_bool_choice True"
    and "obs \<equiv> ades_obs True False True {False}"
  shows "(ades_par P (lift_merge j) Q \<squnion>\<^sub>D\<^sub>A
           ades_par P (lift_merge j) R) obs"
    and "\<not> ades_par P (lift_merge j) (Q \<squnion>\<^sub>D\<^sub>A R) obs"
proof -
  show "(ades_par P (lift_merge j) Q \<squnion>\<^sub>D\<^sub>A
           ades_par P (lift_merge j) R) obs"
    by (auto simp: j_def P_def Q_def R_def obs_def ades_par_eval choices_ex
        lift_merge_obs[simplified] ades_bool_choice_eval; blast)
  show "\<not> ades_par P (lift_merge j) (Q \<squnion>\<^sub>D\<^sub>A R) obs"
    unfolding j_def P_def Q_def R_def obs_def
    apply (simp only: ades_par_eval choices_ex lift_merge_obs[simplified]
        ades_bool_choice_eval split_beta fst_conv snd_conv
        des_vars.select_convs mrg.select_convs achoices.select_convs inf_apply sup_apply)

    by force
qed

subsection \<open>A Merge Satisfying the Union Condition\<close>

text \<open>This merge accepts completed branches with nonempty choice sets when
  the final set contains their union. It satisfies the sufficient condition
  above, as well as A0m, A1m and A3m w.

  It is not A2m-healthy on Boolean states. Its parallel composition can
  require both Boolean values, just as angelic choice can.\<close>

definition ades_union_merge :: "'s ades_merge_rel" where
  [pred]: "ades_union_merge \<equiv> (\<lambda>(m,out).
    \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
     des_vars.ok\<^sub>v (mrg_right\<^sub>v m) \<and> des_vars.ok\<^sub>v out \<and>
     achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)) \<noteq> {} \<and>
     achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m)) \<noteq> {} \<and>
     achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)) \<union>
       achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m)) \<subseteq>
       achoices.ac\<^sub>v (des_vars.more out)))"

lemma ades_union_merge_union_closed:
  "ades_merge_union_closed ades_union_merge"
  by (auto simp: ades_merge_union_closed_def ades_union_merge_def)

lemma ades_union_merge_A0m [closure]: "ades_union_merge is A0m"
  by (auto simp: A0m_healthy_iff A0_healthy_obs_iff ades_union_merge_def)

lemma ades_union_merge_A1m [closure]: "ades_union_merge is A1m"
  by (unfold A1m_healthy_iff; intro allI Healthy_intro; rule ades_obs_ext;
      auto simp: A1_obs ades_union_merge_def; blast)

lemma ades_union_merge_A3m [closure]: "ades_union_merge is A3m w"
  by (rule Healthy_intro, rule ades_merge_ext, rule ades_obs_ext;
      simp only: A3m_obs; auto simp: ades_union_merge_def)

lemma ades_union_parallel_bool:
  "ades_par (ades_bool_choice a) ades_union_merge (ades_bool_choice b) =
    (ades_bool_choice a \<squnion>\<^sub>D\<^sub>A ades_bool_choice b)"
  by (rule ades_obs_ext;
      auto simp: ades_par_eval choices_ex ades_union_merge_def ades_bool_choice_eval;
      blast)

lemma ades_union_merge_not_A2m:
  "\<not> ((ades_union_merge :: bool ades_merge_rel) is A2m)"
proof (rule notI)
  assume healthy: "(ades_union_merge :: bool ades_merge_rel) is A2m"
  have "ades_par (ades_bool_choice False) ades_union_merge (ades_bool_choice True) is A2"
    by (rule ades_par_A2_closure[OF healthy])
  then show False
    using ades_bool_angelic_not_A2 by (simp only: ades_union_parallel_bool)
qed

end
