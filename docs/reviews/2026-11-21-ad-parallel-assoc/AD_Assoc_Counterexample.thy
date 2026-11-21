theory AD_Assoc_Counterexample
  imports "UTP-Angelic-Designs.utp_ades"
begin

text \<open> We want to know whether the A2 premise of @{thm [source] ades_par_assoc} can be
  dropped while keeping its premises on j. It cannot: with a nondeterministic merge,
  one operand with angelic choice already breaks associativity.
  States are booleans, False = 0 and True = 1. \<close>

(* j(0,x) = {x}; j(1,1) = {0,1} *)
definition jnd :: "bool merge" where
  "jnd = (\<lambda>(m, z). (mrg_left\<^sub>v m \<and> mrg_right\<^sub>v m) \<or> z = (mrg_left\<^sub>v m \<or> mrg_right\<^sub>v m))"

lemma jnd_eval [simp]: "merge_eval jnd s0 p q z \<longleftrightarrow> (p \<and> q) \<or> z = (p \<or> q)"
  by (simp add: jnd_def)

lemma jnd_SymMerge: "jnd is SymMerge"
  by (simp add: SymMerge_eval; blast)

lemma jnd_AssocMerge: "AssocMerge jnd"
  by (simp add: AssocMerge_iff ex_bool_eq; blast)

lemma jnd_mergeable: "mergeable jnd"
  by simp

lemma jnd_not_Functional: "\<not> Functional jnd"
  by (simp add: Functional_merge_eval) (metis (full_types))

(* <0> and <1>: assign 0 or 1 to the whole state *)
abbreviation zero :: "bool angelic_design" where "zero \<equiv> assigns_ades 1\<^sub>L (\<lambda>_. False)"
abbreviation one :: "bool angelic_design" where "one \<equiv> assigns_ades 1\<^sub>L (\<lambda>_. True)"

lemma assign_obs:
  "assigns_ades 1\<^sub>L (\<lambda>_. v) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow> (ok0 \<longrightarrow> ok' \<and> v \<in> ac')"
  by (simp add: assigns_ades_def assign_arel_def arel_to_ades_def; pred_auto)

lemma demonic_obs: "(P \<sqinter>\<^sub>D\<^sub>A Q) x \<longleftrightarrow> P x \<or> Q x"
  by (simp add: sup_fun_def sup_bool_def)

lemma angelic_obs: "(P \<squnion>\<^sub>D\<^sub>A Q) x \<longleftrightarrow> P x \<and> Q x"
  by (simp add: inf_fun_def inf_bool_def)

lemma par_obs:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR.
      P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      (\<not>ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (okL \<and> okR \<longrightarrow> (ok' \<and>
          (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s'))))))"
  by (simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified])

text \<open> The two bracketings of <1> \<parallel> <1> \<parallel> (<0> \<squnion> <1>) differ. \<close>

(* <1> \<parallel> <1> = <0> \<sqinter> <1>: the merge of 1 and 1 is demonic *)
lemma one_par_one: "one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> one = zero \<sqinter>\<^sub>D\<^sub>A one"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  show "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> one) (ades_obs ok0 s0 ok' ac') = (zero \<sqinter>\<^sub>D\<^sub>A one) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: par_obs assign_obs demonic_obs)
  next
    case True
    have "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> one) (ades_obs True s0 ok' ac') \<longleftrightarrow> ok' \<and> ac' \<noteq> {}"
    proof
      assume "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> one) (ades_obs True s0 ok' ac')"
      then obtain acL acR where "True \<in> acL" "True \<in> acR"
        and m: "ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval jnd s0 sL sR s')"
        by (auto simp: par_obs assign_obs)
      then show "ok' \<and> ac' \<noteq> {}" by blast
    next
      assume h: "ok' \<and> ac' \<noteq> {}"
      show "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> one) (ades_obs True s0 ok' ac')"
        apply (simp only: par_obs assign_obs)
        apply (rule exI[where x=True], rule exI[where x="{True}"],
               rule exI[where x=True], rule exI[where x="{True}"])
        using h by auto
    qed
    then show ?thesis
      using True by (simp add: demonic_obs assign_obs) (metis (full_types) ex_in_conv)
  qed
qed

(* <1> \<parallel> (<0> \<squnion> <1>) = <1>: the angel answers 1 with 0 *)
lemma one_par_zero_or_one: "one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one) = one"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  show "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs ok0 s0 ok' ac') = one (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: par_obs assign_obs angelic_obs)
  next
    case True
    have "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs True s0 ok' ac') \<longleftrightarrow> ok' \<and> True \<in> ac'"
    proof
      assume "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs True s0 ok' ac')"
      then obtain acL acR where "True \<in> acL" "False \<in> acR"
        and m: "ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval jnd s0 sL sR s')"
        by (auto simp: par_obs assign_obs angelic_obs)
      then show "ok' \<and> True \<in> ac'" by fastforce
    next
      assume h: "ok' \<and> True \<in> ac'"
      show "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs True s0 ok' ac')"
        apply (simp only: par_obs assign_obs angelic_obs)
        apply (rule exI[where x=True], rule exI[where x="{True}"],
               rule exI[where x=True], rule exI[where x="{False, True}"])
        using h by auto
    qed
    then show ?thesis
      using True by (simp add: assign_obs)
  qed
qed

(* (<0> \<sqinter> <1>) \<parallel> (<0> \<squnion> <1>) = <1>: the angel sees the demon's result *)
lemma zero_or_one_par: "(zero \<sqinter>\<^sub>D\<^sub>A one) \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one) = one"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  show "((zero \<sqinter>\<^sub>D\<^sub>A one) \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs ok0 s0 ok' ac') =
      one (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: par_obs assign_obs angelic_obs demonic_obs)
  next
    case True
    have "((zero \<sqinter>\<^sub>D\<^sub>A one) \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs True s0 ok' ac') \<longleftrightarrow>
        ok' \<and> True \<in> ac'"
    proof
      assume "((zero \<sqinter>\<^sub>D\<^sub>A one) \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs True s0 ok' ac')"
      then obtain acL acR where "False \<in> acL \<or> True \<in> acL" "False \<in> acR" "True \<in> acR"
        and m: "ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval jnd s0 sL sR s')"
        by (auto simp: par_obs assign_obs angelic_obs demonic_obs)
      then show "ok' \<and> True \<in> ac'" by fastforce
    next
      assume h: "ok' \<and> True \<in> ac'"
      show "((zero \<sqinter>\<^sub>D\<^sub>A one) \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one)) (ades_obs True s0 ok' ac')"
        apply (simp only: par_obs assign_obs angelic_obs demonic_obs)
        apply (rule exI[where x=True], rule exI[where x="{True}"],
               rule exI[where x=True], rule exI[where x="{False, True}"])
        using h by auto
    qed
    then show ?thesis
      using True by (simp add: assign_obs)
  qed
qed

theorem ades_par_not_assoc_nondet:
  "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> one) \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one) \<noteq>
   one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one))"
proof
  assume "(one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> one) \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one) =
    one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (one \<parallel>\<^sub>A\<^sub>D\<^bsub>jnd\<^esub> (zero \<squnion>\<^sub>D\<^sub>A one))"
  then have "one = zero \<sqinter>\<^sub>D\<^sub>A one"
    by (simp only: one_par_one zero_or_one_par one_par_zero_or_one)
  then have "one (ades_obs True False True {False}) = (zero \<sqinter>\<^sub>D\<^sub>A one) (ades_obs True False True {False})"
    by simp
  then show False
    by (simp add: assign_obs demonic_obs)
qed

text \<open> Only the third operand has angelic choice: <1> is A2, and <0> \<squnion> <1> is not. \<close>

lemma one_A2: "one is A2"
  by (rule Healthy_intro, rule ades_obs_ext) (auto simp: A2_obs assign_obs)

lemma zero_or_one_not_A2: "\<not> (zero \<squnion>\<^sub>D\<^sub>A one is A2)"
proof
  assume "zero \<squnion>\<^sub>D\<^sub>A one is A2"
  then have "A2 (zero \<squnion>\<^sub>D\<^sub>A one) (ades_obs True False True {False, True}) =
      (zero \<squnion>\<^sub>D\<^sub>A one) (ades_obs True False True {False, True})"
    by (simp add: Healthy_def')
  then show False
    by (simp only: A2_obs angelic_obs assign_obs) simp
qed

end
