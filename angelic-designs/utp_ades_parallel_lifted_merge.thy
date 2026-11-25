section \<open>AD Lifted State Merge\<close>

theory utp_ades_parallel_lifted_merge
  imports utp_ades_parallel_choice_lift
begin

text \<open>Lifting a state merge to AD through choice sets.\<close>

subsection \<open>Construction\<close>

text \<open>The AD merge lifts the design merge of @{term j} through choice sets.\<close>

(* merge_ades j = H3m (H1m (ABm (ac'_lift_merge (merge_des_raw j)))) *)
definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "merge_ades j \<equiv> H3m (H1m (ABm (ac'_lift_merge (merge_des_raw j))))"

lemma merge_ades_completion [simp]: "merge_ades j ;; II\<^sub>D = merge_ades j"
  by (simp add: merge_ades_def H3m_def seqr_assoc)

subsection \<open>Evaluation\<close>

text \<open>Started merges require nonempty branch sets and a witness for every state pair.
  Both branches terminating requires witnesses in the final set; divergence releases it.\<close>

lemma merge_ades_obs:
  "ades_merge_obs (merge_ades j) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
    (\<not> ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow>
        (ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
  unfolding merge_ades_def
  apply (simp only: ac'_lift_merge_completion_obs)
  apply (simp add: merge_des_raw_def)
  by (cases ok0; cases okL; cases okR; cases ok'; simp_all; blast intro: exI[where x=UNIV])

lemma merge_ades_design_lift:
  "merge_ades j = H3m (H1m (ABm (ac'_lift_merge (merge_des j))))"
  apply (rule ades_merge_ext)
  apply (rename_tac ok0 s0 okL acL okR acR ok' ac')
  apply (simp only: merge_ades_obs ac'_lift_merge_completion_obs merge_des_expand simp_thms)
  by (case_tac "okL \<and> okR"; auto; blast intro: exI[where x=UNIV])

lemma merge_ades_unfold:
  "merge_ades j = (\<lambda>(m,z).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        acL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        acR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        ac' = achoices.ac\<^sub>v (des_vars.more z)
    in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
       (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)
          \<longrightarrow> (des_vars.ok\<^sub>v z \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
  by (rule ades_merge_ext; simp add: merge_ades_obs[simplified] Let_def)

subsection \<open>Healthiness, Symmetry and Associativity\<close>

text \<open>The lifted merge satisfies all the healthiness conditions above, for every j.\<close>

lemma merge_ades_is_H1m [closure]: "merge_ades j is H1m"
  by (simp add: Healthy_def' merge_ades_def H3m_def H1m_def; pred_auto)

lemma merge_ades_is_H2m [closure]: "merge_ades j is H2m"
  by (simp add: Healthy_def' H2m_def merge_ades_def H3m_def seqr_assoc skip_d_absorb_J_1)

lemma merge_ades_is_HDm [closure]: "merge_ades j is HDm"
  by (rule HDm_intro[OF merge_ades_is_H1m merge_ades_is_H2m])

lemma merge_ades_is_H3m [closure]: "merge_ades j is H3m"
  by (simp add: Healthy_def' merge_ades_def H3m_Idempotent[unfolded Idempotent_def])

lemma merge_ades_is_A0m [closure]: "merge_ades j is A0m"
  unfolding Healthy_def'
  by (rule ades_merge_ext)
     (auto simp: A0m_eval merge_ades_obs[simplified] Let_def; blast)

lemma merge_ades_is_A1m [closure]: "merge_ades j is A1m"
  unfolding Healthy_def'
  by (rule ades_merge_ext)
     (auto simp: A1m_eval merge_ades_obs[simplified] Let_def; blast)

lemma merge_ades_is_ADm [closure]: "merge_ades j is ADm"
  by (simp add: ADm_healthy_iff merge_ades_is_A0m merge_ades_is_A1m)

lemma merge_ades_is_A2m [closure]: "merge_ades j is A2m"
  unfolding Healthy_def'
  by (rule ades_merge_ext) (auto simp: A2m_obs[simplified] merge_ades_obs[simplified])

lemma merge_ades_SymMerge [closure]:
  assumes "j is SymMerge"
  shows "merge_ades j is SymMerge"
  using assms
  by (simp add: Healthy_def' fun_eq_iff merge_ades_unfold; pred_auto; blast)

text \<open>We want AD parallel to be associative for all operands when j is deterministic,
  so need the lifted merge to be associative. When j is a total function f, merging in
  either order needs f(f(a,b),c) \<in> ac' for all offered a, b and c.\<close>

lemma merge_ades_AssocMerge:
  fixes j :: "'s merge"
  assumes det: "Functional j" and tot: "mergeable j" and assoc: "AssocMerge j"
  shows "AssocMerge (merge_ades j)"
proof -
  obtain f where f: "\<And>s sL sR s'. merge_eval j s sL sR s' \<longleftrightarrow> s' = f s sL sR"
    using mergeable_Functional_fun[OF tot det] by blast
  have fcyc: "f s (f s sP sQ) sR = f s (f s sQ sR) sP" for s sP sQ sR
    using assoc[unfolded AssocMerge_iff, rule_format, of s sP sQ sR "f s (f s sP sQ) sR"]
    by (simp add: f)
  (* one cyclic step; three steps return to the start *)
  have rot: "\<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<forall>sP\<in>acP. f s (f s sQ sR) sP \<in> Z"
    if h: "\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. f s (f s sP sQ) sR \<in> Z" for s acP acQ acR Z
  proof (intro ballI)
    fix sQ sR sP assume "sQ \<in> acQ" "sR \<in> acR" "sP \<in> acP"
    then have "f s (f s sP sQ) sR \<in> Z" using h by blast
    then show "f s (f s sQ sR) sP \<in> Z" by (metis fcyc)
  qed
  have rotate: "(\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. f s (f s sP sQ) sR \<in> Z) \<longleftrightarrow>
      (\<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<forall>sP\<in>acP. f s (f s sQ sR) sP \<in> Z)" for s acP acQ acR Z
    using rot[of acP acQ acR s Z] rot[of acQ acR acP s Z] rot[of acR acP acQ s Z] by blast
  have started:
    "merge_eval (merge_ades j) \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
        (ades_output okL acL) (ades_output okR acR) (ades_output ok' ac') \<longleftrightarrow>
     acL \<noteq> {} \<and> acR \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac'))"
    for s0 okL acL okR acR ok' ac'
    by (simp add: merge_ades_obs[simplified] f)
  (* the smallest middle set is the image of the first merge *)
  have middle:
    "(\<exists>okU acU. (acP \<noteq> {} \<and> acQ \<noteq> {} \<and> (okP \<and> okQ \<longrightarrow> okU \<and> (\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. g sP sQ \<in> acU))) \<and>
        (acU \<noteq> {} \<and> acR \<noteq> {} \<and> (okU \<and> okR \<longrightarrow> ok' \<and> (\<forall>u\<in>acU. \<forall>sR\<in>acR. g u sR \<in> Z)))) \<longleftrightarrow>
     acP \<noteq> {} \<and> acQ \<noteq> {} \<and> acR \<noteq> {} \<and>
     (okP \<and> okQ \<and> okR \<longrightarrow> ok' \<and> (\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. g (g sP sQ) sR \<in> Z))"
    (is "?L \<longleftrightarrow> ?R")
    for g :: "'s \<Rightarrow> 's \<Rightarrow> 's" and acP acQ acR Z :: "'s set" and okP okQ okR ok' :: bool
  proof
    assume ?L
    then show ?R by blast
  next
    assume r: ?R
    let ?acU = "{g sP sQ | sP sQ. sP \<in> acP \<and> sQ \<in> acQ}"
    have ne: "?acU \<noteq> {}" using r by fastforce
    show ?L
      by (rule exI[where x="okP \<and> okQ"], rule exI[where x="?acU"]) (use r ne in blast)
  qed
  show ?thesis
    unfolding AssocMerge_iff
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okP acP okQ acQ okR acR ok' ac'
      apply (cases ok0)
       apply (simp only: choices_ex started middle rotate[of acP acQ acR s0 ac'])
       apply blast
      by (simp add: choices_ex merge_ades_obs[simplified])
    done
qed

text \<open>We want associativity for nondivergent operands even when j is partial, so we
  guard the merge to nondivergent branches, as for designs. Then a deterministic j is
  enough: both merge orders need the merge of sP, sQ and then sR to exist and lie in ac'.\<close>

lemma merge_ades_guard_AssocMerge:
  fixes j :: "'s merge"
  assumes det: "Functional j" and assoc: "AssocMerge j"
  shows "AssocMerge (merge_guard (\<lambda>x z. des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z) (merge_ades j))"
proof -
  have uniq: "u = v" if "merge_eval j s sL sR u" "merge_eval j s sL sR v" for s sL sR u v
    using det[unfolded Functional_merge_eval] that by blast
  have Tcyc: "(\<exists>u. merge_eval j s sP sQ u \<and> merge_eval j s u sR s') \<longleftrightarrow>
      (\<exists>u. merge_eval j s sQ sR u \<and> merge_eval j s u sP s')" for s sP sQ sR s'
    by (rule assoc[unfolded AssocMerge_iff, rule_format])
  (* one cyclic step; three steps return to the start *)
  have rot: "\<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<forall>sP\<in>acP. \<exists>s'\<in>Z. \<exists>u. merge_eval j s sQ sR u \<and> merge_eval j s u sP s'"
    if h: "\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<exists>s'\<in>Z. \<exists>u. merge_eval j s sP sQ u \<and> merge_eval j s u sR s'"
    for s acP acQ acR Z
  proof (intro ballI)
    fix sQ sR sP assume "sQ \<in> acQ" "sR \<in> acR" "sP \<in> acP"
    then have "\<exists>s'\<in>Z. \<exists>u. merge_eval j s sP sQ u \<and> merge_eval j s u sR s'" using h by blast
    then show "\<exists>s'\<in>Z. \<exists>u. merge_eval j s sQ sR u \<and> merge_eval j s u sP s'"
      using Tcyc[of s sP sQ sR] by blast
  qed
  have rotate:
    "(\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<exists>s'\<in>Z. \<exists>u. merge_eval j s sP sQ u \<and> merge_eval j s u sR s') \<longleftrightarrow>
     (\<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<forall>sP\<in>acP. \<exists>s'\<in>Z. \<exists>u. merge_eval j s sQ sR u \<and> merge_eval j s u sP s')"
    for s acP acQ acR Z
    by (rule iffI) (erule rot, erule rot[THEN rot])
  have started:
    "merge_eval (merge_guard (\<lambda>x z. des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z) (merge_ades j))
        \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
        (ades_output okL acL) (ades_output okR acR) (ades_output ok' ac') \<longleftrightarrow>
     okL \<and> okR \<and> acL \<noteq> {} \<and> acR \<noteq> {} \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
     ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')"
    for s0 okL acL okR acR ok' ac'
    by (auto simp: merge_guard_eval merge_ades_obs[simplified])
  (* the middle set holds every result of the first merge *)
  have middle:
    "(\<exists>okU acU.
        (okP \<and> okQ \<and> acP \<noteq> {} \<and> acQ \<noteq> {} \<and> (\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<exists>s'. merge_eval j s0 sP sQ s') \<and>
         okU \<and> (\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<exists>u\<in>acU. merge_eval j s0 sP sQ u)) \<and>
        (okU \<and> okR \<and> acU \<noteq> {} \<and> acR \<noteq> {} \<and> (\<forall>u\<in>acU. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 u sR s') \<and>
         ok' \<and> (\<forall>u\<in>acU. \<forall>sR\<in>acR. \<exists>s'\<in>Z. merge_eval j s0 u sR s'))) \<longleftrightarrow>
     okP \<and> okQ \<and> okR \<and> acP \<noteq> {} \<and> acQ \<noteq> {} \<and> acR \<noteq> {} \<and> ok' \<and>
     (\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<exists>s'\<in>Z. \<exists>u. merge_eval j s0 sP sQ u \<and> merge_eval j s0 u sR s')"
    (is "?L \<longleftrightarrow> ?R")
    for s0 acP acQ acR Z okP okQ okR ok'
  proof
    assume ?L
    then show ?R by blast
  next
    assume r: ?R
    let ?acU = "{u. \<exists>sP\<in>acP. \<exists>sQ\<in>acQ. merge_eval j s0 sP sQ u}"
    have uz: "\<exists>s'\<in>Z. merge_eval j s0 u sR s'" if "u \<in> ?acU" "sR \<in> acR" for u sR
      using that r uniq by blast
    show ?L
      by (rule exI[where x=True], rule exI[where x="?acU"]) (use r uz in blast)
  qed
  show ?thesis
    unfolding AssocMerge_iff
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okP acP okQ acQ okR acR ok' ac'
      apply (cases ok0)
       apply (simp only: choices_ex started middle
          rotate[where s=s0 and acP=acP and acQ=acQ and acR=acR and Z=ac'])
       apply blast
      by (simp add: choices_ex merge_guard_eval merge_ades_obs[simplified])
    done
qed

end
