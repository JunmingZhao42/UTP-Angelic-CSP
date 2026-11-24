section \<open>AD Parallel with a Lifted State Merge\<close>

theory utp_ades_parallel_lift
  imports utp_ades_parallel_laws
begin

text \<open>Lifting a state merge to AD, the AD parallel operator, and its
  correspondence with designs.\<close>

subsection \<open>Lifting a State Merge\<close>

subsubsection \<open>Construction\<close>

text \<open>The AD merge lifts the design merge of @{term j} through choice sets.\<close>

(* merge_ades j = H3m (H1m (ABm (ac'_lift_merge (merge_des_raw j)))) *)
definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "merge_ades j \<equiv> H3m (H1m (ABm (ac'_lift_merge (merge_des_raw j))))"

lemma merge_ades_completion [simp]: "merge_ades j ;; II\<^sub>D = merge_ades j"
  by (simp add: merge_ades_def H3m_def seqr_assoc)

subsubsection \<open>Evaluation\<close>

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
  "merge_ades j = (\<lambda>(m,out).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        acL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        acR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        ac' = achoices.ac\<^sub>v (des_vars.more out)
    in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
       (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)
          \<longrightarrow> (des_vars.ok\<^sub>v out \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
  by (rule ades_merge_ext; simp add: merge_ades_obs[simplified] Let_def)

subsubsection \<open>Healthiness, Symmetry and Associativity\<close>

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
  obtain f where f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
    using mergeable_Functional_fun[OF tot det] by blast
  have fcyc: "f s (f s a b) c = f s (f s b c) a" for s a b c
    using assoc[unfolded AssocMerge_iff, rule_format, of s a b c "f s (f s a b) c"]
    by (simp add: f)
  (* one cyclic step; three steps return to the start *)
  have rot: "\<forall>a\<in>XQ. \<forall>b\<in>XR. \<forall>c\<in>XP. f s (f s a b) c \<in> Z"
    if h: "\<forall>a\<in>XP. \<forall>b\<in>XQ. \<forall>c\<in>XR. f s (f s a b) c \<in> Z" for s XP XQ XR Z
  proof (intro ballI)
    fix a b c assume "a \<in> XQ" "b \<in> XR" "c \<in> XP"
    then have "f s (f s c a) b \<in> Z" using h by blast
    then show "f s (f s a b) c \<in> Z" by (metis fcyc)
  qed
  have rotate: "(\<forall>a\<in>XP. \<forall>b\<in>XQ. \<forall>c\<in>XR. f s (f s a b) c \<in> Z) \<longleftrightarrow>
      (\<forall>a\<in>XQ. \<forall>b\<in>XR. \<forall>c\<in>XP. f s (f s a b) c \<in> Z)" for s XP XQ XR Z
    using rot[of XP XQ XR s Z] rot[of XQ XR XP s Z] rot[of XR XP XQ s Z] by blast
  have started:
    "merge_eval (merge_ades j) \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
        (ades_output okL acL) (ades_output okR acR) (ades_output ok' ac') \<longleftrightarrow>
     acL \<noteq> {} \<and> acR \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>a\<in>acL. \<forall>b\<in>acR. f s0 a b \<in> ac'))"
    for s0 okL acL okR acR ok' ac'
    by (simp add: merge_ades_obs[simplified] f)
  (* the smallest middle set is the image of the first merge *)
  have middle:
    "(\<exists>okU U. (XP \<noteq> {} \<and> XQ \<noteq> {} \<and> (okP \<and> okQ \<longrightarrow> okU \<and> (\<forall>a\<in>XP. \<forall>b\<in>XQ. g a b \<in> U))) \<and>
        (U \<noteq> {} \<and> XR \<noteq> {} \<and> (okU \<and> okR \<longrightarrow> ok' \<and> (\<forall>a\<in>U. \<forall>b\<in>XR. g a b \<in> Z)))) \<longleftrightarrow>
     XP \<noteq> {} \<and> XQ \<noteq> {} \<and> XR \<noteq> {} \<and>
     (okP \<and> okQ \<and> okR \<longrightarrow> ok' \<and> (\<forall>a\<in>XP. \<forall>b\<in>XQ. \<forall>c\<in>XR. g (g a b) c \<in> Z))"
    (is "?L \<longleftrightarrow> ?R")
    for g :: "'s \<Rightarrow> 's \<Rightarrow> 's" and XP XQ XR Z :: "'s set" and okP okQ okR ok' :: bool
  proof
    assume ?L
    then show ?R by blast
  next
    assume r: ?R
    let ?U = "{g a b | a b. a \<in> XP \<and> b \<in> XQ}"
    have ne: "?U \<noteq> {}" using r by fastforce
    show ?L
      by (rule exI[where x="okP \<and> okQ"], rule exI[where x="?U"]) (use r ne in blast)
  qed
  show ?thesis
    unfolding AssocMerge_iff
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okP XP okQ XQ okR XR ok' ac'
      apply (cases ok0)
       apply (simp only: choices_ex started middle rotate[of XP XQ XR s0 ac'])
       apply blast
      by (simp add: choices_ex merge_ades_obs[simplified])
    done
qed

text \<open>We want associativity for nondivergent operands even when j is partial, so we
  guard the merge to nondivergent branches, as for designs. Then a deterministic j is
  enough: both merge orders need the merge of a, b and then c to exist and lie in ac'.\<close>

lemma merge_ades_guard_AssocMerge:
  fixes j :: "'s merge"
  assumes det: "Functional j" and assoc: "AssocMerge j"
  shows "AssocMerge (merge_guard (\<lambda>x z. des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z) (merge_ades j))"
proof -
  have uniq: "u = v" if "merge_eval j s a b u" "merge_eval j s a b v" for s a b u v
    using det[unfolded Functional_merge_eval] that by blast
  have Tcyc: "(\<exists>u. merge_eval j s a b u \<and> merge_eval j s u c z) \<longleftrightarrow>
      (\<exists>u. merge_eval j s b c u \<and> merge_eval j s u a z)" for s a b c z
    by (rule assoc[unfolded AssocMerge_iff, rule_format])
  (* one cyclic step; three steps return to the start *)
  have rot: "\<forall>a\<in>XQ. \<forall>b\<in>XR. \<forall>c\<in>XP. \<exists>z\<in>Z. \<exists>u. merge_eval j s a b u \<and> merge_eval j s u c z"
    if h: "\<forall>a\<in>XP. \<forall>b\<in>XQ. \<forall>c\<in>XR. \<exists>z\<in>Z. \<exists>u. merge_eval j s a b u \<and> merge_eval j s u c z"
    for s XP XQ XR Z
  proof (intro ballI)
    fix a b c assume "a \<in> XQ" "b \<in> XR" "c \<in> XP"
    then have "\<exists>z\<in>Z. \<exists>u. merge_eval j s c a u \<and> merge_eval j s u b z" using h by blast
    then show "\<exists>z\<in>Z. \<exists>u. merge_eval j s a b u \<and> merge_eval j s u c z"
      using Tcyc[of s c a b] by blast
  qed
  have rotate:
    "(\<forall>a\<in>XP. \<forall>b\<in>XQ. \<forall>c\<in>XR. \<exists>z\<in>Z. \<exists>u. merge_eval j s a b u \<and> merge_eval j s u c z) \<longleftrightarrow>
     (\<forall>a\<in>XQ. \<forall>b\<in>XR. \<forall>c\<in>XP. \<exists>z\<in>Z. \<exists>u. merge_eval j s a b u \<and> merge_eval j s u c z)"
    for s XP XQ XR Z
    by (rule iffI) (erule rot, erule rot[THEN rot])
  have started:
    "merge_eval (merge_guard (\<lambda>x z. des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z) (merge_ades j))
        \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
        (ades_output okL acL) (ades_output okR acR) (ades_output ok' ac') \<longleftrightarrow>
     okL \<and> okR \<and> acL \<noteq> {} \<and> acR \<noteq> {} \<and> (\<forall>a\<in>acL. \<forall>b\<in>acR. \<exists>z. merge_eval j s0 a b z) \<and>
     ok' \<and> (\<forall>a\<in>acL. \<forall>b\<in>acR. \<exists>z\<in>ac'. merge_eval j s0 a b z)"
    for s0 okL acL okR acR ok' ac'
    by (auto simp: merge_guard_eval merge_ades_obs[simplified])
  (* the middle set holds every result of the first merge *)
  have middle:
    "(\<exists>okU U.
        (okP \<and> okQ \<and> XP \<noteq> {} \<and> XQ \<noteq> {} \<and> (\<forall>a\<in>XP. \<forall>b\<in>XQ. \<exists>z. merge_eval j s0 a b z) \<and>
         okU \<and> (\<forall>a\<in>XP. \<forall>b\<in>XQ. \<exists>z\<in>U. merge_eval j s0 a b z)) \<and>
        (okU \<and> okR \<and> U \<noteq> {} \<and> XR \<noteq> {} \<and> (\<forall>a\<in>U. \<forall>b\<in>XR. \<exists>z. merge_eval j s0 a b z) \<and>
         ok' \<and> (\<forall>a\<in>U. \<forall>b\<in>XR. \<exists>z\<in>Z. merge_eval j s0 a b z))) \<longleftrightarrow>
     okP \<and> okQ \<and> okR \<and> XP \<noteq> {} \<and> XQ \<noteq> {} \<and> XR \<noteq> {} \<and> ok' \<and>
     (\<forall>a\<in>XP. \<forall>b\<in>XQ. \<forall>c\<in>XR. \<exists>z\<in>Z. \<exists>u. merge_eval j s0 a b u \<and> merge_eval j s0 u c z)"
    (is "?L \<longleftrightarrow> ?R")
    for s0 XP XQ XR Z okP okQ okR ok'
  proof
    assume ?L
    then show ?R by blast
  next
    assume r: ?R
    let ?U = "{u. \<exists>a\<in>XP. \<exists>b\<in>XQ. merge_eval j s0 a b u}"
    have uz: "\<exists>z\<in>Z. merge_eval j s0 u c z" if "u \<in> ?U" "c \<in> XR" for u c
      using that r uniq by blast
    show ?L
      by (rule exI[where x=True], rule exI[where x="?U"]) (use r uz in blast)
  qed
  show ?thesis
    unfolding AssocMerge_iff
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okP XP okQ XQ okR XR ok' ac'
      apply (cases ok0)
       apply (simp only: choices_ex started middle
          rotate[where s=s0 and XP=XP and XQ=XQ and XR=XR and Z=ac'])
       apply blast
      by (simp add: choices_ex merge_guard_eval merge_ades_obs[simplified])
    done
qed

subsection \<open>AD Parallel\<close>

subsubsection \<open>Definition and Evaluation\<close>

definition ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^bsub>merge_ades j\<^esub> Q"

text \<open>H1 handles unstarted observations; A2 reduces nonempty branch sets to singleton witnesses.\<close>

lemma ades_par_obs_A2:
  fixes P Q :: "'s angelic_design"
  assumes "P is A2" "Q is A2" "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not>ok0 \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> (\<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
proof -
  have pick: "\<exists>x\<in>X. R (ades_obs True s0 okL {x})"
    if "R is A2" "X \<noteq> {}" "R (ades_obs True s0 okL X)" for R :: "'s angelic_design" and okL X
  proof -
    have "R (ades_obs True s0 okL Y) \<longleftrightarrow>
        R (ades_obs True s0 okL {}) \<or> (\<exists>y\<in>Y. R (ades_obs True s0 okL {y}))" for Y
      using A2_obs[of R True s0 okL Y] by (simp only: Healthy_if[OF that(1)])
    then show ?thesis
      using that(2,3) by blast
  qed
  show ?thesis
    apply (cases ok0; simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified]
        assms(3,4)[unfolded H1_healthy_obs_iff])
    apply (rule iffI)
    subgoal using pick[OF assms(1)] pick[OF assms(2)] by metis
    subgoal by (fastforce intro: exI[where x="{_}"])
    done
qed

lemma ades_par_obs:
  fixes P Q :: "'s angelic_design"
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not> ok0 \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> (\<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: A_healthy_components_iff)
  show ?thesis
    by (rule ades_par_obs_A2[OF assms(3,4) operands_H1])
qed

lemma ades_par_normalise_A:
  assumes "P is A2" "Q is A2" "P is H1" "Q is H1"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q"
  by (rule ades_obs_ext;
      simp add: ades_par_obs_A2[OF assms]
        ades_par_obs_A2[OF A_preserves_A2[OF assms(1)] A_preserves_A2[OF assms(2)] A_is_H1[folded Healthy_def'] A_is_H1[folded Healthy_def']]
        A_obs_A2[OF assms(1)] A_obs_A2[OF assms(2)] ex_bool_eq; blast)

lemma ades_par_eval:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR.
      P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      (\<not>ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (okL \<and> okR \<longrightarrow> (ok' \<and>
          (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s'))))))"
  by (simp add: ades_par_def
      par_by_merge_eval choices_ex merge_ades_obs[simplified])

subsubsection \<open>Healthiness Closure\<close>

lemma ades_par_A0_closure [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0"
  unfolding ades_par_def
  by (rule A0_par_by_merge[OF merge_ades_is_A0m])

lemma ades_par_A1_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A1"
  unfolding ades_par_def
  by (rule A1_par_by_merge[OF assms merge_ades_is_A1m])

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_def
  by (rule A_par_by_merge[OF assms merge_ades_is_ADm])

lemma ades_par_A2_closure [closure]:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  unfolding ades_par_def
  by (rule A2_par_by_merge[OF assms merge_ades_is_A2m])

lemma ades_par_A3_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  unfolding ades_par_def
  by (rule A3_par_by_merge[OF assms merge_ades_is_H1m merge_ades_is_H3m])

subsubsection \<open>Correspondence with Designs\<close>

text \<open>For A- and A2-healthy operands, ac2p and d2ac preserve parallel by the
  lift of an HDm- and H3m-healthy design merge.\<close>

lemma ades_par_d2ac_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = d2ac ((ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q))"
  unfolding ades_par_def merge_ades_design_lift
  by (rule ades_par_by_merge_d2ac_ac2p[OF assms merge_des_is_HDm merge_des_is_H3m refl])

lemma ades_par_d2ac:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(d2ac P) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac Q) = d2ac (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)"
  by (simp only: ades_par_d2ac_ac2p[OF d2ac_is_A d2ac_is_A d2ac_is_A2 d2ac_is_A2]
      ac2p_d2ac[OF assms(1), simplified comp_apply]
      ac2p_d2ac[OF assms(2), simplified comp_apply])

lemma ades_par_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q)"
  unfolding ades_par_def
  by (rule ades_par_by_merge_ac2p[OF assms merge_des_is_HDm merge_des_is_H3m merge_ades_design_lift])

lemma ades_par_ac2p_d2ac:
  assumes "D is \<^bold>H" "E is \<^bold>H"
  shows "D \<parallel>\<^sub>D\<^bsub>j\<^esub> E = ac2p ((d2ac D) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac E))"
  by (simp only: ades_par_d2ac[OF assms]
      ac2p_d2ac[OF des_par_H_closure[OF H_implies_H1[OF assms(1)] H_implies_H1[OF assms(2)]], simplified comp_apply])

subsubsection \<open>Canonicity\<close>

(* P \<parallel>\<^sub>A\<^sub>D[j] Q \<sqsubseteq> P \<parallel>[H3m (H1m M)] Q *)
theorem ades_par_canonical:
  assumes "M is ABm" "singleton_refines (merge_des j) M"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>H3m (H1m M)\<^esub> Q"
proof -
  have "ABm (ac'_lift_merge (merge_des j)) \<sqsubseteq> M"
    by (rule choice_lift_least[OF assms])
  then have "H1m (ABm (ac'_lift_merge (merge_des j))) \<sqsubseteq> H1m M"
    by (rule H1m_Monotonic[unfolded Monotonic_refine, rule_format])
  then have "H3m (H1m (ABm (ac'_lift_merge (merge_des j)))) \<sqsubseteq> H3m (H1m M)"
    by (rule H3m_Monotonic[unfolded Monotonic_refine, rule_format])
  then show ?thesis
    unfolding ades_par_def merge_ades_design_lift by (rule par_by_merge_mono_merge)
qed

subsubsection \<open>Choice\<close>

text \<open>The choice laws for any AD merge apply to the lifted merge. The angelic law can be
  strict, since the left side may resolve the shared operand's demonic choice twice.\<close>

(* P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R) *)
lemma ades_par_demonic_distl:
  "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<sqinter>\<^sub>A\<^sub>D R) = (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<sqinter>\<^sub>A\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (simp only: ades_par_def ades_par_by_merge_demonic_distl)

(* (P \<sqinter> Q) \<parallel> R = (P \<parallel> R) \<sqinter> (Q \<parallel> R) *)
lemma ades_par_demonic_distr:
  "(P \<sqinter>\<^sub>A\<^sub>D Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqinter>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (simp only: ades_par_def ades_par_by_merge_demonic_distr)

(* (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R) *)
lemma ades_par_angelic_subdistl:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<squnion>\<^sub>A\<^sub>D R)"
  by (simp only: ades_par_def ades_par_by_merge_angelic_subdistl)

(* (P \<parallel> R) \<squnion> (Q \<parallel> R) \<sqsubseteq> (P \<squnion> Q) \<parallel> R *)
lemma ades_par_angelic_subdistr:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqsubseteq> (P \<squnion>\<^sub>A\<^sub>D Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R"
  by (simp only: ades_par_def ades_par_by_merge_angelic_subdistr)

text \<open>The angelic laws are equalities when the shared operand Q has no demonic choice,
  so its offered sets are closed under intersection, and no operand diverges:
  (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q.\<close>

(* (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q *)
lemma ades_par_angelic_distr:
  fixes P P' Q :: "'s angelic_design"
  assumes a: "P is A" "P' is A"
    and nd: "P is NDAD" "P' is NDAD" "Q is NDAD"
    and q: "\<And>s0 Y Y'. Q (ades_obs True s0 True Y) \<Longrightarrow> Q (ades_obs True s0 True Y') \<Longrightarrow>
      Q (ades_obs True s0 True (Y \<inter> Y'))"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  have un: "S (ades_obs False s0 c X)" if "S is A" for S :: "'s angelic_design" and c X
    using that by (simp add: A_healthy_components_iff H1_healthy_obs_iff)
  have up: "S (ades_obs True s0 True X')"
    if "S is A" "S (ades_obs True s0 True X)" "X \<subseteq> X'" for S :: "'s angelic_design" and X X'
  proof -
    have pb: "S is PBMH_ades" using that(1) by (simp add: A_healthy_components_iff)
    show ?thesis by (rule PBMH_ades_upward[OF pb that(2)]; simp add: that(3))
  qed
  have ndt: "c \<and> X \<noteq> {}" if "S is NDAD" "S (ades_obs True s0 c X)" for S :: "'s angelic_design" and c X
    using NDAD_obs[of S True s0 c X] that by (simp add: Healthy_if[OF that(1)])
  show "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac') = ((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: ades_par_eval inf_fun_def inf_bool_def un[OF a(1)] un[OF a(2)])
  next
    case True
    show ?thesis
    proof
      assume "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac')"
      then obtain okL X okR Y okL' X' okR' Y' where
        px: "P (ades_obs True s0 okL X)" and qy: "Q (ades_obs True s0 okR Y)"
        and f: "\<forall>a\<in>X. \<forall>b\<in>Y. \<exists>s'. merge_eval j s0 a b s'"
        and h: "okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>a\<in>X. \<forall>b\<in>Y. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        and px': "P' (ades_obs True s0 okL' X')" and qy': "Q (ades_obs True s0 okR' Y')"
        and f': "\<forall>a\<in>X'. \<forall>b\<in>Y'. \<exists>s'. merge_eval j s0 a b s'"
        and h': "okL' \<and> okR' \<longrightarrow> ok' \<and> (\<forall>a\<in>X'. \<forall>b\<in>Y'. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        using True by (simp only: ades_par_eval inf_fun_def inf_bool_def simp_thms) blast
      note ok = ndt[OF nd(1) px] ndt[OF nd(3) qy] ndt[OF nd(2) px'] ndt[OF nd(3) qy']
      have T: "P (ades_obs True s0 True X)" "P' (ades_obs True s0 True X')"
          "Q (ades_obs True s0 True Y)" "Q (ades_obs True s0 True Y')"
        using px px' qy qy' ok by simp_all
      have qi: "Q (ades_obs True s0 True (Y \<inter> Y'))" by (rule q[OF T(3,4)])
      have "((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def
        by (rule exI[where x=True], rule exI[where x="X \<union> X'"],
            rule exI[where x=True], rule exI[where x="Y \<inter> Y'"])
           (use up[OF a(1) T(1) Un_upper1] up[OF a(2) T(2) Un_upper2] ndt[OF nd(3) qi]
             ndt[OF nd(1) T(1)] qi ok f f' h h' in blast)
      then show "((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
        using True by simp
    next
      assume "((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
      then show "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def by blast
    qed
  qed
qed

(* (Q \<parallel> P) \<squnion> (Q \<parallel> P') = Q \<parallel> (P \<squnion> P') *)
lemma ades_par_angelic_distl:
  fixes P P' Q :: "'s angelic_design"
  assumes a: "P is A" "P' is A"
    and nd: "P is NDAD" "P' is NDAD" "Q is NDAD"
    and q: "\<And>s0 Y Y'. Q (ades_obs True s0 True Y) \<Longrightarrow> Q (ades_obs True s0 True Y') \<Longrightarrow>
      Q (ades_obs True s0 True (Y \<inter> Y'))"
  shows "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P') = Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  have un: "S (ades_obs False s0 c X)" if "S is A" for S :: "'s angelic_design" and c X
    using that by (simp add: A_healthy_components_iff H1_healthy_obs_iff)
  have up: "S (ades_obs True s0 True X')"
    if "S is A" "S (ades_obs True s0 True X)" "X \<subseteq> X'" for S :: "'s angelic_design" and X X'
  proof -
    have pb: "S is PBMH_ades" using that(1) by (simp add: A_healthy_components_iff)
    show ?thesis by (rule PBMH_ades_upward[OF pb that(2)]; simp add: that(3))
  qed
  have ndt: "c \<and> X \<noteq> {}" if "S is NDAD" "S (ades_obs True s0 c X)" for S :: "'s angelic_design" and c X
    using NDAD_obs[of S True s0 c X] that by (simp add: Healthy_if[OF that(1)])
  show "((Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac') = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: ades_par_eval inf_fun_def inf_bool_def un[OF a(1)] un[OF a(2)])
  next
    case True
    show ?thesis
    proof
      assume "((Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac')"
      then obtain okR Y okL X okR' Y' okL' X' where
        qy: "Q (ades_obs True s0 okR Y)" and px: "P (ades_obs True s0 okL X)"
        and f: "\<forall>a\<in>Y. \<forall>b\<in>X. \<exists>s'. merge_eval j s0 a b s'"
        and h: "okR \<and> okL \<longrightarrow> ok' \<and> (\<forall>a\<in>Y. \<forall>b\<in>X. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        and qy': "Q (ades_obs True s0 okR' Y')" and px': "P' (ades_obs True s0 okL' X')"
        and f': "\<forall>a\<in>Y'. \<forall>b\<in>X'. \<exists>s'. merge_eval j s0 a b s'"
        and h': "okR' \<and> okL' \<longrightarrow> ok' \<and> (\<forall>a\<in>Y'. \<forall>b\<in>X'. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        using True by (simp only: ades_par_eval inf_fun_def inf_bool_def simp_thms) blast
      note ok = ndt[OF nd(1) px] ndt[OF nd(3) qy] ndt[OF nd(2) px'] ndt[OF nd(3) qy']
      have T: "P (ades_obs True s0 True X)" "P' (ades_obs True s0 True X')"
          "Q (ades_obs True s0 True Y)" "Q (ades_obs True s0 True Y')"
        using px px' qy qy' ok by simp_all
      have qi: "Q (ades_obs True s0 True (Y \<inter> Y'))" by (rule q[OF T(3,4)])
      have "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs True s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def
        by (rule exI[where x=True], rule exI[where x="Y \<inter> Y'"],
            rule exI[where x=True], rule exI[where x="X \<union> X'"])
           (use up[OF a(1) T(1) Un_upper1] up[OF a(2) T(2) Un_upper2] ndt[OF nd(3) qi]
             ndt[OF nd(1) T(1)] qi ok f f' h h' in blast)
      then show "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
        using True by simp
    next
      assume "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
      then show "((Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def by blast
    qed
  qed
qed

subsubsection \<open>Monotonicity\<close>

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1) \<sqsubseteq> (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_def
  using assms by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)

subsubsection \<open>Zero Laws\<close>

text \<open>A nonterminating branch observation releases the output guarantee.
  Chaos in both branches therefore yields Chaos whenever the state merge has
  some merged state at every initial state.\<close>

lemma ades_par_chaos:
  assumes "\<And>s0. \<exists>sL sR s'. merge_eval j s0 sL sR s'"
  shows "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true :: 's angelic_design) = true"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' X
  obtain sL sR s' where witness: "merge_eval j s0 sL sR s'"
    using assms by blast
  have started: "\<exists>okL acL okR acR. acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow>
        (ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>X. merge_eval j s0 sL sR s')))"
    by (rule exI[of _ False], rule exI[of _ "{sL}"], rule exI[of _ False],
        rule exI[of _ "{sR}"]) (use witness in blast)
  show "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true :: 's angelic_design) (ades_obs ok0 s0 ok' X) =
    (true :: 's angelic_design) (ades_obs ok0 s0 ok' X)"
    using started
    by (simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified] true_pred_def)
qed

lemma ades_par_miracle:
  assumes "P is H1"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>A\<^sub>D"
        "\<^bold>\<top>\<^sub>A\<^sub>D \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>D"
proof -
  have miracle: "(A false :: 's angelic_design) = \<top>\<^sub>D"
    by (rule ades_obs_ext; simp add: A_obs top_d_not_ok; pred_simp)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>A\<^sub>D"
       "\<^bold>\<top>\<^sub>A\<^sub>D \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>D"
    unfolding miracle ades_par_def
    by (rule par_by_merge_miracle[OF assms merge_ades_is_H1m])+
qed

subsubsection \<open>Commutativity\<close>

lemma ades_par_comm:
  assumes "j is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P)"
  unfolding ades_par_def
  by (rule par_by_merge_comm[OF merge_ades_SymMerge[OF assms]])

subsubsection \<open>Associativity\<close>

text \<open>Associativity of the design images transfers to the lifted merge.\<close>

lemma ades_lift_par_assoc_transfer:
  fixes M :: "'s des_merge"
  assumes ops: "P is A" "Q is A" "R is A" "P is A2" "Q is A2" "R is A2"
    and merge: "M is HDm" "M is H3m"
    and ordinary: "(ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) \<parallel>\<^bsub>M\<^esub> ac2p R = ac2p P \<parallel>\<^bsub>M\<^esub> (ac2p Q \<parallel>\<^bsub>M\<^esub> ac2p R)"
  shows "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R =
    P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> (Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R)"
proof -
  have pq: "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) is A" "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) is A2"
    and qr: "(Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R) is A" "(Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R) is A2"
    by (simp_all only: ades_par_by_merge_d2ac_ac2p[OF ops(1,2,4,5) merge refl]
        ades_par_by_merge_d2ac_ac2p[OF ops(2,3,5,6) merge refl] d2ac_is_A d2ac_is_A2)
  show ?thesis
    by (simp only: ades_par_by_merge_d2ac_ac2p[OF pq(1) ops(3) pq(2) ops(6) merge refl]
        ades_par_by_merge_d2ac_ac2p[OF ops(1) qr(1) ops(4) qr(2) merge refl]
        ades_par_by_merge_ac2p[OF ops(1,2,4,5) merge refl] ades_par_by_merge_ac2p[OF ops(2,3,5,6) merge refl]
        ordinary)
qed

lemma A_ac2p_NDD:
  assumes "P is A" "P is NDAD"
  shows "ac2p P is NDD"
proof -
  have "ac2p (A P) is NDD"
    using assms(2) unfolding NDD_healthy_iff preD_true_iff NDAD_healthy_obs_iff
    by (auto simp: ac2p_def A_PBMH_ades A_obs StateII_def)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)])
qed

text \<open>For H1 and A2 operands, AD parallel by @{term j} first normalises the
  operands with @{const A}.\<close>

lemma A_preserves_NDAD:
  assumes "P is A2" "P is NDAD"
  shows "A P is NDAD"
  using assms(2) unfolding NDAD_healthy_obs_iff
  by (simp add: A_obs_A2[OF assms(1)]; blast)

lemma ades_par_normalise_A3:
  assumes ops: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R"
    "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
proof -
  have pq: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A" "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2" "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
    and qr: "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A2" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is H1"
    using ades_par_A_closure[OF h1(1,2)] ades_par_A2_closure[OF ops(1,2)]
      ades_par_A_closure[OF h1(2,3)] ades_par_A2_closure[OF ops(2,3)]
    by (simp_all add: A_healthy_components_iff)
  show "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R"
    apply (subst ades_par_normalise_A[OF pq(2) ops(3) pq(3) h1(3)])
    apply (subst Healthy_if[OF pq(1)])
    by (subst ades_par_normalise_A[OF ops(1,2) h1(1,2)], rule refl)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
    apply (subst ades_par_normalise_A[OF ops(1) qr(2) h1(1) qr(3)])
    apply (subst Healthy_if[OF qr(1)])
    by (subst ades_par_normalise_A[OF ops(2,3) h1(2,3)], rule refl)
qed

lemma ades_par_assoc:
  fixes j :: "'s merge"
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and merge: "j is SymMerge" "AssocMerge j" "mergeable j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have a: "A S is A" for S :: "'s angelic_design"
    by (simp add: Healthy_def' A_idem)
  show ?thesis
    unfolding ades_par_normalise_A3[OF operands h1]
    unfolding ades_par_def merge_ades_design_lift
    by (rule ades_lift_par_assoc_transfer[OF a a a A_preserves_A2[OF operands(1)]
          A_preserves_A2[OF operands(2)] A_preserves_A2[OF operands(3)]
          merge_des_is_HDm merge_des_is_H3m des_par_assoc[OF merge]])
qed

lemma ades_par_assoc_nd:
  fixes j :: "'s merge"
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and nondiv: "P is NDAD" "Q is NDAD" "R is NDAD"
      and merge: "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have a: "A S is A" for S :: "'s angelic_design"
    by (simp add: Healthy_def' A_idem)
  show ?thesis
    unfolding ades_par_normalise_A3[OF operands h1]
    unfolding ades_par_def merge_ades_design_lift
    by (rule ades_lift_par_assoc_transfer[OF a a a A_preserves_A2[OF operands(1)]
          A_preserves_A2[OF operands(2)] A_preserves_A2[OF operands(3)]
          merge_des_is_HDm merge_des_is_H3m
          des_par_assoc_nd[OF
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(1) nondiv(1)]]
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(2) nondiv(2)]]
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(3) nondiv(3)]] merge]])
qed

text \<open>For a deterministic (Functional) merge we get associativity for all operands,
  without A2 or nondivergence: (P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R).
  As in D, it follows from associativity of the lifted merge.\<close>

theorem ades_par_assoc_det:
  fixes j :: "'s merge" and P Q R :: "'s angelic_design"
  assumes det: "Functional j" and tot: "mergeable j"
    and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  unfolding ades_par_def
  by (rule par_by_merge_assoc[OF merge_ades_SymMerge[OF sym] merge_ades_AssocMerge[OF det tot assoc]])

text \<open>For nondivergent operands a deterministic merge need not be total:
  (P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R). With divergence, a partial merge breaks this.\<close>

theorem ades_par_assoc_det_nd:
  fixes j :: "'s merge" and P Q R :: "'s angelic_design"
  assumes nondiv: "P is NDAD" "Q is NDAD" "R is NDAD"
    and det: "Functional j" and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  unfolding ades_par_def
proof (rule par_by_merge_assoc_guard[OF SymMerge_merge_guard[OF merge_ades_SymMerge[OF sym]]
      merge_ades_guard_AssocMerge[OF det assoc]])
  (* nondivergent operands never pass from a started prior to ok' = False *)
  have nd_ok: "\<And>x z. S (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z"
    if "S is NDAD" for S :: "'s angelic_design"
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    by (metis (full_types) NDAD_obs Healthy_if[OF that] des_vars.select_convs(1))
  show "\<lbrakk> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v p; des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v q;
      merge_eval (merge_ades j) x p q z \<rbrakk> \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z" for x p q z
    by (auto simp: merge_ades_unfold Let_def)
  show "P (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z"
    "Q (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z"
    "R (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z" for x z
    using nd_ok[OF nondiv(1)] nd_ok[OF nondiv(2)] nd_ok[OF nondiv(3)] by blast+
qed

subsubsection \<open>Example: Skip Merge\<close>

text \<open>With two terminating branch observations, the skip state merge requires
  s in ac'. A nonterminating branch permits every output set, including empty.\<close>

lemma ades_par_skip_eval:
  assumes operands: "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not>ok0 \<or> (\<exists>okL acL okR acR.
      acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      P (ades_obs True s0 okL acL) \<and> Q (ades_obs True s0 okR acR) \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> s0 \<in> ac'))))"
  using operands[unfolded H1_healthy_obs_iff]
  by (cases ok0; simp add: ades_par_def
      par_by_merge_eval choices_ex merge_ades_obs[simplified] skip_merge_eval; blast)

lemma ades_par_skip_comm:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> P)"
  by (rule ades_par_comm; simp add: Healthy_def skip_merge_swap)

lemma ades_par_skip_assoc:
  assumes "P is A2" "Q is A2" "R is A2" "P is H1" "Q is H1" "R is H1"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R) =
  (P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R))"
proof (rule ades_par_assoc[OF assms])
  show "skip\<^sub>m is SymMerge"
    by (simp add: Healthy_def skip_merge_swap)
  show "AssocMerge skip\<^sub>m"
    by (simp add: AssocMerge_def skip\<^sub>m_def; pred_auto)
qed (simp add: skip_merge_eval)

end
