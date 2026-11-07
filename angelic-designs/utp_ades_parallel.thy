section \<open>Angelic Parallel and Ordinary Designs\<close>

theory utp_ades_parallel
  imports utp_ades_designs
begin

text \<open>AD merge healthiness, state-merge lifting, and parallel composition laws.\<close>

subsection \<open>Merge Observations\<close>

type_synonym 's ades_mrg =
  "('s astate des_vars_ext, 's achoices des_vars_ext, 's achoices des_vars_ext) mrg"

type_synonym 's ades_merge_rel = "('s ades_mrg, 's achoices des_vars_ext) urel"

abbreviation ades_merge_obs where
  "ades_merge_obs M ok0 s0 okL acL okR acR ok' ac' \<equiv>
    (\<lambda>(prior,out). merge_eval M prior (ades_output okL acL) (ades_output okR acR) out)
      (ades_obs ok0 s0 ok' ac')"

lemma ades_merge_ext:
  fixes M N :: "'s ades_merge_rel"
  assumes "\<And>ok0 s0 okL acL okR acR ok' ac'. ades_merge_obs M ok0 s0 okL acL okR acR ok' ac' = ades_merge_obs N ok0 s0 okL acL okR acR ok' ac'"
  shows "M = N"
  using assms by pred_auto

lemma ades_par_by_merge_obs:
  "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR. P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      ades_merge_obs M ok0 s0 okL acL okR acR ok' ac')"
  by (simp add: par_by_merge_eval choices_ex)

subsection \<open>Merge Healthiness\<close>

text \<open>The condition Xm gives X closure under parallel by merge. H1m, H2m, H3m
  and HDM come from the design theory. A closure uses A0m and A1m;
  A3 closure follows from H1m and H3m.\<close>

subsubsection \<open>A0m and A1m\<close>

(* A0m M (m, (ok', ac')) = M (m, (ok', ac')) \<and>
     (ok \<and> ok' \<and> ac' = {} \<longrightarrow> M (m, (False, {}))) *)
definition A0m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A0m M \<equiv> (\<lambda>(m,out).
     M (m,out) \<and>
     (des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<and> des_vars.ok\<^sub>v out \<and> achoices.ac\<^sub>v (des_vars.more out) = {}
       \<longrightarrow> M (m, ades_output False {})))"

(* A1m M (m, (ok', ac')) = \<not> ok \<or> (\<exists>Y \<subseteq> ac'. M (m, (False, Y))) \<or>
     (ok' \<and> (\<exists>Y \<subseteq> ac'. M (m, (True, Y)))) *)
definition A1m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A1m M \<equiv> (\<lambda>(m,out).
     let ac' = achoices.ac\<^sub>v (des_vars.more out)
     in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
        (\<exists>Y\<subseteq>ac'. M (m, ades_output False Y)) \<or>
        (des_vars.ok\<^sub>v out \<and> (\<exists>Y\<subseteq>ac'. M (m, ades_output True Y))))"

lemma A0m_Idempotent [closure]: "Idempotent A0m"
  unfolding Idempotent_def
  by (intro allI, rule ades_merge_ext) (auto simp: A0m_def)

lemma A1m_Idempotent [closure]: "Idempotent A1m"
  unfolding Idempotent_def
  by (intro allI, rule ades_merge_ext) (auto simp: A1m_def Let_def; blast)

lemma A0m_Monotonic [closure]: "Monotonic A0m"
  by (rule MonotonicI) (auto simp: pred_refine_iff A0m_def)

lemma A1m_Monotonic [closure]: "Monotonic A1m"
  by (rule MonotonicI) (auto simp: pred_refine_iff A1m_def Let_def)

subsubsection \<open>A2m\<close>

(* A2m M (m, (ok', ac')) =
     if both branch sets are singletons then M (m, (ok', {})) \<or> (\<exists>w \<in> ac'. M (m, (ok', {w})))
     else M (m, (ok', ac')) \<and> every singleton branch pair accepts {} or some {w} \<subseteq> ac'. *)
definition A2m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "A2m M \<equiv> (\<lambda>(m,out).
  let acL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
      acR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
      ok' = des_vars.ok\<^sub>v out;
      ac' = achoices.ac\<^sub>v (des_vars.more out)
  in if (\<exists>x. acL = {x}) \<and> (\<exists>y. acR = {y})
     then M (m, ades_output ok' {}) \<or> (\<exists>w\<in>ac'. M (m, ades_output ok' {w}))
     else M (m,out) \<and>
       (\<forall>x y. (acL = {} \<or> x \<in> acL) \<and> (acR = {} \<or> y \<in> acR) \<longrightarrow>
         (let m' = m\<lparr>mrg_left\<^sub>v := ades_output (des_vars.ok\<^sub>v (mrg_left\<^sub>v m)) {x},
                     mrg_right\<^sub>v := ades_output (des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) {y}\<rparr>
          in M (m', ades_output ok' {}) \<or> (\<exists>w\<in>ac'. M (m', ades_output ok' {w})))))"

lemma A2m_obs:
  "ades_merge_obs (A2m M) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
    ((\<exists>p. acL = {p}) \<and> (\<exists>q. acR = {q}) \<or> ades_merge_obs M ok0 s0 okL acL okR acR ok' ac') \<and>
    (\<forall>x y. (acL = {} \<or> x \<in> acL) \<and> (acR = {} \<or> y \<in> acR) \<longrightarrow>
       ades_merge_obs M ok0 s0 okL {x} okR {y} ok' {} \<or>
       (\<exists>w\<in>ac'. ades_merge_obs M ok0 s0 okL {x} okR {y} ok' {w}))"
  by (simp add: A2m_def Let_def; auto)

lemma A2m_Idempotent [closure]: "Idempotent A2m"
  unfolding Idempotent_def
  by (intro allI, rule ades_merge_ext) (auto simp: A2m_obs[simplified])

lemma A2m_Monotonic [closure]: "Monotonic A2m"
  by (rule MonotonicI)
     (auto simp: pred_refine_iff A2m_def Let_def split: if_splits; meson)

subsubsection \<open>Commutation\<close>

lemma H1m_AD_commute:
  "H1m (A0m M) = A0m (H1m M)"
  "H1m (A1m M) = A1m (H1m M)"
  by (rule ades_merge_ext; simp add: A0m_def A1m_def Let_def; pred_simp; blast)+

lemma H1m_A2m_commute:
  "H1m (A2m M) = A2m (H1m M)"
  by (rule ades_merge_ext; rename_tac ok0 s0 okL acL okR acR ok' ac'; case_tac ok0;
      simp add: A2m_obs[simplified] H1m_def; pred_simp;
      simp add: A2m_obs[simplified])

lemma H2m_ades_obs:
  "ades_merge_obs (H2m M) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
   ades_merge_obs M ok0 s0 okL acL okR acR ok' ac' \<or>
   (ok' \<and> ades_merge_obs M ok0 s0 okL acL okR acR False ac')"
  by (cases ok'; simp add: H2m_def seq_def choices_ex J_def; pred_simp; simp add: ex_bool_eq)

lemma H3m_ades_obs:
  "ades_merge_obs (H3m M) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
   ades_merge_obs M ok0 s0 okL acL okR acR ok' ac' \<or>
   (\<exists>Y. ades_merge_obs M ok0 s0 okL acL okR acR False Y)"
  by (cases ok'; simp add: H3m_def seq_def choices_ex skip_d_def rdesign_def design_def; pred_simp; auto simp: ex_bool_eq)

lemma H2m_A0m_commute:
  "H2m (A0m M) = A0m (H2m M)"
  by (rule ades_merge_ext; auto simp: H2m_ades_obs[simplified] A0m_def)

lemma H2m_A1m_commute:
  "H2m (A1m M) = A1m (H2m M)"
  by (rule ades_merge_ext; auto simp: H2m_ades_obs[simplified] A1m_def Let_def)

lemma H3m_A0m_commute:
  "H3m (A0m M) = A0m (H3m M)"
  by (rule ades_merge_ext; auto simp: H3m_ades_obs[simplified] A0m_def)

lemma H3m_A1m_commute:
  "H3m (A1m M) = A1m (H3m M)"
  by (rule ades_merge_ext; auto simp: H3m_ades_obs[simplified] A1m_def Let_def; blast)

lemma HDM_angelic_commute:
  "HDM (A0m M) = A0m (HDM M)"
  "HDM (A1m M) = A1m (HDM M)"
  by (simp add: HDM_def H1m_AD_commute H2m_A0m_commute H2m_A1m_commute)+

subsection \<open>Generic AD Parallel Laws\<close>

subsubsection \<open>Healthiness Closure\<close>

text \<open>The design rules @{thm [source] H1_par_by_merge}, @{thm [source] H2_par_by_merge}
  and @{thm [source] H3_par_by_merge} apply to AD relations directly. The rules below
  cover A, A2 and A3.\<close>

lemma A0_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes "M is A0m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A0"
proof -
  obtain N where M: "M = A0m N"
    using assms by (metis Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        auto simp: A0_obs ades_par_by_merge_obs M A0m_def; blast)
qed

lemma A1_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes operands: "P is H1" "Q is H1" and merge: "M is A1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A1"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  let ?Par = "P \<parallel>\<^bsub>M\<^esub> Q"
  have started: "A1 ?Par (ades_obs True s0 ok' ac') = ?Par (ades_obs True s0 ok' ac')"
  proof -
    have "A1 ?Par (ades_obs True s0 ok' ac') =
      (\<exists>okL acL okR acR. P (ades_obs True s0 okL acL) \<and> Q (ades_obs True s0 okR acR) \<and>
        ades_merge_obs (A1m M) True s0 okL acL okR acR ok' ac')"
      by (simp add: A1_obs ades_par_by_merge_obs A1m_def Let_def; meson)
    also have "... = ?Par (ades_obs True s0 ok' ac')"
      by (simp only: Healthy_if[OF merge] ades_par_by_merge_obs)
    finally show ?thesis .
  qed
  have un: "ades_merge_obs M False s0 False {} False {} ok' ac'"
  proof -
    have "ades_merge_obs (A1m M) False s0 False {} False {} ok' ac'"
      by (simp add: A1m_def)
    then show ?thesis by (simp only: Healthy_if[OF merge])
  qed
  show "A1 ?Par (ades_obs ok0 s0 ok' ac') = ?Par (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case True
    then show ?thesis by (simp only: started)
  next
    case False
    then show ?thesis
      using operands[unfolded H1_healthy_obs_iff] un
      by (simp add: A1_obs ades_par_by_merge_obs; blast)
  qed
qed

lemma A_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes "P is H1" "Q is H1" "M is A0m" "M is A1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) is A0"
    by (rule A0_par_by_merge[OF assms(3)])
  moreover have "(P \<parallel>\<^bsub>M\<^esub> Q) is A1"
    by (rule A1_par_by_merge[OF assms(1,2,4)])
  ultimately show ?thesis
    by (simp add: Healthy_def' A_def)
qed

text \<open>A2 operands reduce branch choice sets to singleton witnesses. A2m preserves
  the accepted output at those witnesses.\<close>

lemma A2_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes operands: "P is A2" "Q is A2" and merge: "M is A2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A2"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  obtain N where M: "M = A2m N"
    using merge by (metis Healthy_def')
  have pick: "\<exists>x. (X = {} \<or> x \<in> X) \<and> S (ades_obs ok0 s0 okL {x})"
    if "S is A2" "S (ades_obs ok0 s0 okL X)" for S :: "'s angelic_design" and okL X
  proof -
    have "S (ades_obs ok0 s0 okL Y) \<longleftrightarrow> S (ades_obs ok0 s0 okL {}) \<or> (\<exists>y\<in>Y. S (ades_obs ok0 s0 okL {y}))"
      for Y using A2_obs[of S ok0 s0 okL Y] by (simp only: Healthy_if[OF that(1)])
    then show ?thesis
      using that(2) by (cases "X = {}") blast+
  qed
  have red: "ades_merge_obs M ok0 s0 okL {x} okR {y} ok' Y"
    if "ades_merge_obs M ok0 s0 okL acL okR acR ok' Y" "acL = {} \<or> x \<in> acL" "acR = {} \<or> y \<in> acR"
    for okL acL okR acR x y Y
    using that by (auto simp: M A2m_obs[simplified])
  have par: "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs ok0 s0 ok' Y) \<longleftrightarrow> (\<exists>okL x okR y.
      P (ades_obs ok0 s0 okL {x}) \<and> Q (ades_obs ok0 s0 okR {y}) \<and> ades_merge_obs M ok0 s0 okL {x} okR {y} ok' Y)"
    for Y
    unfolding ades_par_by_merge_obs
    using pick[OF operands(1)] pick[OF operands(2)] red by blast
  show "A2 (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs ok0 s0 ok' ac') = (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
    unfolding A2_obs par by (simp add: M A2m_obs[simplified]; blast)
qed

lemma A3_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes "P is H1" "Q is H1" "M is H1m" "M is H3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A3"
  by (rule H1_H3_impl_A3[OF H1_par_by_merge[OF assms(1-3)] H3_par_by_merge[OF assms(4)]])

subsubsection \<open>Symmetry and Associativity\<close>

text \<open>Use @{thm [source] par_by_merge_comm} for symmetric merges and
  @{thm [source] par_by_merge_assoc} for symmetric AssocMerge merges.
  These laws need no operand healthiness or mergeability premise.\<close>

subsection \<open>Lifting okL State Merge\<close>

subsubsection \<open>Construction\<close>

text \<open>The raw lift requires a witness in the output set for every branch-state pair.
  H3m releases the final set after divergence, retaining merge feasibility.\<close>

(* ades_lift_merge j ((ok,s), (okL,acL), (okR,acR), (ok',ac')) =
     acL \<noteq> {} \<and> acR \<noteq> {} \<and> ok' = (okL \<and> okR) \<and>
     (\<forall>sL \<in> acL. \<forall>sR \<in> acR. \<exists>s' \<in> ac'. j(s, sL, sR, s')) *)
definition ades_lift_merge :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ades_lift_merge j \<equiv> (\<lambda>(m,out).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        acL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        acR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        ac' = achoices.ac\<^sub>v (des_vars.more out)
    in acL \<noteq> {} \<and> acR \<noteq> {} \<and>
       des_vars.ok\<^sub>v out =
         (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
       (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s'))"

lemma ades_lift_merge_obs:
  "ades_merge_obs (ades_lift_merge j) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
    (acL \<noteq> {} \<and> acR \<noteq> {} \<and> ok' = (okL \<and> okR) \<and>
     (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s'))"
  by (auto simp: ades_lift_merge_def Let_def)

definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "merge_ades j \<equiv> H3m (H1m (ades_lift_merge j))"

lemma merge_ades_completion [simp]: "merge_ades j ;; II\<^sub>D = merge_ades j"
  by (simp add: merge_ades_def H3m_def seqr_assoc)

subsubsection \<open>Evaluation\<close>

text \<open>Started merges require nonempty branch sets and a witness for every state pair.
  Both branches terminating requires witnesses in the final set; divergence releases it.\<close>

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
  by (simp add: merge_ades_def H3m_def ades_lift_merge_def H1m_def Let_def;
      pred_auto; metis UNIV_I ex_in_conv)

lemma merge_ades_obs:
  "ades_merge_obs (merge_ades j) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
    (\<not> ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow>
        (ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
  by (auto simp: merge_ades_unfold Let_def)

subsubsection \<open>Healthiness and Symmetry\<close>

text \<open>The lifted merge satisfies all the healthiness conditions above, for every j.\<close>

lemma merge_ades_is_H1m [closure]: "merge_ades j is H1m"
  by (simp add: Healthy_def' merge_ades_def H3m_def H1m_def; pred_auto)

lemma merge_ades_is_H2m [closure]: "merge_ades j is H2m"
  by (simp add: Healthy_def' H2m_def merge_ades_def H3m_def seqr_assoc skip_d_absorb_J_1)

lemma merge_ades_is_HDM [closure]: "merge_ades j is HDM"
  by (rule HDM_intro[OF merge_ades_is_H1m merge_ades_is_H2m])

lemma merge_ades_is_H3m [closure]: "merge_ades j is H3m"
  by (simp add: Healthy_def' merge_ades_def H3m_idem)

lemma merge_ades_is_A0m [closure]: "merge_ades j is A0m"
  unfolding Healthy_def'
  by (rule ades_merge_ext)
     (auto simp: A0m_def merge_ades_obs[simplified] Let_def; blast)

lemma merge_ades_is_A1m [closure]: "merge_ades j is A1m"
  unfolding Healthy_def'
  by (rule ades_merge_ext)
     (auto simp: A1m_def merge_ades_obs[simplified] Let_def; blast)

lemma merge_ades_is_A2m [closure]: "merge_ades j is A2m"
  unfolding Healthy_def'
  by (rule ades_merge_ext) (auto simp: A2m_obs[simplified] merge_ades_obs[simplified])

lemma merge_ades_SymMerge [closure]:
  assumes "j is SymMerge"
  shows "merge_ades j is SymMerge"
  using assms
  by (simp add: Healthy_def' fun_eq_iff merge_ades_unfold; pred_auto; blast)

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
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR.
      P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      (\<not>ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (okL \<and> okR \<longrightarrow> (ok' \<and>
          (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s'))))))"
  by (simp add: ades_par_def
      par_by_merge_eval choices_ex merge_ades_obs[simplified])

subsubsection \<open>Healthiness Closure\<close>

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_def
  by (rule A_par_by_merge[OF assms merge_ades_is_A0m merge_ades_is_A1m])

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

text \<open>For A- and A2-healthy operands, ac2p and d2ac preserve parallel for every j.\<close>

lemma ades_par_d2ac_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = d2ac ((ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q))"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: A_healthy_components_iff)
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use assms(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    apply (rule ades_obs_ext)
    apply (simp only: ades_par_obs[OF assms] d2ac_healthy_obs[OF des_par_H_closure[OF H_implies_H1[OF designs_H(1)] H_implies_H1[OF designs_H(2)]]]
      des_par_expand ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(1)]]
      ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(2)]])
    by blast
qed

lemma ades_par_d2ac:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(d2ac P) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac Q) = d2ac (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)"
  by (simp only: ades_par_d2ac_ac2p[OF d2ac_is_A d2ac_is_A d2ac_is_A2 d2ac_is_A2]
      ac2p_d2ac[OF assms(1), simplified comp_apply]
      ac2p_d2ac[OF assms(2), simplified comp_apply])

lemma ades_par_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q)"
proof -
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use assms(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    by (simp only: ades_par_d2ac_ac2p[OF assms]
        ac2p_d2ac[OF des_par_H_closure[OF H_implies_H1[OF designs_H(1)] H_implies_H1[OF designs_H(2)]], simplified comp_apply])
qed

lemma ades_par_ac2p_d2ac:
  assumes "D is \<^bold>H" "E is \<^bold>H"
  shows "D \<parallel>\<^sub>D\<^bsub>j\<^esub> E = ac2p ((d2ac D) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac E))"
  by (simp only: ades_par_d2ac[OF assms]
      ac2p_d2ac[OF des_par_H_closure[OF H_implies_H1[OF assms(1)] H_implies_H1[OF assms(2)]], simplified comp_apply])

subsubsection \<open>Monotonicity\<close>

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1) \<sqsubseteq> (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_def
  using assms by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)

subsubsection \<open>Divergence and Zero Laws\<close>

lemma ades_par_diverge:
  assumes "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 False X)"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' Y)"
  using assms
  by (auto simp: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified]; blast)


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

text \<open>The proof transfers associativity through the D/AD correspondence.\<close>

lemma ades_par_assoc:
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and merge: "j is SymMerge" "AssocMerge j" "mergeable j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have represent: "S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> T = d2ac (ac2p (A S) \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p (A T))"
    and project: "ac2p (A (S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> T)) = ac2p (A S) \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p (A T)"
    if "S is A2" "T is A2" "S is H1" "T is H1" for S T
    using ades_par_d2ac_ac2p[of "A S" "A T" j] ades_par_ac2p[of "A S" "A T" j]
      ades_par_normalise_A[OF that, of j] Healthy_if[OF ades_par_A_closure[OF that(3,4)]]
      A_preserves_A2[OF that(1)] A_preserves_A2[OF that(2)]
    by (simp_all add: Healthy_def' A_idem)
  have pq: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
    and qr: "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is H1"
    using ades_par_A_closure[OF h1(1,2)] ades_par_A_closure[OF h1(2,3)]
    by (simp_all add: A_healthy_components_iff)
  show ?thesis
    by (simp only: represent[OF ades_par_A2_closure[OF operands(1,2)] operands(3) pq h1(3)]
        represent[OF operands(1) ades_par_A2_closure[OF operands(2,3)] h1(1) qr]
        project[OF operands(1,2) h1(1,2)] project[OF operands(2,3) h1(2,3)] des_par_assoc[OF merge])
qed

(* NDAD operands remove the mergeability premise from the AD law. *)
lemma ades_par_assoc_nondiv:
  fixes j :: "'s merge"
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and nondiv: "P is NDAD" "Q is NDAD" "R is NDAD"
      and merge: "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have represent: "S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> T = d2ac (ac2p (A S) \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p (A T))"
    and project: "ac2p (A (S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> T)) = ac2p (A S) \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p (A T)"
    if "S is A2" "T is A2" "S is H1" "T is H1" for S T
    using ades_par_d2ac_ac2p[of "A S" "A T" j] ades_par_ac2p[of "A S" "A T" j]
      ades_par_normalise_A[OF that, of j] Healthy_if[OF ades_par_A_closure[OF that(3,4)]]
      A_preserves_A2[OF that(1)] A_preserves_A2[OF that(2)]
    by (simp_all add: Healthy_def' A_idem)
  have pq: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
    and qr: "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is H1"
    using ades_par_A_closure[OF h1(1,2)] ades_par_A_closure[OF h1(2,3)]
    by (simp_all add: A_healthy_components_iff)
  have ndd: "ac2p (A T) is NDD" if "T is NDAD" for T :: "'s angelic_design"
    using that unfolding NDD_healthy_iff preD_true_iff NDAD_healthy_obs_iff
    by (auto simp: ac2p_def A_PBMH_ades A_obs StateII_def)
  show ?thesis
    by (simp only: represent[OF ades_par_A2_closure[OF operands(1,2)] operands(3) pq h1(3)]
        represent[OF operands(1) ades_par_A2_closure[OF operands(2,3)] h1(1) qr]
        project[OF operands(1,2) h1(1,2)] project[OF operands(2,3) h1(2,3)]
        des_par_assoc_nondiv[OF merge nondiv[THEN ndd]])
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
