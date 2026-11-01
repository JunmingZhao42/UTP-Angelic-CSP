theory tmp_pide_mcp_scratch_ades_generic_closure
  imports "UTP-Angelic-Designs.utp_ades_parallel"
begin

lemma generic_H1:
  fixes M :: "'s0 ades_merge_rel"
  assumes "P is H1" "Q is H1" "M is ADH1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H1"
proof -
  have un: "ades_merge_obs M False s0 False {} False {} c Z" for s0 c Z
    using assms(3)
    apply (simp add: Healthy_def' ADH1m_def fun_eq_iff)
    apply pred_auto
    by blast
  show ?thesis
    using assms(1,2)[unfolded H1_healthy_obs_iff] un
    by (simp add: H1_healthy_obs_iff ades_par_by_merge_eval choices_ex; blast)
qed

lemma generic_H2:
  fixes M :: "'s0 ades_merge_rel"
  assumes "M is ADH2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H2"
  using assms
  by (simp add: Healthy_def' H2_def ADH2m_def par_by_merge_def seqr_assoc)

lemma generic_H3:
  fixes M :: "'s0 ades_merge_rel"
  assumes "M is ADH3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is H3"
  using assms
  by (simp add: Healthy_def' H3_def ADH3m_def par_by_merge_def seqr_assoc)

definition merge_slice :: "'s0 ades_merge_rel \<Rightarrow> 's0 achoices des_vars_ext \<Rightarrow>
    's0 achoices des_vars_ext \<Rightarrow> 's0 angelic_design" where
  "merge_slice M l r \<equiv> (\<lambda>(x,z). ades_merge_eval M x l r z)"

lemma slice_obs:
  "merge_slice M (ades_output a L) (ades_output b R) (ades_obs c s0 d Z) =
    ades_merge_obs M c s0 a L b R d Z"
  by (simp add: merge_slice_def)

lemma par_obs:
  "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z) \<longleftrightarrow>
    (\<exists>a L d R. P (ades_obs b s0 a L) \<and> Q (ades_obs b s0 d R) \<and>
      merge_slice M (ades_output a L) (ades_output d R) (ades_obs b s0 c Z))"
  by (simp add: ades_par_by_merge_eval choices_ex merge_slice_def)

lemma ad_completion_obs:
  "H3 P (ades_obs b s0 c Z) \<longleftrightarrow>
    ((\<exists>Y. P (ades_obs b s0 False Y)) \<or> (c \<and> P (ades_obs b s0 True Z)))"
  apply (simp add: H3_def skip_d_def rdesign_def design_def)
  apply pred_auto
  by (metis (full_types))

lemma normal_AD_A3:
  assumes "P is H1" "P is H3"
  shows "P is A3"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c Z
  have h3: "P (ades_obs b s0 c Z) \<longleftrightarrow>
    ((\<exists>Y. P (ades_obs b s0 False Y)) \<or> (c \<and> P (ades_obs b s0 True Z)))"
    for b s0 c Z
    using ad_completion_obs[of P b s0 c Z] by (simp only: Healthy_if[OF assms(2)])
  have allfail: "(\<forall>z. P (ades_obs True s0 False {z})) \<Longrightarrow>
    P (ades_obs True s0 False {})"
    using h3[of True s0 False "{}"] by fastforce
  show "A3 P (ades_obs b s0 c Z) = P (ades_obs b s0 c Z)"
    apply (cases b)
    subgoal using h3[of True s0 c Z] allfail
      by (cases c; simp add: A3_obs; blast)
    subgoal using assms(1)[unfolded H1_healthy_obs_iff]
      by (simp add: A3_obs)
    done
qed

lemma generic_A3:
  fixes M :: "'s0 ades_merge_rel"
  assumes "P is H1" "Q is H1" "M is ADH1m" "M is ADH3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A3"
  by (rule normal_AD_A3[OF generic_H1[OF assms(1-3)] generic_H3[OF assms(4)]])

lemma generic_A2_slices:
  assumes "\<And>l r. merge_slice M l r is A2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A2"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c Z
  have obs: "merge_slice M l r (ades_obs b s0 c Z) \<longleftrightarrow>
    (merge_slice M l r (ades_obs b s0 c {}) \<or>
      (\<exists>z\<in>Z. merge_slice M l r (ades_obs b s0 c {z})))" for l r
    using A2_obs[of "merge_slice M l r" b s0 c Z]
    by (simp only: Healthy_if[OF assms])
  show "A2 (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z) =
    (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
    apply (simp only: A2_obs par_obs)
    using obs
    by fast
qed

lemma generic_A_slices:
  assumes operands: "P is H1" "Q is H1"
      and slices: "\<And>l r. merge_slice M l r is A"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c Z
  let ?R = "P \<parallel>\<^bsub>M\<^esub> Q"
  have started: "A ?R (ades_obs True s0 c Z) = ?R (ades_obs True s0 c Z)"
  proof -
    have "A ?R (ades_obs True s0 c Z) =
      (\<exists>a L d R. P (ades_obs True s0 a L) \<and> Q (ades_obs True s0 d R) \<and>
       A (merge_slice M (ades_output a L) (ades_output d R)) (ades_obs True s0 c Z))"
      apply (simp only: A_obs par_obs)
      by meson
    also have "... = ?R (ades_obs True s0 c Z)"
      by (simp only: Healthy_if[OF slices] par_obs)
    finally show ?thesis .
  qed
  have un: "merge_slice M (ades_output False {}) (ades_output False {}) (ades_obs False s0 c Z)"
    using A_obs[of "merge_slice M (ades_output False {}) (ades_output False {})" False s0 c Z]
    by (simp only: Healthy_if[OF slices]; simp)
  show "A ?R (ades_obs b s0 c Z) = ?R (ades_obs b s0 c Z)"
  proof (cases b)
    case True
    then show ?thesis by (simp only: started)
  next
    case False
    then show ?thesis
      using operands[unfolded H1_healthy_obs_iff] un
      by (simp add: A_obs par_obs; blast)
  qed
qed

lemma constructed_A_slices:
  "merge_slice (merge_ades j) l r is A"
  apply (rule Healthy_intro, rule ades_obs_ext)
  apply (cases l; cases r)
  apply (simp add: A_obs merge_slice_def merge_ades_unfold Let_def)
  by blast

lemma A2_atom:
  assumes "P is A2" "P (ades_obs b s0 c X)"
  shows "\<exists>x. (X = {} \<or> x \<in> X) \<and> P (ades_obs b s0 c {x})"
proof (cases "X = {}")
  case True
  have "P (ades_obs b s0 c {undefined})"
    using A2_obs[of P b s0 c "{undefined}"] assms True
    by (simp only: Healthy_if[OF assms(1)]; blast)
  then show ?thesis using True by blast
next
  case False
  show ?thesis using A2_nonempty_singleton[OF assms(1) False assms(2)] by blast
qed

lemma par_singletons:
  assumes operands: "P is A2" "Q is A2"
    and reduce: "\<And>b s0 a L d R c Z x y.
      \<lbrakk>ades_merge_obs M b s0 a L d R c Z; L = {} \<or> x \<in> L; R = {} \<or> y \<in> R\<rbrakk>
      \<Longrightarrow> ades_merge_obs M b s0 a {x} d {y} c Z"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z) \<longleftrightarrow>
    (\<exists>a x d y. P (ades_obs b s0 a {x}) \<and> Q (ades_obs b s0 d {y}) \<and>
      merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z))"
proof
  assume "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
  then obtain a L d R where pq:
    "P (ades_obs b s0 a L)" "Q (ades_obs b s0 d R)"
    "ades_merge_obs M b s0 a L d R c Z"
    by (auto simp: par_obs slice_obs)
  obtain x where x: "L = {} \<or> x \<in> L" "P (ades_obs b s0 a {x})"
    using A2_atom[OF operands(1) pq(1)] by blast
  obtain y where y: "R = {} \<or> y \<in> R" "Q (ades_obs b s0 d {y})"
    using A2_atom[OF operands(2) pq(2)] by blast
  show "\<exists>a x d y. P (ades_obs b s0 a {x}) \<and> Q (ades_obs b s0 d {y}) \<and>
    merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z)"
    using x(2) y(2) reduce[OF pq(3) x(1) y(1)] by (auto simp: slice_obs)
next
  assume "\<exists>a x d y. P (ades_obs b s0 a {x}) \<and> Q (ades_obs b s0 d {y}) \<and>
    merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z)"
  then show "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
    by (auto simp: par_obs)
qed

lemma generic_A2_atoms:
  assumes operands: "P is A2" "Q is A2"
    and reduce: "\<And>b s0 a L d R c Z x y.
      \<lbrakk>ades_merge_obs M b s0 a L d R c Z; L = {} \<or> x \<in> L; R = {} \<or> y \<in> R\<rbrakk>
      \<Longrightarrow> ades_merge_obs M b s0 a {x} d {y} c Z"
    and atoms: "\<And>a x d y. merge_slice M (ades_output a {x}) (ades_output d {y}) is A2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A2"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c Z
  have obs: "merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z) \<longleftrightarrow>
    (merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c {}) \<or>
     (\<exists>z\<in>Z. merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c {z})))"
    for a x d y
    using A2_obs[of "merge_slice M (ades_output a {x}) (ades_output d {y})" b s0 c Z]
    by (simp only: Healthy_if[OF atoms])
  show "A2 (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z) =
    (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
    apply (simp only: A2_obs par_singletons[OF operands reduce])
    using obs by fast
qed

lemma constructed_reduce:
  assumes "ades_merge_obs (merge_ades j) b s0 a L d R c Z"
    "L = {} \<or> x \<in> L" "R = {} \<or> y \<in> R"
  shows "ades_merge_obs (merge_ades j) b s0 a {x} d {y} c Z"
  using assms by (auto simp: merge_ades_obs[simplified]; blast)

lemma constructed_A2_atoms:
  "merge_slice (merge_ades j) (ades_output a {x}) (ades_output d {y}) is A2"
  by (rule Healthy_intro, rule ades_obs_ext;
      simp add: A2_obs slice_obs merge_ades_obs[simplified]; blast)

definition terminating_merge :: "('s set \<Rightarrow> bool) \<Rightarrow> 's ades_merge_rel" where
  "terminating_merge F \<equiv> (\<lambda>(m,z). \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
    (des_vars.ok\<^sub>v z \<and> F (achoices.ac\<^sub>v (des_vars.more z))))"

lemma terminating_merge_ADHM: "terminating_merge F is ADHM"
  by (simp add: Healthy_def' ADHM_def ADH1m_def ADH2m_def terminating_merge_def;
      pred_auto)

lemma terminating_merge_ADH3m: "terminating_merge F is ADH3m"
  by (simp add: Healthy_def' ADH3m_def terminating_merge_def; pred_auto)

lemma terminating_merge_par:
  "(true \<parallel>\<^bsub>terminating_merge F\<^esub> true) (ades_obs b s0 c Z) \<longleftrightarrow>
    (\<not>b \<or> (c \<and> F Z))"
  by (simp add: par_obs merge_slice_def terminating_merge_def true_pred_def)

lemma true_A_A2:
  "(true :: 's angelic_design) is A" "(true :: 's angelic_design) is A2"
  by (rule Healthy_intro, rule ades_obs_ext; auto simp: A_obs A2_obs true_pred_def)+

lemma ADHM_ADH3m_not_A:
  "\<not> ((true \<parallel>\<^bsub>terminating_merge (\<lambda>Z :: bool set. Z = {})\<^esub> true) is A)"
proof
  let ?P = "true \<parallel>\<^bsub>terminating_merge (\<lambda>Z :: bool set. Z = {})\<^esub> true"
  assume h: "?P is A"
  have "A ?P (ades_obs True False True {}) = ?P (ades_obs True False True {})"
    by (simp only: Healthy_if[OF h])
  then show False by (simp add: A_obs terminating_merge_par)
qed

lemma ADHM_ADH3m_not_A2:
  "\<not> ((true \<parallel>\<^bsub>terminating_merge (\<lambda>Z :: bool set. {False,True} \<subseteq> Z)\<^esub> true) is A2)"
proof
  let ?P = "true \<parallel>\<^bsub>terminating_merge (\<lambda>Z :: bool set. {False,True} \<subseteq> Z)\<^esub> true"
  assume h: "?P is A2"
  have "A2 ?P (ades_obs True False True UNIV) = ?P (ades_obs True False True UNIV)"
    by (simp only: Healthy_if[OF h])
  then show False by (auto simp: A2_obs terminating_merge_par)
qed

lemma recovered_constructed_A:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A"
  by (rule generic_A_slices[OF assms constructed_A_slices])

lemma recovered_constructed_A2:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A2"
  by (rule generic_A2_atoms[OF assms constructed_reduce constructed_A2_atoms])

lemma recovered_constructed_A3:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A3"
  by (rule generic_A3[OF assms merge_ades_ADH1m merge_ades_ADH3m])

lemma constructed_not_all_A2_slices:
  defines "j \<equiv> (\<lambda>(m,z). z = mrg_left\<^sub>v m) :: bool merge"
  shows "\<not> (merge_slice (merge_ades j) (ades_output True UNIV)
    (ades_output True {False}) is A2)"
proof
  let ?S = "merge_slice (merge_ades j) (ades_output True UNIV) (ades_output True {False})"
  assume h: "?S is A2"
  have "A2 ?S (ades_obs True False True UNIV) = ?S (ades_obs True False True UNIV)"
    by (simp only: Healthy_if[OF h])
  then show False
    by (simp add: A2_obs slice_obs merge_ades_obs[simplified] j_def all_bool_eq ex_bool_eq)
qed

end
