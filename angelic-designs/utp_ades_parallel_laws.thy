section \<open>AD Parallel-by-Merge Laws\<close>

theory utp_ades_parallel_laws
  imports utp_ades_parallel_merge
begin

text \<open>Parallel-by-merge laws for any AD merge.\<close>

subsection \<open>Healthiness Closure\<close>

text \<open>The design rules @{thm [source] H1_par_by_merge}, @{thm [source] H2_par_by_merge}
  and @{thm [source] H3_par_by_merge} apply to AD relations directly. The rules below
  cover A, A2 and A3.\<close>

lemma PBMH_ades_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes "M is PBMHm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is PBMH_ades"
  unfolding Healthy_def'
  apply (rule ades_obs_ext)
  apply (simp only: PBMH_ades_obs ades_par_by_merge_obs)
  using PBMHm_up[OF assms] by blast

lemma A0_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes "M is A0m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A0"
proof -
  obtain N where M: "M = A0m N"
    using assms by (metis Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        auto simp: A0_obs ades_par_by_merge_obs M A0m_eval; blast)
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
      by (simp add: A1_obs ades_par_by_merge_obs A1m_eval Let_def; meson)
    also have "... = ?Par (ades_obs True s0 ok' ac')"
      by (simp only: Healthy_if[OF merge] ades_par_by_merge_obs)
    finally show ?thesis .
  qed
  have un: "ades_merge_obs M False s0 False {} False {} ok' ac'"
  proof -
    have "ades_merge_obs (A1m M) False s0 False {} False {} ok' ac'"
      by (simp add: A1m_eval)
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
  assumes "P is H1" "Q is H1" "M is ADm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A"
  using A0_par_by_merge A1_par_by_merge[OF assms(1,2)] assms(3)[unfolded ADm_healthy_iff]
  by (auto simp: Healthy_def' A_def)

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

subsection \<open>Symmetry and Associativity\<close>

text \<open>Use @{thm [source] par_by_merge_comm} for symmetric merges and
  @{thm [source] par_by_merge_assoc} for symmetric AssocMerge merges.
  These laws need no operand healthiness or mergeability premise.\<close>

subsection \<open>Choice\<close>

text \<open>Demonic choice is disjunction, so parallel distributes over it. Angelic choice
  is conjunction, so parallel only subdistributes: (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R).\<close>

(* P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R) *)
lemma ades_par_by_merge_demonic_distl:
  fixes P Q R :: "'s angelic_design" and M :: "'s ades_merge_rel"
  shows "P \<parallel>\<^bsub>M\<^esub> (Q \<sqinter>\<^sub>A\<^sub>D R) = (P \<parallel>\<^bsub>M\<^esub> Q) \<sqinter>\<^sub>A\<^sub>D (P \<parallel>\<^bsub>M\<^esub> R)"
  by (simp only: angelic_design_demonic par_by_merge_disj_distl)

(* (P \<sqinter> Q) \<parallel> R = (P \<parallel> R) \<sqinter> (Q \<parallel> R) *)
lemma ades_par_by_merge_demonic_distr:
  fixes P Q R :: "'s angelic_design" and M :: "'s ades_merge_rel"
  shows "(P \<sqinter>\<^sub>A\<^sub>D Q) \<parallel>\<^bsub>M\<^esub> R = (P \<parallel>\<^bsub>M\<^esub> R) \<sqinter>\<^sub>A\<^sub>D (Q \<parallel>\<^bsub>M\<^esub> R)"
  by (simp only: angelic_design_demonic par_by_merge_disj_distr)

(* (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R) *)
lemma ades_par_by_merge_angelic_subdistl:
  fixes P Q R :: "'s angelic_design" and M :: "'s ades_merge_rel"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P \<parallel>\<^bsub>M\<^esub> R) \<sqsubseteq> P \<parallel>\<^bsub>M\<^esub> (Q \<squnion>\<^sub>A\<^sub>D R)"
  by (simp only: angelic_design_angelic par_by_merge_conj_subdistl)

(* (P \<parallel> R) \<squnion> (Q \<parallel> R) \<sqsubseteq> (P \<squnion> Q) \<parallel> R *)
lemma ades_par_by_merge_angelic_subdistr:
  fixes P Q R :: "'s angelic_design" and M :: "'s ades_merge_rel"
  shows "(P \<parallel>\<^bsub>M\<^esub> R) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^bsub>M\<^esub> R) \<sqsubseteq> (P \<squnion>\<^sub>A\<^sub>D Q) \<parallel>\<^bsub>M\<^esub> R"
  by (simp only: angelic_design_angelic par_by_merge_conj_subdistr)

end
