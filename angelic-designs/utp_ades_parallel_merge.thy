section \<open>AD Merge Healthiness\<close>

theory utp_ades_parallel_merge
  imports utp_ades_designs
begin

text \<open>AD merge observations and merge healthiness, for any AD merge.\<close>

subsection \<open>Merge Observations\<close>

type_synonym 's ades_mrg =
  "('s astate des_vars_ext, 's achoices des_vars_ext, 's achoices des_vars_ext) mrg"

type_synonym 's ades_merge_rel = "('s ades_mrg, 's achoices des_vars_ext) urel"

abbreviation ades_merge_obs where
  "ades_merge_obs M ok0 s0 okL acL okR acR ok' ac' \<equiv>
    (\<lambda>(x,z). merge_eval M x (ades_output okL acL) (ades_output okR acR) z)
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
  and HDm come from the design theory. A closure uses ADm;
  A3 closure follows from H1m and H3m.\<close>

subsubsection \<open>A0m and A1m\<close>

(* A0m M = M \<and> (ok \<and> ac' = {} \<longrightarrow> M[False/ok']) *)
definition A0m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A0m M \<equiv> (M \<and>
    (($<:ok\<^sup>< \<and> $\<^bold>v\<^sub>D:ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e
      \<longrightarrow> M\<lbrakk>\<guillemotleft>False\<guillemotright>/ok\<^sup>>\<rbrakk>))"

lemma A0m_eval:
  "A0m M = (\<lambda>(m,z).
     M (m,z) \<and>
     (des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<and> des_vars.ok\<^sub>v z \<and> achoices.ac\<^sub>v (des_vars.more z) = {}
       \<longrightarrow> M (m, ades_output False {})))"
  by (rule ades_merge_ext; rename_tac ok0 s0 okL acL okR acR ok' ac';
      case_tac ok'; simp add: A0m_def; pred_auto)

(* A1m M = HDm (PBMH_ades M) *)
definition A1m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A1m M \<equiv> HDm (PBMH_ades M)"

(* A1m M (m, (ok', ac')) = \<not> ok \<or> (\<exists>Y \<subseteq> ac'. M (m, (False, Y))) \<or>
     (ok' \<and> (\<exists>Y \<subseteq> ac'. M (m, (True, Y)))) *)
lemma A1m_eval:
  "A1m M = (\<lambda>(m,z).
     let ac' = achoices.ac\<^sub>v (des_vars.more z)
     in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
        (\<exists>Y\<subseteq>ac'. M (m, ades_output False Y)) \<or>
        (des_vars.ok\<^sub>v z \<and> (\<exists>Y\<subseteq>ac'. M (m, ades_output True Y))))"
  by (rule ades_merge_ext; simp add: A1m_def PBMH_ades_def HDm_def Let_def H1m_def H2m_def J_def pbmh_step_def seq_def choices_ex ex_bool_eq;
      pred_auto)

lemma A0m_Idempotent [closure]: "Idempotent A0m"
  unfolding Idempotent_def
  by (intro allI, rule ades_merge_ext) (auto simp: A0m_eval)

lemma A1m_Idempotent [closure]: "Idempotent A1m"
  unfolding Idempotent_def
  by (intro allI, rule ades_merge_ext) (auto simp: A1m_eval Let_def; blast)

lemma A0m_Monotonic [closure]: "Monotonic A0m"
  by (rule MonotonicI) (auto simp: pred_refine_iff A0m_eval)

lemma A1m_Monotonic [closure]: "Monotonic A1m"
  unfolding A1m_def
  by (rule Monotonic_comp[OF HDm_Monotonic PBMH_ades_Monotonic, unfolded comp_def])

subsubsection \<open>ADm\<close>

(* ADm combines A0m and A1m; A2m is a separate merge condition. *)
definition ADm :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "ADm \<equiv> A0m \<circ> A1m"

lemma ADm_A0m: "ADm M is A0m"
  by (simp add: Healthy_def' ADm_def
      A0m_Idempotent[unfolded Idempotent_def, rule_format])

lemma ADm_A1m: "ADm M is A1m"
  unfolding Healthy_def' ADm_def
  apply (rule ades_merge_ext)
  subgoal for ok0 s0 okL acL okR acR ok' ac'
    by (cases ok0; cases ok'; cases "ac' = {}";
        auto simp: A0m_eval A1m_eval Let_def; blast)
  done

lemma ADm_healthy_iff:
  "(M is ADm) \<longleftrightarrow> ((M is A0m) \<and> (M is A1m))"
  using ADm_A0m[of M] ADm_A1m[of M] by (auto simp: Healthy_def' ADm_def)

lemma ADm_Idempotent [closure]: "Idempotent ADm"
  by (rule IdempotentI) (simp add: ADm_healthy_iff[THEN iffD2] ADm_A0m ADm_A1m Healthy_if)

lemma ADm_Monotonic [closure]: "Monotonic ADm"
  unfolding ADm_def
  by (rule Monotonic_comp[OF A0m_Monotonic A1m_Monotonic])

subsubsection \<open>A2m\<close>

(* Singleton branches admit empty or singleton output witnesses;
   other branches retain M and require those witnesses at every eligible pair. *)
definition A2m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A2m M \<equiv>
    ((((\<exists>sL. $0:\<^bold>v\<^sub>D:ac\<^sup>< = {sL}) \<and>
       (\<exists>sR. $1:\<^bold>v\<^sub>D:ac\<^sup>< = {sR})) \<or> M) \<and>
     (\<forall>sL sR.
       ($0:\<^bold>v\<^sub>D:ac\<^sup>< = {} \<or> sL \<in> $0:\<^bold>v\<^sub>D:ac\<^sup><) \<and>
       ($1:\<^bold>v\<^sub>D:ac\<^sup>< = {} \<or> sR \<in> $1:\<^bold>v\<^sub>D:ac\<^sup><) \<longrightarrow>
       @(A2 M)\<lbrakk>\<guillemotleft>{sL}\<guillemotright>, \<guillemotleft>{sR}\<guillemotright>/0:\<^bold>v\<^sub>D:ac\<^sup><, 1:\<^bold>v\<^sub>D:ac\<^sup><\<rbrakk>))\<^sub>e"

lemma A2m_obs_A2:
  "ades_merge_obs (A2m M) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
    ((\<exists>sL. acL = {sL}) \<and> (\<exists>sR. acR = {sR}) \<or>
      ades_merge_obs M ok0 s0 okL acL okR acR ok' ac') \<and>
    (\<forall>sL sR. (acL = {} \<or> sL \<in> acL) \<and> (acR = {} \<or> sR \<in> acR) \<longrightarrow>
      ades_merge_obs (A2 M) ok0 s0 okL {sL} okR {sR} ok' ac')"
  by (simp add: A2m_def expr_defs lens_defs alpha_defs)

lemma A2m_obs:
  "ades_merge_obs (A2m M) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
    ((\<exists>p. acL = {p}) \<and> (\<exists>q. acR = {q}) \<or> ades_merge_obs M ok0 s0 okL acL okR acR ok' ac') \<and>
    (\<forall>x y. (acL = {} \<or> x \<in> acL) \<and> (acR = {} \<or> y \<in> acR) \<longrightarrow>
       ades_merge_obs M ok0 s0 okL {x} okR {y} ok' {} \<or>
       (\<exists>w\<in>ac'. ades_merge_obs M ok0 s0 okL {x} okR {y} ok' {w}))"
  by (simp add: A2m_obs_A2[simplified] A2_output_obs)

lemma A2m_Idempotent [closure]: "Idempotent A2m"
proof (rule IdempotentI)
  fix M :: "'s ades_merge_rel"
  have singleton:
    "ades_merge_obs (A2m M) ok0 s0 okL {sL} okR {sR} ok' X =
      ades_merge_obs (A2 M) ok0 s0 okL {sL} okR {sR} ok' X"
    for ok0 s0 okL sL okR sR ok' X
    by (simp add: A2m_obs_A2[simplified])
  have normalised:
    "ades_merge_obs (A2 (A2m M)) ok0 s0 okL {sL} okR {sR} ok' X =
      ades_merge_obs (A2 M) ok0 s0 okL {sL} okR {sR} ok' X"
    for ok0 s0 okL sL okR sR ok' X
    by (subst A2_idem[of M, symmetric])
       (simp add: A2_output_obs singleton[simplified])
  show "A2m (A2m M) = A2m M"
    by (rule ades_merge_ext;
        simp add: A2m_obs_A2[simplified] normalised[simplified]; blast)
qed

lemma A2m_Monotonic [closure]: "Monotonic A2m"
proof (rule MonotonicI)
  fix M N :: "'s ades_merge_rel"
  assume refinement: "M \<sqsubseteq> N"
  have normalised: "A2 M \<sqsubseteq> A2 N"
    by (rule A2_mono[OF refinement])
  show "A2m M \<sqsubseteq> A2m N"
    using refinement normalised
    by (auto simp: pred_refine_iff A2m_def expr_defs lens_defs)
qed

subsubsection \<open>Choice-set closure\<close>

(* PBMHm M = PBMH_ades (M \<and> ac' \<noteq> {}) *)
definition PBMHm :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "PBMHm M \<equiv> PBMH_ades (M \<and> ($\<^bold>v\<^sub>D:ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"

(* m = ((ok,s),(okL,acL),(okR,acR)).
   PBMHm M(m,(ok',ac')) =
     (\<exists>X \<subseteq> ac'. X \<noteq> {} \<and> M(m,(ok',X))). *)
lemma PBMHm_obs:
  "ades_merge_obs (PBMHm M) ok0 s0 okL X okR Y ok' Z =
    (\<exists>Z' \<subseteq> Z. Z' \<noteq> {} \<and> ades_merge_obs M ok0 s0 okL X okR Y ok' Z')"
  by (simp add: PBMHm_def PBMH_ades_def pbmh_step_def seq_def choices_ex; pred_auto)

lemma PBMHm_idem: "PBMHm (PBMHm M) = PBMHm M"
  apply (rule ades_merge_ext)
  apply (simp add: PBMHm_obs[simplified])
  by blast

lemma PBMHm_Idempotent [closure]: "Idempotent PBMHm"
  by (simp add: Idempotent_def PBMHm_idem)

lemma PBMHm_Monotonic [closure]: "Monotonic PBMHm"
  unfolding PBMHm_def
  by (rule MonotonicI, rule PBMH_ades_mono; simp add: pred_refine_iff conj_pred_def)

lemma PBMHm_up:
  assumes "M is PBMHm" "Z \<subseteq> Z'" "ades_merge_obs M ok0 s0 okL X okR Y ok' Z"
  shows "ades_merge_obs M ok0 s0 okL X okR Y ok' Z'"
proof -
  have w: "\<exists>W \<subseteq> Z. W \<noteq> {} \<and> ades_merge_obs M ok0 s0 okL X okR Y ok' W"
    using assms(3)
    by (subst (asm) Healthy_if[OF assms(1), symmetric]; simp add: PBMHm_obs[simplified])
  show ?thesis
    apply (subst Healthy_if[OF assms(1), symmetric])
    apply (simp add: PBMHm_obs[simplified])
    using w assms(2) by (blast intro: subset_trans)
qed

subsubsection \<open>Commutation\<close>

lemma H1m_AD_commute:
  "H1m (A0m M) = A0m (H1m M)"
  "H1m (A1m M) = A1m (H1m M)"
  by (rule ades_merge_ext; simp add: A0m_eval A1m_eval Let_def; pred_simp; blast)+

lemma H1m_A2m_commute:
  "H1m (A2m M) = A2m (H1m M)"
  by (rule ades_merge_ext; rename_tac ok0 s0 okL acL okR acR ok' ac'; case_tac ok0;
      simp add: A2m_obs[simplified] H1m_def; pred_simp;
      simp add: A2m_obs[simplified])

(* H2m is called CSPA2m on the RAD alphabet.
   H2m M(m,(ok',ac')) = M(m,(ok',ac')) \<or> (ok' \<and> M(m,(False,ac'))). *)
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
  by (rule ades_merge_ext; auto simp: H2m_ades_obs[simplified] A0m_eval)

lemma H2m_A1m_commute:
  "H2m (A1m M) = A1m (H2m M)"
  by (rule ades_merge_ext; auto simp: H2m_ades_obs[simplified] A1m_eval Let_def)

lemma H3m_A0m_commute:
  "H3m (A0m M) = A0m (H3m M)"
  by (rule ades_merge_ext; auto simp: H3m_ades_obs[simplified] A0m_eval)

lemma H3m_A1m_commute:
  "H3m (A1m M) = A1m (H3m M)"
  by (rule ades_merge_ext; auto simp: H3m_ades_obs[simplified] A1m_eval Let_def; blast)

lemma HDm_angelic_commute:
  "HDm (A0m M) = A0m (HDm M)"
  "HDm (A1m M) = A1m (HDm M)"
  by (simp add: HDm_def H1m_AD_commute H2m_A0m_commute H2m_A1m_commute)+

lemma PBMHm_H2m_commute: "PBMHm (H2m M) = H2m (PBMHm M)"
  by (rule ades_merge_ext; auto simp: PBMHm_obs[simplified] H2m_ades_obs[simplified] ; blast)

end
