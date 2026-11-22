section \<open>AD Parallel-by-Merge Laws\<close>

theory utp_ades_parallel_laws
  imports utp_ades_designs
begin

text \<open>AD merge healthiness and parallel-by-merge laws for any AD merge.\<close>

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
  and HDm come from the design theory. A closure uses ADm;
  A3 closure follows from H1m and H3m.\<close>

subsubsection \<open>A0m and A1m\<close>

(* A0m M = M \<and> (ok \<and> ac' = {} \<longrightarrow> M[False/ok']) *)
definition A0m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A0m M \<equiv> (M \<and>
    (($<:ok\<^sup>< \<and> $\<^bold>v\<^sub>D:ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e
      \<longrightarrow> M\<lbrakk>\<guillemotleft>False\<guillemotright>/ok\<^sup>>\<rbrakk>))"

lemma A0m_eval:
  "A0m M = (\<lambda>(m,out).
     M (m,out) \<and>
     (des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<and> des_vars.ok\<^sub>v out \<and> achoices.ac\<^sub>v (des_vars.more out) = {}
       \<longrightarrow> M (m, ades_output False {})))"
  by (rule ades_merge_ext; rename_tac ok0 s0 okL acL okR acR ok' ac';
      case_tac ok'; simp add: A0m_def; pred_auto)

(* A1m M = HDm (PBMH_ades M) *)
definition A1m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A1m M \<equiv> HDm (PBMH_ades M)"

(* A1m M (m, (ok', ac')) = \<not> ok \<or> (\<exists>Y \<subseteq> ac'. M (m, (False, Y))) \<or>
     (ok' \<and> (\<exists>Y \<subseteq> ac'. M (m, (True, Y)))) *)
lemma A1m_eval:
  "A1m M = (\<lambda>(m,out).
     let ac' = achoices.ac\<^sub>v (des_vars.more out)
     in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
        (\<exists>Y\<subseteq>ac'. M (m, ades_output False Y)) \<or>
        (des_vars.ok\<^sub>v out \<and> (\<exists>Y\<subseteq>ac'. M (m, ades_output True Y))))"
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

text \<open>A2m healthiness is singleton output normalization together with
  preservation of acceptance at every eligible singleton branch pair.
  An empty branch choice set permits every singleton replacement.\<close>

lemma A2m_healthy_iff:
  "M is A2m \<longleftrightarrow>
    (\<forall>ok0 s0 okL sL okR sR ok' ac'.
      ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac' \<longleftrightarrow>
      ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {} \<or>
      (\<exists>s'\<in>ac'. ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {s'})) \<and>
    (\<forall>ok0 s0 okL acL okR acR ok' ac' sL sR.
      ades_merge_obs M ok0 s0 okL acL okR acR ok' ac' \<and>
      (acL = {} \<or> sL \<in> acL) \<and> (acR = {} \<or> sR \<in> acR) \<longrightarrow>
      ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac')"
  (is "_ \<longleftrightarrow> ?conditions")
proof (rule iffI)
  assume healthy: "M is A2m"
  have norm: "ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac' =
    (ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {} \<or>
     (\<exists>s'\<in>ac'. ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {s'}))"
    for ok0 s0 okL sL okR sR ok' ac'
    by (subst Healthy_if[OF healthy, symmetric]) (simp add: A2m_obs[simplified])
  have restrict: "ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac'"
    if "ades_merge_obs M ok0 s0 okL acL okR acR ok' ac'"
       "acL = {} \<or> sL \<in> acL" "acR = {} \<or> sR \<in> acR"
    for ok0 s0 okL acL okR acR ok' ac' sL sR
  proof -
    have accepted: "ades_merge_obs (A2m M) ok0 s0 okL acL okR acR ok' ac'"
      using that(1) by (simp only: Healthy_if[OF healthy])
    have "ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {} \<or>
      (\<exists>s'\<in>ac'. ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {s'})"
      using accepted that(2,3)
      by (simp add: A2m_obs[simplified])
    then show ?thesis by (rule norm[THEN iffD2])
  qed
  show ?conditions
    by (intro conjI allI impI; (rule norm | (elim conjE, rule restrict))) assumption+
next
  assume conditions: ?conditions
  have norm: "ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac' =
    (ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {} \<or>
     (\<exists>s'\<in>ac'. ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' {s'}))"
    for ok0 s0 okL sL okR sR ok' ac'
    by (rule conditions[THEN conjunct1, rule_format])
  have restrict: "ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac'"
    if "ades_merge_obs M ok0 s0 okL acL okR acR ok' ac'"
       "acL = {} \<or> sL \<in> acL" "acR = {} \<or> sR \<in> acR"
    for ok0 s0 okL acL okR acR ok' ac' sL sR
    using conditions[THEN conjunct2, rule_format] that by blast
  show "M is A2m"
  proof (rule Healthy_intro, rule ades_merge_ext)
    fix ok0 s0 okL acL okR acR ok' ac'
    show "ades_merge_obs (A2m M) ok0 s0 okL acL okR acR ok' ac' =
      ades_merge_obs M ok0 s0 okL acL okR acR ok' ac'"
      by (auto simp: A2m_obs[simplified] norm[simplified, symmetric]
          intro: restrict[simplified])
  qed
qed

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

(* ABm M = acL \<noteq> {} \<and> acR \<noteq> {} \<and>
     (\<exists>X Y. acL \<subseteq> X \<and> acR \<subseteq> Y \<and> M[X,Y/acL,acR]) *)
definition ABm :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "ABm M \<equiv>
    ($0:\<^bold>v\<^sub>D:ac\<^sup>< \<noteq> {} \<and> $1:\<^bold>v\<^sub>D:ac\<^sup>< \<noteq> {} \<and>
     (\<exists>X Y. $0:\<^bold>v\<^sub>D:ac\<^sup>< \<subseteq> X \<and> $1:\<^bold>v\<^sub>D:ac\<^sup>< \<subseteq> Y \<and>
       M\<lbrakk>\<guillemotleft>X\<guillemotright>, \<guillemotleft>Y\<guillemotright>/0:\<^bold>v\<^sub>D:ac\<^sup><, 1:\<^bold>v\<^sub>D:ac\<^sup><\<rbrakk>))\<^sub>e"

(* m = ((ok,s),(okL,acL),(okR,acR)).
   PBMHm M(m,(ok',ac')) =
     (\<exists>X \<subseteq> ac'. X \<noteq> {} \<and> M(m,(ok',X))). *)
lemma PBMHm_obs:
  "ades_merge_obs (PBMHm M) ok0 s0 okL X okR Y ok' Z =
    (\<exists>Z' \<subseteq> Z. Z' \<noteq> {} \<and> ades_merge_obs M ok0 s0 okL X okR Y ok' Z')"
  by (simp add: PBMHm_def PBMH_ades_def pbmh_step_def seq_def choices_ex; pred_auto)

(* ABm M((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
     acL \<noteq> {} \<and> acR \<noteq> {} \<and>
     (\<exists>X Y. acL \<subseteq> X \<and> acR \<subseteq> Y \<and> M((ok,s),(okL,X),(okR,Y),(ok',ac'))). *)
lemma ABm_obs:
  "ades_merge_obs (ABm M) ok0 s0 okL X okR Y ok' Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and>
      (\<exists>X' Y'. X \<subseteq> X' \<and> Y \<subseteq> Y' \<and> ades_merge_obs M ok0 s0 okL X' okR Y' ok' Z))"
  by (simp add: ABm_def; pred_auto)

lemma PBMHm_idem: "PBMHm (PBMHm M) = PBMHm M"
  apply (rule ades_merge_ext)
  apply (simp add: PBMHm_obs[simplified])
  by blast

lemma ABm_idem: "ABm (ABm M) = ABm M"
  apply (rule ades_merge_ext)
  apply (simp add: ABm_obs[simplified])
  by (meson order_refl order_trans)

lemma PBMHm_Idempotent [closure]: "Idempotent PBMHm"
  by (simp add: Idempotent_def PBMHm_idem)

lemma PBMHm_Monotonic [closure]: "Monotonic PBMHm"
  unfolding PBMHm_def
  by (rule MonotonicI, rule PBMH_ades_mono; simp add: pred_refine_iff conj_pred_def)

lemma ABm_Idempotent [closure]: "Idempotent ABm"
  by (simp add: Idempotent_def ABm_idem)

lemma ABm_Monotonic [closure]: "Monotonic ABm"
proof (rule MonotonicI)
  fix P Q :: "'s ades_merge_rel"
  assume "P \<sqsubseteq> Q"
  then have pointwise: "Q z \<Longrightarrow> P z" for z
    unfolding pred_refine_iff by blast
  show "ABm P \<sqsubseteq> ABm Q"
    by (auto simp: pred_refine_iff ABm_def expr_defs dest: pointwise)
qed

lemma ABm_restrict:
  assumes "M is ABm" "X' \<subseteq> X" "Y' \<subseteq> Y" "X' \<noteq> {}" "Y' \<noteq> {}"
    "ades_merge_obs M ok0 s0 okL X okR Y ok' Z"
  shows "ades_merge_obs M ok0 s0 okL X' okR Y' ok' Z"
proof -
  have w: "\<exists>U V. X \<subseteq> U \<and> Y \<subseteq> V \<and> ades_merge_obs M ok0 s0 okL U okR V ok' Z"
    using assms(6)
    by (subst (asm) Healthy_if[OF assms(1), symmetric]; simp add: ABm_obs[simplified])
  show ?thesis
    apply (subst Healthy_if[OF assms(1), symmetric])
    apply (simp add: ABm_obs[simplified] assms(4,5))
    using w assms(2,3)
    apply (simp only: case_prod_conv)
    by (meson subset_trans)
qed

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

lemma PBMHm_ABm_commute: "PBMHm (ABm M) = ABm (PBMHm M)"
  by (rule ades_merge_ext; simp add: PBMHm_obs[simplified] ABm_obs[simplified]; blast)

lemma PBMHm_H2m_commute: "PBMHm (H2m M) = H2m (PBMHm M)"
  by (rule ades_merge_ext; auto simp: PBMHm_obs[simplified] H2m_ades_obs[simplified] ; blast)

lemma ABm_H2m_commute: "ABm (H2m M) = H2m (ABm M)"
  by (rule ades_merge_ext; auto simp: ABm_obs[simplified] H2m_ades_obs[simplified] ; blast)

subsection \<open>Generic AD Parallel Laws\<close>

subsubsection \<open>Healthiness Closure\<close>

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

subsubsection \<open>Symmetry and Associativity\<close>

text \<open>Use @{thm [source] par_by_merge_comm} for symmetric merges and
  @{thm [source] par_by_merge_assoc} for symmetric AssocMerge merges.
  These laws need no operand healthiness or mergeability premise.\<close>

subsubsection \<open>Choice\<close>

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

subsection \<open>Choice-set lifting\<close>

(* ac'_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
     (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. M((ok,s),(okL,sL),(okR,sR),(ok',s'))). *)
definition ac'_lift_merge :: "'s des_merge \<Rightarrow> 's ades_merge_rel" where
  "ac'_lift_merge M \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; p = mrg_left\<^sub>v m; q = mrg_right\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x);
        acL = achoices.ac\<^sub>v (des_vars.more p);
        acR = achoices.ac\<^sub>v (des_vars.more q);
        ac' = achoices.ac\<^sub>v (des_vars.more z)
    in \<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
      merge_eval M
        \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v x, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v p, \<dots> = sL\<rparr>
        \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v q, \<dots> = sR\<rparr>
        \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v z, \<dots> = s'\<rparr>)"

lemma ac'_lift_merge_obs:
  "ades_merge_obs (ac'_lift_merge M) ok0 s0 okL acL okR acR ok' ac' =
    (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
      merge_eval M \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)"
  by (simp add: ac'_lift_merge_def Let_def)

lemma ABm_ac'_lift_merge_obs:
  "ades_merge_obs (ABm (ac'_lift_merge M)) ok0 s0 okL acL okR acR ok' ac' =
    (acL \<noteq> {} \<and> acR \<noteq> {} \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
      merge_eval M \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>))"
  by (simp add: ABm_obs[simplified] ac'_lift_merge_obs[simplified]; blast)

text \<open>The AD lift of a design merge completes after lifting, so divergence
  releases the final choice set, including to the empty set.\<close>

(* Before start, ordinary merging into Z, or divergence with unrestricted output. *)
lemma ac'_lift_merge_completion_obs:
  "ades_merge_obs (H3m (H1m (ABm (ac'_lift_merge M)))) ok0 s0 okL X okR Y ok' Z \<longleftrightarrow>
    (\<not> ok0 \<or>
     (X \<noteq> {} \<and> Y \<noteq> {} \<and>
       ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
           merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
             \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
             \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>) \<or>
        (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'.
           merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
             \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
             \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>))))"
  apply (simp only: H3m_ades_obs)
  apply (simp add: H1m_def disj_pred_def expr_defs lens_defs alpha_defs)
  apply (simp add: ABm_ac'_lift_merge_obs[simplified])
  by (cases ok0; simp; blast intro: exI[where x=UNIV])

subsection \<open>Correspondence with Designs\<close>

lemma A_A2_pick:
  assumes "R is A" "R is A2" "X \<noteq> {}"
  shows "R (ades_obs b s0 c X) \<longleftrightarrow> (\<exists>x\<in>X. R (ades_obs b s0 c {x}))"
proof -
  have a2: "R (ades_obs b s0 c Y) \<longleftrightarrow>
      R (ades_obs b s0 c {}) \<or> (\<exists>y\<in>Y. R (ades_obs b s0 c {y}))" for Y
    using A2_obs[of R b s0 c Y] by (simp only: Healthy_if[OF assms(2)])
  have up: "R (ades_obs b s0 c {}) \<Longrightarrow> R (ades_obs b s0 c {y})" for y
    using PBMH_ades_obs[of R b s0 c "{y}"]
    by (simp only: Healthy_if[OF A_is_PBMH_ades[OF assms(1)]]; blast)
  show ?thesis
    using a2[of X] up assms(3) by blast
qed

lemma ades_par_by_merge_d2ac_ac2p:
  fixes M :: "'s des_merge" and AM :: "'s ades_merge_rel"
  assumes ops: "P is A" "Q is A" "P is A2" "Q is A2"
    and merge: "M is HDm" "M is H3m"
    and lift: "AM = H3m (H1m (ABm (ac'_lift_merge M)))"
  shows "P \<parallel>\<^bsub>AM\<^esub> Q = d2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
proof -
  have h1: "P is H1" "Q is H1"
    using ops(1,2) by (simp_all add: A_healthy_components_iff)
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use ops(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  have H: "(ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) is \<^bold>H"
    by (rule H_par_by_merge[OF H_implies_H1[OF designs_H(1)] H_implies_H1[OF designs_H(2)] merge(1)])
  have ex_des: "(\<exists>p. F p) = (\<exists>b s. F \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr>)"
    for F :: "'s des_vars_ext \<Rightarrow> bool"
    by pred_auto
  have acP: "ac2p P (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) = P (ades_obs b s0 c {z})"
    and acQ: "ac2p Q (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) = Q (ades_obs b s0 c {z})"
    for b s0 c z
    by (simp_all add: ac2p_healthy_obs A_is_PBMH_ades ops(1,2))
  show ?thesis
  proof (rule ades_obs_ext)
    fix b s0 c Z
    show "(P \<parallel>\<^bsub>AM\<^esub> Q) (ades_obs b s0 c Z) =
        d2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) (ades_obs b s0 c Z)"
    proof (cases b)
      case False
      have p: "P (ades_obs False s0 c' X)" "Q (ades_obs False s0 c' X)" for c' X
        using h1 by (simp_all add: H1_healthy_obs_iff)
      have bF: "b = False"
        using False by simp
      show ?thesis
        unfolding bF
        apply (simp only: d2ac_healthy_obs[OF H] ades_par_by_merge_obs lift ac'_lift_merge_completion_obs simp_thms)
        using p by blast
    next
      case True
      define Ms where "Ms okL sL okR sR c' s' \<equiv> merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c', \<dots> = s'\<rparr>"
        for okL sL okR sR c' s'
      have rhs: "d2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) (ades_obs True s0 c Z) \<longleftrightarrow>
          (\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z) \<or>
          (\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z)"
        by (simp only: d2ac_healthy_obs[OF H] par_by_merge_eval ex_des acP acQ Ms_def simp_thms)
      have lhs: "(P \<parallel>\<^bsub>AM\<^esub> Q) (ades_obs True s0 c Z) \<longleftrightarrow>
          (\<exists>okL X okR Y. P (ades_obs True s0 okL X) \<and> Q (ades_obs True s0 okR Y) \<and>
            X \<noteq> {} \<and> Y \<noteq> {} \<and>
            ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s')))"
        proof -
          have witnesses: "(\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. F sL sR s') =
            (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'. F sL sR s')" for X Y and F :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
            by (blast intro: exI[where x=UNIV])
          show ?thesis
            by (simp only: ades_par_by_merge_obs lift ac'_lift_merge_completion_obs
                Ms_def simp_thms witnesses)
        qed
      have divM: "Ms okL sL okR sR False s' \<Longrightarrow> Ms okL sL okR sR False z" for okL sL okR sR s' z
        unfolding Ms_def by (rule H3m_diverge[OF merge(2)])
      have bT: "b = True"
        using True by simp
      show ?thesis
        unfolding bT lhs rhs
      proof (intro iffI)
        assume "\<exists>okL X okR Y. P (ades_obs True s0 okL X) \<and> Q (ades_obs True s0 okR Y) \<and>
            X \<noteq> {} \<and> Y \<noteq> {} \<and>
            ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s'))"
        then obtain okL X okR Y where
          p: "P (ades_obs True s0 okL X)" and q: "Q (ades_obs True s0 okR Y)"
          and ne: "X \<noteq> {}" "Y \<noteq> {}"
          and m: "(\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s')"
          by blast
        obtain sL where sL: "sL \<in> X" "P (ades_obs True s0 okL {sL})"
          using p A_A2_pick[OF ops(1,3) ne(1)] by blast
        obtain sR where sR: "sR \<in> Y" "Q (ades_obs True s0 okR {sR})"
          using q A_A2_pick[OF ops(2,4) ne(2)] by blast
        show "(\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z) \<or>
          (\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z)"
          using m sL sR divM by blast
      next
        assume "(\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z) \<or>
          (\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z)"
        then show "\<exists>okL X okR Y. P (ades_obs True s0 okL X) \<and> Q (ades_obs True s0 okR Y) \<and>
            X \<noteq> {} \<and> Y \<noteq> {} \<and>
            ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s'))"
        proof (elim disjE)
          assume "\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z"
          then obtain okL sL okR sR where "P (ades_obs True s0 okL {sL})"
              "Q (ades_obs True s0 okR {sR})" "Ms okL sL okR sR False undefined"
            by blast
          then show ?thesis
            by (intro exI[of _ okL] exI[of _ "{sL}"] exI[of _ okR] exI[of _ "{sR}"]) blast
        next
          assume "\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z"
          then obtain z okL sL okR sR where "z \<in> Z" "P (ades_obs True s0 okL {sL})"
              "Q (ades_obs True s0 okR {sR})" "Ms okL sL okR sR c z"
            by blast
          then show ?thesis
            by (intro exI[of _ okL] exI[of _ "{sL}"] exI[of _ okR] exI[of _ "{sR}"]) blast
        qed
      qed
    qed
  qed
qed

lemma ades_par_by_merge_ac2p:
  fixes M :: "'s des_merge" and AM :: "'s ades_merge_rel"
  assumes ops: "P is A" "Q is A" "P is A2" "Q is A2"
    and merge: "M is HDm" "M is H3m"
    and lift: "AM = H3m (H1m (ABm (ac'_lift_merge M)))"
  shows "ac2p (P \<parallel>\<^bsub>AM\<^esub> Q) = ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q"
proof -
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use ops(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    by (simp only: ades_par_by_merge_d2ac_ac2p[OF assms] ac2p_d2ac[OF H_par_by_merge[OF
        H_implies_H1[OF designs_H(1)] H_implies_H1[OF designs_H(2)] merge(1)], simplified comp_apply])
qed

end
