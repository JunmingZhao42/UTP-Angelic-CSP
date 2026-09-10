section \<open>Parallel with Full Angelic-Design Merges\<close>

theory utp_ades_parallel_generic
  imports utp_ades_parallel
begin

text \<open>
  A full merge relates the complete prior observation and both branch
  observations to the complete final observation. It can therefore constrain
  the final control flag and choice set directly. The state-level lifting
  remains an instance of this interface.
\<close>

abbreviation ades_par_full ::
  "'s angelic_design \<Rightarrow> 's ades_merge_rel \<Rightarrow>
   's angelic_design \<Rightarrow> 's angelic_design"
where "ades_par_full P M Q \<equiv> P \<parallel>\<^bsub>M\<^esub> Q"

lemma ades_par_full_eval:
  fixes P Q :: "'s angelic_design" and M :: "'s ades_merge_rel"
  shows "ades_par_full P M Q (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval M x p q out)"
  by (cases x; cases out;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

lemma ades_par_state_as_full:
  "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = ades_par_full P (merge_ades_up j) Q"
  by simp

text \<open>
  Symmetry and associativity are separate algebraic requirements on the merge,
  not consequences of design healthiness. MergeSym exchanges the branch
  results. MergeAssoc compares the two ways of merging three branch results,
  keeping the same prior observation at both merges. Unlike the library's
  homogeneous, rotation-based AssocMerge, it directly expresses reassociation
  on the distinct input and output alphabets of angelic designs and does not
  require symmetry.
\<close>

definition MergeSym :: "'s ades_merge_rel \<Rightarrow> bool" where
  "MergeSym M \<longleftrightarrow>
    (\<forall>x p q out. ades_merge_eval M x p q out = ades_merge_eval M x q p out)"

definition MergeAssoc :: "'s ades_merge_rel \<Rightarrow> bool" where
  "MergeAssoc M \<longleftrightarrow>
    (\<forall>x p q r out.
      (\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
      (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x p y out))"

lemma MergeSym_iff_swap:
  "MergeSym M \<longleftrightarrow> swap\<^sub>m ;; M = M"
  by (simp add: MergeSym_def fun_eq_iff; pred_auto; blast)

definition merge_slice ::
  "'s ades_merge_rel \<Rightarrow> 's achoices des_vars_ext \<Rightarrow>
   's achoices des_vars_ext \<Rightarrow> 's angelic_design"
where [pred]:
  "merge_slice M p q = (\<lambda>(x,out). ades_merge_eval M x p q out)"

lemma merge_slice_eval [simp]:
  "merge_slice M p q (x,out) = ades_merge_eval M x p q out"
  by (simp add: merge_slice_def)

lemma merge_slice_ext:
  fixes M N :: "'s ades_merge_rel"
  assumes "\<And>p q. merge_slice M p q = merge_slice N p q"
  shows "M = N"
  using assms
  by (simp add: merge_slice_def fun_eq_iff; pred_auto)

lemma MergeSym_iff_slices:
  "MergeSym M \<longleftrightarrow> (\<forall>p q. merge_slice M p q = merge_slice M q p)"
  by (auto simp: MergeSym_def merge_slice_def fun_eq_iff split: prod.splits)

lemma merge_slice_refine:
  assumes "M \<sqsubseteq> N"
  shows "merge_slice M p q \<sqsubseteq> merge_slice N p q"
  using assms by (auto simp: merge_slice_def pred_refine_iff)

lemma merge_slice_refineI:
  fixes M N :: "'s ades_merge_rel"
  assumes "\<And>p q. merge_slice M p q \<sqsubseteq> merge_slice N p q"
  shows "M \<sqsubseteq> N"
  using assms
  by (simp add: merge_slice_def pred_refine_iff; pred_auto)

definition merge_health ::
  "('s angelic_design \<Rightarrow> 's angelic_design) \<Rightarrow>
   's ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]:
  "merge_health H M = (\<lambda>(m,out).
    H (merge_slice M (mrg_left\<^sub>v m) (mrg_right\<^sub>v m))
      (mrg_prior\<^sub>v m,out))"

lemma merge_health_slice [simp]:
  "merge_slice (merge_health H M) p q = H (merge_slice M p q)"
  by (simp add: merge_health_def merge_slice_def fun_eq_iff)

lemma merge_health_eval:
  "ades_merge_eval (merge_health H M) x p q out =
    H (merge_slice M p q) (x,out)"
  by (simp add: merge_health_def)

lemma merge_health_idem:
  assumes "Idempotent H"
  shows "merge_health H (merge_health H M) = merge_health H M"
proof -
  have idem: "H (H P) = H P" for P
    using assms by (simp add: Idempotent_def)
  show ?thesis by (rule merge_slice_ext; simp add: idem)
qed

lemma merge_health_Idempotent [closure]:
  "Idempotent H \<Longrightarrow> Idempotent (merge_health H)"
  by (rule IdempotentI, rule merge_health_idem, assumption)

lemma merge_health_mono:
  assumes "Monotonic H" "M \<sqsubseteq> N"
  shows "merge_health H M \<sqsubseteq> merge_health H N"
proof (rule merge_slice_refineI)
  fix p q
  have "H (merge_slice M p q) \<sqsubseteq> H (merge_slice N p q)"
    using assms(1) merge_slice_refine[OF assms(2), of p q]
    by (auto simp: Monotonic_refine)
  then show "merge_slice (merge_health H M) p q \<sqsubseteq>
    merge_slice (merge_health H N) p q" by simp
qed

lemma merge_health_Monotonic [closure]:
  "Monotonic H \<Longrightarrow> Monotonic (merge_health H)"
  by (rule MonotonicI, rule merge_health_mono, assumption, assumption)

lemma merge_health_healthy_iff:
  "M is merge_health H \<longleftrightarrow> (\<forall>p q. merge_slice M p q is H)"
  unfolding Healthy_def
  by (auto intro: merge_slice_ext dest: arg_cong[where f="\<lambda>M. merge_slice M _ _"])

lemma merge_health_MergeSym:
  assumes "MergeSym M"
  shows "MergeSym (merge_health H M)"
  using assms by (simp add: MergeSym_iff_slices)

lemma merge_health_comp:
  "merge_health (H \<circ> K) M = merge_health H (merge_health K M)"
  by (rule merge_slice_ext; simp)

lemma merge_health_preserves:
  assumes "\<And>P. P is H \<Longrightarrow> K P is H"
    and "M is merge_health H"
  shows "merge_health K M is merge_health H"
  using assms by (auto simp: merge_health_healthy_iff)

subsection \<open>Observation Calculus\<close>

abbreviation ades_obs ::
  "bool \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> 's set \<Rightarrow>
   's astate des_vars_ext \<times> 's achoices des_vars_ext"
where
  "ades_obs b s0 c X \<equiv>
   (\<lparr>ok\<^sub>v = b, s\<^sub>v = s0, \<dots> = ()\<rparr>,
    \<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr>)"

lemma ades_obs_ext:
  fixes P Q :: "'s angelic_design"
  assumes "\<And>b s0 c X. P (ades_obs b s0 c X) = Q (ades_obs b s0 c X)"
  shows "P = Q"
  using assms by (simp add: fun_eq_iff; pred_auto)

lemma H1_obs:
  "H1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not> b \<or> P (ades_obs b s0 c X))"
  by (simp add: H1_def; pred_auto)

lemma H2_obs:
  "H2 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 False X) \<or> (c \<and> P (ades_obs b s0 True X)))"
  by (simp add: H2_split; pred_auto)

lemma A0_obs:
  "A0 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c X) \<and>
      (b \<and> c \<and> X = {} \<longrightarrow> P (ades_obs b s0 False X)))"
  by (simp add: A0_def; pred_auto)

lemma PBMH_ades_obs:
  "PBMH_ades P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<exists>Y \<subseteq> X. P (ades_obs b s0 c Y))"
  by (simp add: PBMH_ades_eval; blast)

lemma A2_obs:
  "A2 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c {}) \<or>
     (\<exists>z\<in>X. P (ades_obs b s0 c {z})))"
  by (simp add: A2_def)

lemma H1_healthy_obs_iff:
  fixes P :: "'s angelic_design"
  shows "P is H1 \<longleftrightarrow> (\<forall>s0 c X. P (ades_obs False s0 c X))"
proof
  assume h: "P is H1"
  show "\<forall>s0 c X. P (ades_obs False s0 c X)"
    using H1_obs[of P False] by (simp only: Healthy_if[OF h]; simp)
next
  assume h: "\<forall>s0 c X. P (ades_obs False s0 c X)"
  show "P is H1"
  proof (rule Healthy_intro, rule ades_obs_ext)
    fix b s0 c X
    show "H1 P (ades_obs b s0 c X) = P (ades_obs b s0 c X)"
      using h by (cases b; auto simp: H1_obs)
  qed
qed

lemma A0_healthy_obs_iff:
  fixes P :: "'s angelic_design"
  shows "P is A0 \<longleftrightarrow>
    (\<forall>s0. P (ades_obs True s0 True {}) \<longrightarrow>
      P (ades_obs True s0 False {}))"
proof
  assume h: "P is A0"
  show "\<forall>s0. P (ades_obs True s0 True {}) \<longrightarrow>
    P (ades_obs True s0 False {})"
    using A0_obs[of P True _ True "{}"] h
    by (simp only: Healthy_if; blast)
next
  assume h: "\<forall>s0. P (ades_obs True s0 True {}) \<longrightarrow>
    P (ades_obs True s0 False {})"
  show "P is A0"
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: A0_obs; insert h; auto)
qed

subsection \<open>Merge Healthiness Operators\<close>

text \<open>
  Weakest-for-closure claims depend on the permitted operands: a merge
  condition is weakest when it holds exactly for the merges that preserve
  the target healthiness for every permitted pair of operands. Idempotence,
  monotonicity, and the slice fixed-point equivalences alone do not show this.

  For arbitrary operands, constant branch selectors P(x,p) = (p = p0) and
  Q(x,q) = (q = q0) recover any chosen merge slice. Universal closure therefore
  forces every slice to be healthy. Together with the closure lemmas below,
  this shows that PBMHM, H2M, A0M, and A2M are weakest for their respective
  targets with arbitrary operands. The necessity arguments and counterexamples
  in these comments are mathematical explanations, not additional Isabelle
  necessity or counterexample lemmas. See also docs/GENERIC_PARALLEL.md.
\<close>

text \<open>
  PBMHM is weakest for PBMH_ades closure with arbitrary operands, by the
  selector argument above. This does not assert weakestness when the operands
  are restricted to an already healthy layer.
\<close>

definition PBMHM :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]: "PBMHM = merge_health PBMH_ades"

lemma PBMHM_idem: "PBMHM (PBMHM M) = PBMHM M"
  by (simp only: PBMHM_def; rule merge_health_idem;
      rule PBMH_ades_Idempotent)

lemma PBMHM_Idempotent [closure]: "Idempotent PBMHM"
  by (simp add: Idempotent_def PBMHM_idem)

lemma PBMHM_mono: "M \<sqsubseteq> N \<Longrightarrow> PBMHM M \<sqsubseteq> PBMHM N"
  by (simp only: PBMHM_def; rule merge_health_mono;
      simp add: PBMH_ades_Monotonic)

lemma PBMHM_Monotonic [closure]: "Monotonic PBMHM"
  by (rule MonotonicI, rule PBMHM_mono)

lemma PBMHM_healthy [closure]: "PBMHM M is PBMHM"
  by (rule Healthy_Idempotent[OF PBMHM_Idempotent])

lemma PBMHM_healthy_iff:
  "M is PBMHM \<longleftrightarrow> (\<forall>p q. merge_slice M p q is PBMH_ades)"
  by (simp only: PBMHM_def merge_health_healthy_iff)

text \<open>
  H1M is sufficient but not weakest for H1 closure with H1-healthy operands.
  At an unstarted input, those operands accept every branch result, so closure
  needs some pair p,q for each final output o. H1M instead requires every pair
  p,q to permit o. For example, M(x,p,q,o) = (not ok(x) and p = o and q = o)
  yields the H1-healthy parallel predicate not ok(x), but fails H1M.
\<close>

definition H1M :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]: "H1M = merge_health H1"

lemma H1M_idem: "H1M (H1M M) = H1M M"
  by (simp only: H1M_def; rule merge_health_idem;
      simp add: Idempotent_def H1_idem)

lemma H1M_Idempotent [closure]: "Idempotent H1M"
  by (simp add: Idempotent_def H1M_idem)

lemma H1M_mono: "M \<sqsubseteq> N \<Longrightarrow> H1M M \<sqsubseteq> H1M N"
  by (simp only: H1M_def; rule merge_health_mono;
      simp add: Continuous_Monotonic[OF H1_Continuous])

lemma H1M_Monotonic [closure]: "Monotonic H1M"
  by (rule MonotonicI, rule H1M_mono)

lemma H1M_healthy [closure]: "H1M M is H1M"
  by (rule Healthy_Idempotent[OF H1M_Idempotent])

lemma H1M_healthy_iff:
  "M is H1M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is H1)"
  by (simp only: H1M_def merge_health_healthy_iff)

text \<open>
  H2M is weakest for H2 closure with arbitrary operands: the closure lemma
  gives sufficiency and constant branch selectors give necessity.
\<close>

definition H2M :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]: "H2M = merge_health H2"

lemma H2M_idem: "H2M (H2M M) = H2M M"
  by (simp only: H2M_def; rule merge_health_idem;
      simp add: Idempotent_def H2_idem)

lemma H2M_Idempotent [closure]: "Idempotent H2M"
  by (simp add: Idempotent_def H2M_idem)

lemma H2M_mono: "M \<sqsubseteq> N \<Longrightarrow> H2M M \<sqsubseteq> H2M N"
  by (simp only: H2M_def; rule merge_health_mono;
      simp add: Continuous_Monotonic[OF H2_Continuous])

lemma H2M_Monotonic [closure]: "Monotonic H2M"
  by (rule MonotonicI, rule H2M_mono)

lemma H2M_healthy [closure]: "H2M M is H2M"
  by (rule Healthy_Idempotent[OF H2M_Idempotent])

lemma H2M_healthy_iff:
  "M is H2M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is H2)"
  by (simp only: H2M_def merge_health_healthy_iff)

text \<open>
  A0M is weakest for A0 closure with arbitrary operands, by the same selector
  argument. It constrains full observation slices; it is distinct from the
  state-merge totality predicate A0j and the earlier skip-adding operator H0.
\<close>

definition A0M :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]: "A0M = merge_health A0"

lemma A0M_idem: "A0M (A0M M) = A0M M"
  by (simp only: A0M_def; rule merge_health_idem;
      rule A0_Idempotent)

lemma A0M_Idempotent [closure]: "Idempotent A0M"
  by (simp add: Idempotent_def A0M_idem)

lemma A0M_mono: "M \<sqsubseteq> N \<Longrightarrow> A0M M \<sqsubseteq> A0M N"
  by (simp only: A0M_def; rule merge_health_mono;
      simp add: A0_Monotonic)

lemma A0M_Monotonic [closure]: "Monotonic A0M"
  by (rule MonotonicI, rule A0M_mono)

lemma A0M_healthy [closure]: "A0M M is A0M"
  by (rule Healthy_Idempotent[OF A0M_Idempotent])

lemma A0M_healthy_iff:
  "M is A0M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is A0)"
  by (simp only: A0M_def merge_health_healthy_iff)

text \<open>
  A1M supplies the slice lifting and its healthiness algebra. No separate
  parallel closure or weakest-for-closure characterisation is claimed for
  A1M here.
\<close>

definition A1M :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]: "A1M = merge_health A1"

lemma A1M_idem: "A1M (A1M M) = A1M M"
  by (simp only: A1M_def; rule merge_health_idem;
      rule A1_Idempotent)

lemma A1M_Idempotent [closure]: "Idempotent A1M"
  by (simp add: Idempotent_def A1M_idem)

lemma A1M_mono: "M \<sqsubseteq> N \<Longrightarrow> A1M M \<sqsubseteq> A1M N"
  by (simp only: A1M_def; rule merge_health_mono;
      simp add: A1_Monotonic)

lemma A1M_Monotonic [closure]: "Monotonic A1M"
  by (rule MonotonicI, rule A1M_mono)

lemma A1M_healthy [closure]: "A1M M is A1M"
  by (rule Healthy_Idempotent[OF A1M_Idempotent])

lemma A1M_healthy_iff:
  "M is A1M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is A1)"
  by (simp only: A1M_def merge_health_healthy_iff)

text \<open>
  A2M is weakest for A2 closure with arbitrary operands, by the closure lemma
  and the selector argument. This statement applies to the full merge
  interface and does not assert necessity of the earlier state condition A2j.
\<close>

definition A2M :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]: "A2M = merge_health A2"

lemma A2M_idem: "A2M (A2M M) = A2M M"
  by (simp only: A2M_def; rule merge_health_idem;
      rule A2_Idempotent)

lemma A2M_Idempotent [closure]: "Idempotent A2M"
  by (simp add: Idempotent_def A2M_idem)

lemma A2M_mono: "M \<sqsubseteq> N \<Longrightarrow> A2M M \<sqsubseteq> A2M N"
  by (simp only: A2M_def; rule merge_health_mono;
      simp add: A2_Monotonic)

lemma A2M_Monotonic [closure]: "Monotonic A2M"
  by (rule MonotonicI, rule A2M_mono)

lemma A2M_healthy [closure]: "A2M M is A2M"
  by (rule Healthy_Idempotent[OF A2M_Idempotent])

lemma A2M_healthy_iff:
  "M is A2M \<longleftrightarrow> (\<forall>p q. merge_slice M p q is A2)"
  by (simp only: A2M_def merge_health_healthy_iff)

text \<open>
  ADM is sufficient but not weakest for A closure with H1-healthy operands
  (also when both operands are A-healthy). The example given for H1M yields
  not ok(x), which is A-healthy, but fails H1M and hence ADM. The component
  equivalence below characterises this chosen class of merges, rather than
  every merge that preserves A.
\<close>

definition ADM :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where [pred]: "ADM = merge_health A"

lemma ADM_idem: "ADM (ADM M) = ADM M"
  by (simp only: ADM_def; rule merge_health_idem;
      rule A_Idempotent)

lemma ADM_Idempotent [closure]: "Idempotent ADM"
  by (simp add: Idempotent_def ADM_idem)

lemma ADM_mono: "M \<sqsubseteq> N \<Longrightarrow> ADM M \<sqsubseteq> ADM N"
  by (simp only: ADM_def; rule merge_health_mono;
      simp add: A_Monotonic)

lemma ADM_Monotonic [closure]: "Monotonic ADM"
  by (rule MonotonicI, rule ADM_mono)

lemma ADM_healthy [closure]: "ADM M is ADM"
  by (rule Healthy_Idempotent[OF ADM_Idempotent])

lemma ADM_healthy_iff:
  "M is ADM \<longleftrightarrow> (\<forall>p q. merge_slice M p q is A)"
  by (simp only: ADM_def merge_health_healthy_iff)

subsection \<open>Combined Design Healthiness\<close>

lemma A_healthy_components_iff:
  fixes P :: "'s angelic_design"
  shows "P is A \<longleftrightarrow>
    ((P is H1) \<and> (P is H2) \<and> (P is PBMH_ades) \<and> (P is A0))"
proof
  assume h: "P is A"
  have h1: "P is H1"
    using A_is_H1[of P] by (simp only: Healthy_if[OF h] Healthy_def')
  have h2: "P is H2"
    using A_is_H2[of P] by (simp only: Healthy_if[OF h] Healthy_def')
  have a0: "P is A0"
  proof -
    have "A P is A0" by (simp add: Healthy_def A_def A0_idem)
    then show ?thesis by (simp only: Healthy_if[OF h])
  qed
  show "(P is H1) \<and> (P is H2) \<and> (P is PBMH_ades) \<and> (P is A0)"
    using h1 h2 A_is_PBMH_ades[OF h] a0 by blast
next
  assume h: "(P is H1) \<and> (P is H2) \<and> (P is PBMH_ades) \<and> (P is A0)"
  have hh: "P is \<^bold>H"
    using h by (simp add: Healthy_def H1_H2_comp)
  show "P is A"
    using h by (simp add: Healthy_def A_def A1_eq_PBMH_ades[OF hh])
qed

lemma ADM_components_iff:
  "M is ADM \<longleftrightarrow>
    ((M is H1M) \<and> (M is H2M) \<and> (M is PBMHM) \<and> (M is A0M))"
  by (auto simp: ADM_healthy_iff H1M_healthy_iff H2M_healthy_iff
      PBMHM_healthy_iff A0M_healthy_iff A_healthy_components_iff)

lemma ADM_intro:
  assumes "M is H1M" "M is H2M" "M is PBMHM" "M is A0M"
  shows "M is ADM"
  using assms by (simp add: ADM_components_iff)

subsection \<open>Healthiness Closure of Generic Parallel\<close>

lemma ades_par_full_PBMH_distrib:
  "PBMH_ades (ades_par_full P M Q) = ades_par_full P (PBMHM M) Q"
  by (rule ades_obs_ext;
      simp only: PBMH_ades_obs ades_par_full_eval PBMHM_def
        merge_health_eval merge_slice_eval; blast)

lemma ades_par_full_H2_distrib:
  "H2 (ades_par_full P M Q) = ades_par_full P (H2M M) Q"
  by (rule ades_obs_ext;
      simp only: H2_obs ades_par_full_eval H2M_def
        merge_health_eval merge_slice_eval; blast)

lemma ades_par_full_A2_distrib:
  "A2 (ades_par_full P M Q) = ades_par_full P (A2M M) Q"
  by (rule ades_obs_ext;
      simp only: A2_obs ades_par_full_eval A2M_def
        merge_health_eval merge_slice_eval; blast)

lemma ades_par_full_PBMH_closure [closure]:
  assumes "M is PBMHM"
  shows "ades_par_full P M Q is PBMH_ades"
  by (simp only: Healthy_def' ades_par_full_PBMH_distrib Healthy_if[OF assms])

lemma ades_par_full_H2_closure [closure]:
  assumes "M is H2M"
  shows "ades_par_full P M Q is H2"
  by (simp only: Healthy_def' ades_par_full_H2_distrib Healthy_if[OF assms])

lemma ades_par_full_A2_closure [closure]:
  assumes "M is A2M"
  shows "ades_par_full P M Q is A2"
  by (simp only: Healthy_def' ades_par_full_A2_distrib Healthy_if[OF assms])

lemma ades_par_full_A0_closure [closure]:
  fixes P Q :: "'s angelic_design" and M :: "'s ades_merge_rel"
  assumes "M is A0M"
  shows "ades_par_full P M Q is A0"
proof (unfold A0_healthy_obs_iff, intro allI impI)
  fix s0 :: 's
  assume running: "ades_par_full P M Q (ades_obs True s0 True {})"
  obtain p q where branches:
      "P (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,p)"
      "Q (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,q)"
    and success: "merge_slice M p q (ades_obs True s0 True {})"
    using running by (auto simp: ades_par_full_eval)
  have slice: "merge_slice M p q is A0"
    using assms by (simp add: A0M_healthy_iff)
  have failure: "merge_slice M p q (ades_obs True s0 False {})"
    using slice success by (auto simp: A0_healthy_obs_iff)
  show "ades_par_full P M Q (ades_obs True s0 False {})"
    using branches failure by (auto simp: ades_par_full_eval)
qed

lemma ades_par_full_H1_closure [closure]:
  fixes P Q :: "'s angelic_design" and M :: "'s ades_merge_rel"
  assumes "P is H1" "Q is H1" "M is H1M"
  shows "ades_par_full P M Q is H1"
proof (unfold H1_healthy_obs_iff, intro allI)
  fix s0 :: 's and c :: bool and X :: "'s set"
  let ?x = "\<lparr>ok\<^sub>v = False, s\<^sub>v = s0, \<dots> = ()\<rparr>"
  let ?out = "\<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr>"
  have p: "P (?x,?out)" and q: "Q (?x,?out)"
    using assms(1,2) by (simp_all add: H1_healthy_obs_iff)
  have slice: "merge_slice M ?out ?out is H1"
    using assms(3) by (simp add: H1M_healthy_iff)
  have m: "merge_slice M ?out ?out (?x,?out)"
    using slice by (simp add: H1_healthy_obs_iff)
  show "ades_par_full P M Q (ades_obs False s0 c X)"
    using p q m by (auto simp: ades_par_full_eval)
qed

lemma ades_par_full_A_closure [closure]:
  assumes "P is H1" "Q is H1" "M is ADM"
  shows "ades_par_full P M Q is A"
proof -
  have parts: "M is H1M" "M is H2M" "M is PBMHM" "M is A0M"
    using assms(3) by (simp_all add: ADM_components_iff)
  show ?thesis
    using ades_par_full_H1_closure[OF assms(1,2) parts(1)]
      ades_par_full_H2_closure[OF parts(2), of P Q]
      ades_par_full_PBMH_closure[OF parts(3), of P Q]
      ades_par_full_A0_closure[OF parts(4), of P Q]
    by (simp add: A_healthy_components_iff)
qed

lemma ades_par_full_ADM_image [closure]:
  assumes "P is H1" "Q is H1"
  shows "ades_par_full P (ADM M) Q is A"
  by (rule ades_par_full_A_closure[OF assms ADM_healthy])

subsection \<open>Algebraic Laws\<close>

text \<open>
  These laws concern full predicates; no operand healthiness is needed.
  Disjunction (demonic choice) distributes through parallel, and false is
  an annihilator. For healthy operands and a healthy merge, the closure
  theorems above establish that the resulting expressions stay in the layer.
\<close>

lemma ades_par_full_mono:
  fixes P1 P2 Q1 Q2 :: "'s angelic_design" and M1 M2 :: "'s ades_merge_rel"
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2" "M1 \<sqsubseteq> M2"
  shows "ades_par_full P1 M1 Q1 \<sqsubseteq> ades_par_full P2 M2 Q2"
  using assms
  by (auto simp: pred_refine_iff ades_par_full_eval split: prod.splits; blast)

lemma ades_par_full_comm:
  assumes "MergeSym M"
  shows "ades_par_full P M Q = ades_par_full Q M P"
  by (rule par_by_merge_comm; use assms in \<open>simp add: MergeSym_iff_swap\<close>)

lemma ades_par_full_comm_iff:
  "MergeSym M \<longleftrightarrow> (\<forall>P Q. ades_par_full P M Q = ades_par_full Q M P)"
proof
  assume "MergeSym M"
  then show "\<forall>P Q. ades_par_full P M Q = ades_par_full Q M P"
    by (blast intro: ades_par_full_comm)
next
  assume comm: "\<forall>P Q. ades_par_full P M Q = ades_par_full Q M P"
  show "MergeSym M"
  proof (unfold MergeSym_def, intro allI)
    fix x p q out
    have eq: "ades_par_full (\<lambda>(x,r). r = p) M (\<lambda>(x,r). r = q) =
        ades_par_full (\<lambda>(x,r). r = q) M (\<lambda>(x,r). r = p)"
      using comm by blast
    from fun_cong[OF eq, of "(x,out)"]
    show "ades_merge_eval M x p q out = ades_merge_eval M x q p out"
      by (simp add: ades_par_full_eval)
  qed
qed

lemma ades_par_full_assoc:
  assumes "MergeAssoc M"
  shows "ades_par_full (ades_par_full P M Q) M R =
    ades_par_full P M (ades_par_full Q M R)"
proof (rule ext, clarify)
  fix x out
  have assoc: "(\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
      (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x p y out)"
    for p q r
    using assms by (simp add: MergeAssoc_def)
  show "ades_par_full (ades_par_full P M Q) M R (x,out) =
      ades_par_full P M (ades_par_full Q M R) (x,out)"
    unfolding ades_par_full_eval using assoc by blast
qed

lemma ades_par_full_assoc_iff:
  "MergeAssoc M \<longleftrightarrow>
    (\<forall>P Q R. ades_par_full (ades_par_full P M Q) M R =
      ades_par_full P M (ades_par_full Q M R))"
proof
  assume "MergeAssoc M"
  then show "\<forall>P Q R. ades_par_full (ades_par_full P M Q) M R =
      ades_par_full P M (ades_par_full Q M R)"
    by (blast intro: ades_par_full_assoc)
next
  assume assoc: "\<forall>P Q R. ades_par_full (ades_par_full P M Q) M R =
      ades_par_full P M (ades_par_full Q M R)"
  show "MergeAssoc M"
  proof (unfold MergeAssoc_def, intro allI)
    fix x p q r out
    have eq: "ades_par_full
        (ades_par_full (\<lambda>(x,u). u = p) M (\<lambda>(x,u). u = q)) M
        (\<lambda>(x,u). u = r) =
      ades_par_full (\<lambda>(x,u). u = p) M
        (ades_par_full (\<lambda>(x,u). u = q) M (\<lambda>(x,u). u = r))"
      using assoc by blast
    from fun_cong[OF eq, of "(x,out)"]
    show "(\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
        (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x p y out)"
      by (simp add: ades_par_full_eval)
  qed
qed

lemma ades_par_full_disj_left:
  "ades_par_full (P \<or> Q) M R = (ades_par_full P M R \<or> ades_par_full Q M R)"
  by (auto simp: fun_eq_iff ades_par_full_eval disj_pred_def split: prod.splits)

lemma ades_par_full_disj_right:
  "ades_par_full P M (Q \<or> R) = (ades_par_full P M Q \<or> ades_par_full P M R)"
  by (auto simp: fun_eq_iff ades_par_full_eval disj_pred_def split: prod.splits)

lemma ades_par_full_disj_merge:
  "ades_par_full P (M \<or> N) Q = (ades_par_full P M Q \<or> ades_par_full P N Q)"
  by (auto simp: fun_eq_iff ades_par_full_eval disj_pred_def split: prod.splits)

lemma ades_par_full_false_left [simp]: "ades_par_full false M P = false"
  by (rule par_by_merge_left_false)

lemma ades_par_full_false_right [simp]: "ades_par_full P M false = false"
  by (rule par_by_merge_right_false)

lemma ades_par_full_false_merge [simp]: "ades_par_full P false Q = false"
  by (rule par_by_merge_false)

text \<open>
  Every slice healthiness operator preserves merge symmetry. In particular,
  a symmetric seed can be repaired by ADM without losing commutativity.
  No analogous preservation of MergeAssoc is claimed.
\<close>

lemma ADM_MergeSym:
  "MergeSym M \<Longrightarrow> MergeSym (ADM M)"
  by (simp only: ADM_def; rule merge_health_MergeSym)

lemma ades_par_full_ADM_comm:
  "MergeSym M \<Longrightarrow> ades_par_full P (ADM M) Q = ades_par_full Q (ADM M) P"
  by (rule ades_par_full_comm, rule ADM_MergeSym)

end
