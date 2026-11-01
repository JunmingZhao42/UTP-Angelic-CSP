section \<open>Angelic Parallel and Ordinary Designs\<close>

theory utp_ades_parallel
  imports utp_ades_designs
begin

text \<open>An AD merge relates the prior observation and the two branch outputs to a merge
  output. The theory first states conditions on an arbitrary merge under which parallel
  by merge preserves AD healthiness. It then lifts a state merge to a merge that meets
  all of them, defines AD parallel, and proves its laws.\<close>

subsection \<open>Merge Observations and Slices\<close>

type_synonym 's ades_mrg =
  "('s astate des_vars_ext, 's achoices des_vars_ext, 's achoices des_vars_ext) mrg"

type_synonym 's ades_merge_rel = "('s ades_mrg, 's achoices des_vars_ext) urel"

abbreviation ades_merge_eval ::
  "'s ades_merge_rel \<Rightarrow> 's astate des_vars_ext \<Rightarrow>
   's achoices des_vars_ext \<Rightarrow> 's achoices des_vars_ext \<Rightarrow>
   's achoices des_vars_ext \<Rightarrow> bool"
where
"ades_merge_eval M obs0 obsL obsR obsOut \<equiv>
  M ((\<lparr>mrg_prior\<^sub>v = obs0, mrg_left\<^sub>v = obsL, mrg_right\<^sub>v = obsR, \<dots> = ()\<rparr>
      :: 's ades_mrg), obsOut)"

abbreviation ades_merge_obs where
  "ades_merge_obs M ok0 s0 okL SL okR SR okOut SOut \<equiv>
    (\<lambda>(obs0,obsOut). ades_merge_eval M obs0 (ades_output okL SL) (ades_output okR SR) obsOut)
      (ades_obs ok0 s0 okOut SOut)"

lemma ades_par_by_merge_eval:
  "(P \<parallel>\<^bsub>M\<^esub> Q) (obs0,obsOut) \<longleftrightarrow>
    (\<exists>obsL obsR. P (obs0,obsL) \<and> Q (obs0,obsR) \<and> ades_merge_eval M obs0 obsL obsR obsOut)"
  by (cases obs0; cases obsOut;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

text \<open>A slice fixes both branch outputs of a merge. It relates the prior to the merge
  output, so it is an AD relation and AD healthiness conditions apply to it.\<close>

definition merge_slice ::
  "'s ades_merge_rel \<Rightarrow> 's achoices des_vars_ext \<Rightarrow> 's achoices des_vars_ext \<Rightarrow>
   's angelic_design" where
  "merge_slice M l r \<equiv> (\<lambda>(x,z). ades_merge_eval M x l r z)"

lemma merge_slice_ext:
  assumes "\<And>l r. merge_slice M l r = merge_slice N l r"
  shows "M = N"
  using assms by (auto simp: merge_slice_def fun_eq_iff; metis (full_types) mrg.cases)

lemma merge_slice_obs:
  "merge_slice M (ades_output a L) (ades_output d R) (ades_obs b s0 c Z) =
    ades_merge_obs M b s0 a L d R c Z"
  by (simp add: merge_slice_def)

lemma ades_par_by_merge_slices:
  "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z) \<longleftrightarrow>
    (\<exists>a L d R. P (ades_obs b s0 a L) \<and> Q (ades_obs b s0 d R) \<and>
      merge_slice M (ades_output a L) (ades_output d R) (ades_obs b s0 c Z))"
  by (simp add: ades_par_by_merge_eval choices_ex merge_slice_def)

text \<open>@{text "merge_health H"} applies @{text H} to every slice of a merge.\<close>

definition merge_health ::
  "('s angelic_design \<Rightarrow> 's angelic_design) \<Rightarrow> 's ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "merge_health H M \<equiv> (\<lambda>(m,z).
  H (merge_slice M (mrg_left\<^sub>v m) (mrg_right\<^sub>v m)) (mrg_prior\<^sub>v m, z))"

lemma slice_merge_health:
  "merge_slice (merge_health H M) l r = H (merge_slice M l r)"
  by (auto simp: merge_slice_def merge_health_def fun_eq_iff)

subsection \<open>Merge Healthiness\<close>

text \<open>Naming rule: @{text Xm} is the merge condition under which parallel by merge
  preserves @{text X}. The design conditions @{const H1m}, @{const H2m}, @{const H3m} and
  @{const HDM} come from the design parallel theory, which allows the alphabets of a merge
  to differ. The angelic conditions are @{text Am} and @{text A2m}. There is no
  @{text A3m}: A3 closure follows from @{const H1m} and @{const H3m}.\<close>

subsubsection \<open>Design Conditions\<close>

text \<open>On AD merges, the design conditions apply H1, H2, H3 and H1 \<circ> H2 to every slice.\<close>
lemma H1m_merge_health:
  fixes M :: "'s ades_merge_rel"
  shows "H1m M = merge_health H1 M"
proof (rule merge_slice_ext)
  fix l r
  show "merge_slice (H1m M) l r = merge_slice (merge_health H1 M) l r"
    unfolding slice_merge_health
    by (simp add: merge_slice_def H1m_def H1_def fun_eq_iff; pred_auto)
qed

lemma H2m_merge_health:
  fixes M :: "'s ades_merge_rel"
  shows "H2m M = merge_health H2 M"
proof (rule merge_slice_ext)
  fix l r
  show "merge_slice (H2m M) l r = merge_slice (merge_health H2 M) l r"
    unfolding slice_merge_health
    by (simp add: merge_slice_def H2m_def H2_def fun_eq_iff; pred_auto)
qed

lemma H3m_merge_health:
  fixes M :: "'s ades_merge_rel"
  shows "H3m M = merge_health H3 M"
proof (rule merge_slice_ext)
  fix l r
  show "merge_slice (H3m M) l r = merge_slice (merge_health H3 M) l r"
    unfolding slice_merge_health
    by (simp add: merge_slice_def H3m_def H3_def fun_eq_iff; pred_auto)
qed

lemma HDM_merge_health:
  fixes M :: "'s ades_merge_rel"
  shows "HDM M = merge_health \<^bold>H M"
proof (rule merge_slice_ext)
  fix l r
  show "merge_slice (HDM M) l r = merge_slice (merge_health \<^bold>H M) l r"
    by (simp add: HDM_def H1m_merge_health H2m_merge_health slice_merge_health H1_H2_comp)
qed

subsubsection \<open>Am\<close>

text \<open>@{text Am} applies the three clauses of A to the merge output: the merge is
  unstarted, or it may diverge with a subset of the output set, or it may terminate with
  a subset of a nonempty output set. For each started prior and branch pair, the accepted
  output choice sets are therefore upward closed, and the merge terminates with the empty
  set only where it may also diverge with it.\<close>

definition Am :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "Am M \<equiv> (\<lambda>(m,z).
     let Z = achoices.ac\<^sub>v (des_vars.more z)
     in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
        (\<exists>Y\<subseteq>Z. M (m, ades_output False Y)) \<or>
        (des_vars.ok\<^sub>v z \<and> Z \<noteq> {} \<and> (\<exists>Y\<subseteq>Z. M (m, ades_output True Y))))"

text \<open>Equivalently, @{const Am} applies A to every slice.\<close>

lemma Am_merge_health: "Am M = merge_health A M"
proof (rule merge_slice_ext)
  fix l r
  show "merge_slice (Am M) l r = merge_slice (merge_health A M) l r"
  proof (rule ades_obs_ext)
    fix b s0 c X
    have "merge_slice (merge_health A M) l r (ades_obs b s0 c X) =
      A (merge_slice M l r) (ades_obs b s0 c X)"
      by (simp only: slice_merge_health)
    also have "... = merge_slice (Am M) l r (ades_obs b s0 c X)"
      by (cases b; simp add: A_obs merge_slice_def Am_def Let_def)
    finally show "merge_slice (Am M) l r (ades_obs b s0 c X) =
      merge_slice (merge_health A M) l r (ades_obs b s0 c X)"
      by (rule sym)
  qed
qed

lemma Am_slices: "M is Am \<longleftrightarrow> (\<forall>l r. merge_slice M l r is A)"
  unfolding Healthy_def' Am_merge_health
  by (metis slice_merge_health merge_slice_ext)

lemma Am_idem: "Am (Am M) = Am M"
  by (rule merge_slice_ext; simp add: Am_merge_health slice_merge_health A_idem)

lemma Am_mono:
  assumes "M \<sqsubseteq> N"
  shows "Am M \<sqsubseteq> Am N"
proof -
  have "merge_slice M l r \<sqsubseteq> merge_slice N l r" for l r
    using assms by (auto simp: pred_refine_iff merge_slice_def)
  then have "A (merge_slice M l r) \<sqsubseteq> A (merge_slice N l r)" for l r
    by (rule A_mono)
  then show ?thesis
    unfolding Am_merge_health merge_health_def pred_refine_iff by auto
qed

lemma Am_Idempotent [closure]: "Idempotent Am"
  by (simp add: Idempotent_def Am_idem)

lemma Am_Monotonic [closure]: "Monotonic Am"
  by (rule MonotonicI, rule Am_mono)

subsubsection \<open>A2m\<close>

text \<open>@{text A2m} has two parts. @{text A2m_atoms} makes every slice whose branch choice
  sets are singletons A2. @{text A2m_reduce} requires an output accepted for branch sets
  L and R to be accepted for every pair of singletons drawn from them; any state may be
  drawn from an empty set. Requiring A2 of every slice would be too strong for the lifted
  merge below.\<close>

definition singleton_output :: "'s achoices des_vars_ext \<Rightarrow> bool"
where "singleton_output l \<equiv> \<exists>b x. l = ades_output b {x}"

definition selects_singleton ::
  "'s achoices des_vars_ext \<Rightarrow> 's achoices des_vars_ext \<Rightarrow> bool"
where "selects_singleton l k \<equiv> \<exists>x.
  (achoices.ac\<^sub>v (des_vars.more l) = {} \<or> x \<in> achoices.ac\<^sub>v (des_vars.more l)) \<and>
  k = ades_output (des_vars.ok\<^sub>v l) {x}"

lemma selects_singleton_output:
  "selects_singleton l k \<Longrightarrow> singleton_output k"
  by (auto simp: selects_singleton_def singleton_output_def)

lemma selects_from_singleton:
  "singleton_output l \<Longrightarrow> (selects_singleton l k \<longleftrightarrow> k = l)"
  by (auto simp: selects_singleton_def singleton_output_def)

lemma selects_singleton_output_iff:
  "selects_singleton (ades_output a L) (ades_output b K) \<longleftrightarrow>
   (a = b \<and> (\<exists>x. (L = {} \<or> x \<in> L) \<and> K = {x}))"
  by (auto simp: selects_singleton_def)

definition A2m_atoms :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "A2m_atoms M \<equiv> (\<lambda>(m,z).
  let l = mrg_left\<^sub>v m; r = mrg_right\<^sub>v m
  in (if singleton_output l \<and> singleton_output r
      then A2 (merge_slice M l r) (mrg_prior\<^sub>v m,z)
      else M (m,z)))"

definition A2m_reduce :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "A2m_reduce M \<equiv> (\<lambda>(m,z).
  M (m,z) \<and>
  (\<forall>l r. selects_singleton (mrg_left\<^sub>v m) l \<and> selects_singleton (mrg_right\<^sub>v m) r
    \<longrightarrow> merge_slice M l r (mrg_prior\<^sub>v m,z)))"

definition A2m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "A2m M \<equiv> A2m_reduce (A2m_atoms M)"

lemma slice_A2m_atoms:
  "merge_slice (A2m_atoms M) l r =
    (if singleton_output l \<and> singleton_output r
     then A2 (merge_slice M l r) else merge_slice M l r)"
  by (auto simp: A2m_atoms_def merge_slice_def Let_def fun_eq_iff)

lemma slice_A2m_reduce:
  "merge_slice (A2m_reduce M) l r =
    (\<lambda>obs. merge_slice M l r obs \<and>
      (\<forall>k t. selects_singleton l k \<and> selects_singleton r t \<longrightarrow> merge_slice M k t obs))"
  by (auto simp: A2m_reduce_def merge_slice_def fun_eq_iff)

lemma A2m_reduce_singletons:
  "\<lbrakk>singleton_output l; singleton_output r\<rbrakk> \<Longrightarrow>
   merge_slice (A2m_reduce M) l r = merge_slice M l r"
  by (simp add: slice_A2m_reduce selects_from_singleton)

lemma A2m_atoms_idem: "A2m_atoms (A2m_atoms M) = A2m_atoms M"
  by (rule merge_slice_ext; simp add: slice_A2m_atoms A2_idem)

lemma A2m_reduce_idem: "A2m_reduce (A2m_reduce M) = A2m_reduce M"
proof -
  have inner: "merge_slice (A2m_reduce M) k t = merge_slice M k t"
    if "selects_singleton l k" "selects_singleton r t" for l r k t
    using A2m_reduce_singletons[OF selects_singleton_output[OF that(1)]
        selects_singleton_output[OF that(2)]] .
  show ?thesis
    apply (rule merge_slice_ext)
    apply (subst slice_A2m_reduce)
    apply (subst slice_A2m_reduce)
    using inner
    apply (simp only: slice_A2m_reduce fun_eq_iff)
    by fast
qed

lemma A2m_atoms_reduce_atoms:
  "A2m_atoms (A2m_reduce (A2m_atoms M)) = A2m_reduce (A2m_atoms M)"
  apply (rule merge_slice_ext)
  apply (simp add: slice_A2m_atoms)
  using A2m_reduce_singletons slice_A2m_atoms A2_idem by metis

lemma A2m_idem: "A2m (A2m M) = A2m M"
  by (simp add: A2m_def A2m_atoms_reduce_atoms A2m_reduce_idem)

lemma A2m_atoms_mono:
  assumes "M \<sqsubseteq> N"
  shows "A2m_atoms M \<sqsubseteq> A2m_atoms N"
proof -
  have "merge_slice M l r \<sqsubseteq> merge_slice N l r" for l r
    using assms by (auto simp: pred_refine_iff merge_slice_def)
  then have "A2 (merge_slice M l r) \<sqsubseteq> A2 (merge_slice N l r)" for l r
    by (rule A2_mono)
  then show ?thesis
    using assms unfolding A2m_atoms_def Let_def pred_refine_iff by auto
qed

lemma A2m_reduce_mono:
  "M \<sqsubseteq> N \<Longrightarrow> A2m_reduce M \<sqsubseteq> A2m_reduce N"
  by (auto simp: A2m_reduce_def merge_slice_def pred_refine_iff)

lemma A2m_mono:
  "M \<sqsubseteq> N \<Longrightarrow> A2m M \<sqsubseteq> A2m N"
  unfolding A2m_def by (intro A2m_reduce_mono A2m_atoms_mono)

lemma A2m_Idempotent [closure]: "Idempotent A2m"
  by (simp add: Idempotent_def A2m_idem)

lemma A2m_Monotonic [closure]: "Monotonic A2m"
  by (rule MonotonicI, rule A2m_mono)

lemma A2m_atoms_fixed:
  "M is A2m_atoms \<longleftrightarrow>
    (\<forall>l r. singleton_output l \<and> singleton_output r \<longrightarrow> merge_slice M l r is A2)"
proof -
  have eq: "A2m_atoms M = M \<longleftrightarrow>
      (\<forall>l r. merge_slice (A2m_atoms M) l r = merge_slice M l r)"
    by (metis merge_slice_ext)
  show ?thesis
    unfolding Healthy_def' using eq by (auto simp: slice_A2m_atoms split: if_splits)
qed

lemma A2m_reduce_fixed:
  "M is A2m_reduce \<longleftrightarrow> (\<forall>l r k t obs.
    merge_slice M l r obs \<and> selects_singleton l k \<and> selects_singleton r t \<longrightarrow>
    merge_slice M k t obs)"
proof -
  have eq: "A2m_reduce M = M \<longleftrightarrow>
      (\<forall>l r. merge_slice (A2m_reduce M) l r = merge_slice M l r)"
    by (metis merge_slice_ext)
  show ?thesis
    unfolding Healthy_def'
    apply (subst eq)
    apply (simp only: slice_A2m_reduce fun_eq_iff)
    by blast
qed

lemma A2m_fixed:
  "M is A2m \<longleftrightarrow> (M is A2m_atoms) \<and> (M is A2m_reduce)"
proof
  assume h: "M is A2m"
  have atom: "merge_slice M l r is A2" if "singleton_output l" "singleton_output r" for l r
  proof -
    have "merge_slice M l r = A2 (merge_slice M l r)"
      using h[unfolded Healthy_def' A2m_def]
      by (metis A2m_reduce_singletons slice_A2m_atoms that)
    then show ?thesis by (simp add: Healthy_def')
  qed
  have t: "M is A2m_atoms" using atom A2m_atoms_fixed by blast
  have b: "M is A2m_reduce" using h t by (simp add: Healthy_def' A2m_def)
  show "(M is A2m_atoms) \<and> (M is A2m_reduce)" using t b by blast
next
  assume "(M is A2m_atoms) \<and> (M is A2m_reduce)"
  then show "M is A2m" by (simp add: Healthy_def' A2m_def)
qed

text \<open>Both parts in terms of merge observations.\<close>

lemma choices_all:
  "(\<forall>l :: 's achoices des_vars_ext. F l) \<longleftrightarrow> (\<forall>b X. F (ades_output b X))"
  using choices_ex[of "\<lambda>l. \<not> F l"] by blast

lemma obs_all:
  fixes F :: "'s angelic_design"
  shows "(\<forall>obs. F obs) \<longleftrightarrow> (\<forall>b s0 c Z. F (ades_obs b s0 c Z))"
  by pred_auto

lemma A2m_atoms_obs:
  "M is A2m_atoms \<longleftrightarrow> (\<forall>a x d y.
    merge_slice M (ades_output a {x}) (ades_output d {y}) is A2)"
  by (auto simp: A2m_atoms_fixed singleton_output_def)

lemma A2m_reduce_obs:
  "M is A2m_reduce \<longleftrightarrow> (\<forall>b s0 a L d R c Z x y.
    ades_merge_obs M b s0 a L d R c Z \<and> (L = {} \<or> x \<in> L) \<and> (R = {} \<or> y \<in> R)
    \<longrightarrow> ades_merge_obs M b s0 a {x} d {y} c Z)"
  unfolding A2m_reduce_fixed
  apply (simp only: choices_all obs_all selects_singleton_output_iff merge_slice_obs)
  by blast

subsection \<open>Parallel by Merge Preserves AD Healthiness\<close>

text \<open>The design rules @{thm [source] H1_par_by_merge}, @{thm [source] H2_par_by_merge}
  and @{thm [source] H3_par_by_merge} apply to AD relations directly. The rules below
  cover A, A2 and A3.\<close>

lemma A_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes operands: "P is H1" "Q is H1" and merge: "M is Am"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c Z
  let ?R = "P \<parallel>\<^bsub>M\<^esub> Q"
  have slices: "merge_slice M l r is A" for l r
    using merge by (simp add: Am_slices)
  have started: "A ?R (ades_obs True s0 c Z) = ?R (ades_obs True s0 c Z)"
  proof -
    have "A ?R (ades_obs True s0 c Z) =
      (\<exists>a L d R. P (ades_obs True s0 a L) \<and> Q (ades_obs True s0 d R) \<and>
       A (merge_slice M (ades_output a L) (ades_output d R)) (ades_obs True s0 c Z))"
      apply (simp only: A_obs ades_par_by_merge_slices)
      by meson
    also have "... = ?R (ades_obs True s0 c Z)"
      by (simp only: Healthy_if[OF slices] ades_par_by_merge_slices)
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
      by (simp add: A_obs ades_par_by_merge_slices; blast)
  qed
qed

text \<open>An A2 relation that accepts a choice set also accepts a singleton drawn from it;
  any singleton will do when the set is empty.\<close>

lemma A2_nonempty_singleton:
  fixes R :: "'s angelic_design"
  assumes "R is A2" "X \<noteq> {}" "R (ades_obs b s0 c X)"
  shows "\<exists>x\<in>X. R (ades_obs b s0 c {x})"
proof -
  have up: "R (ades_obs b s0 c {}) \<Longrightarrow> R (ades_obs b s0 c {x})" for x
    using A2_obs[of R b s0 c "{x}"]
    by (simp only: Healthy_if[OF assms(1)]; blast)
  show ?thesis
    using A2_obs[of R b s0 c X] up assms(2,3)
    by (simp only: Healthy_if[OF assms(1)]; blast)
qed

lemma A2_singleton_witness:
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

text \<open>With A2 operands and @{const A2m_reduce}, parallel by merge is determined by
  singleton branch outputs.\<close>

lemma ades_par_by_merge_singletons:
  assumes operands: "P is A2" "Q is A2" and reduce: "M is A2m_reduce"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z) \<longleftrightarrow>
    (\<exists>a x d y. P (ades_obs b s0 a {x}) \<and> Q (ades_obs b s0 d {y}) \<and>
      merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z))"
proof
  have red: "\<And>a L d R x y. \<lbrakk>ades_merge_obs M b s0 a L d R c Z; L = {} \<or> x \<in> L;
      R = {} \<or> y \<in> R\<rbrakk> \<Longrightarrow> ades_merge_obs M b s0 a {x} d {y} c Z"
    using reduce[unfolded A2m_reduce_obs] by blast
  assume "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
  then obtain a L d R where pq:
    "P (ades_obs b s0 a L)" "Q (ades_obs b s0 d R)"
    "ades_merge_obs M b s0 a L d R c Z"
    by (auto simp: ades_par_by_merge_slices merge_slice_obs)
  obtain x where x: "L = {} \<or> x \<in> L" "P (ades_obs b s0 a {x})"
    using A2_singleton_witness[OF operands(1) pq(1)] by blast
  obtain y where y: "R = {} \<or> y \<in> R" "Q (ades_obs b s0 d {y})"
    using A2_singleton_witness[OF operands(2) pq(2)] by blast
  show "\<exists>a x d y. P (ades_obs b s0 a {x}) \<and> Q (ades_obs b s0 d {y}) \<and>
    merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z)"
    using x(2) y(2) red[OF pq(3) x(1) y(1)] by (auto simp: merge_slice_obs)
next
  assume "\<exists>a x d y. P (ades_obs b s0 a {x}) \<and> Q (ades_obs b s0 d {y}) \<and>
    merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z)"
  then show "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
    by (auto simp: ades_par_by_merge_slices)
qed

lemma A2_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes operands: "P is A2" "Q is A2" and merge: "M is A2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A2"
proof (rule Healthy_intro, rule ades_obs_ext)
  fix b s0 c Z
  have reduce: "M is A2m_reduce" and atoms: "M is A2m_atoms"
    using merge by (simp_all add: A2m_fixed)
  have atom_A2: "merge_slice M (ades_output a {x}) (ades_output d {y}) is A2" for a x d y
    using atoms by (simp add: A2m_atoms_obs)
  have obs: "merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c Z) \<longleftrightarrow>
    (merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c {}) \<or>
     (\<exists>z\<in>Z. merge_slice M (ades_output a {x}) (ades_output d {y}) (ades_obs b s0 c {z})))"
    for a x d y
    using A2_obs[of "merge_slice M (ades_output a {x}) (ades_output d {y})" b s0 c Z]
    by (simp only: Healthy_if[OF atom_A2])
  show "A2 (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z) = (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
    apply (simp only: A2_obs ades_par_by_merge_singletons[OF operands reduce])
    using obs by fast
qed

lemma A3_par_by_merge [closure]:
  fixes M :: "'s ades_merge_rel"
  assumes "P is H1" "Q is H1" "M is H1m" "M is H3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A3"
  by (rule H1_H3_impl_A3[OF H1_par_by_merge[OF assms(1-3)] H3_par_by_merge[OF assms(4)]])

subsection \<open>Lifting a State Merge\<close>

text \<open>The raw lift requires every branch-state pair to have a witness in the
  output choice set, independently of termination. Design skip will release the
  final choice set after divergence while retaining an intermediate merge witness.\<close>

definition ades_lift_merge :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ades_lift_merge j \<equiv> (\<lambda>(m,obsOut).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        SL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        SR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        SOut = achoices.ac\<^sub>v (des_vars.more obsOut)
    in SL \<noteq> {} \<and> SR \<noteq> {} \<and>
       des_vars.ok\<^sub>v obsOut =
         (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
       (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut))"

lemma ades_lift_merge_obs:
  "ades_merge_obs (ades_lift_merge j) ok0 s0 okL SL okR SR okOut SOut \<longleftrightarrow>
    (SL \<noteq> {} \<and> SR \<noteq> {} \<and> okOut = (okL \<and> okR) \<and>
     (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut))"
  by (auto simp: ades_lift_merge_def Let_def)

definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "merge_ades j \<equiv> H1m (ades_lift_merge j) ;; II\<^sub>D"

lemma merge_ades_completion [simp]: "merge_ades j ;; II\<^sub>D = merge_ades j"
  by (simp add: merge_ades_def seqr_assoc)

text \<open>merge_ades adds unstarted behaviour to the raw lift, then completes with
  design skip. When ok0 is false, the completed merge imposes no constraints.
  When started, branch sets remain nonempty and every pair of branch states has some
  merged state. Termination and coverage are required only when both branches terminate;
  otherwise every output set is permitted.\<close>

lemma merge_ades_unfold:
  "merge_ades j = (\<lambda>(m,obsOut).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        SL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        SR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        SOut = achoices.ac\<^sub>v (des_vars.more obsOut)
    in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
       (SL \<noteq> {} \<and> SR \<noteq> {} \<and>
        (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut. merge_eval j s0 sL sR sOut) \<and>
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)
          \<longrightarrow> (des_vars.ok\<^sub>v obsOut \<and>
        (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut)))))"
  by (simp add: merge_ades_def ades_lift_merge_def H1m_def Let_def;
      pred_auto; metis UNIV_I ex_in_conv)

lemma merge_ades_obs:
  "ades_merge_obs (merge_ades j) ok0 s0 okL SL okR SR okOut SOut \<longleftrightarrow>
    (\<not> ok0 \<or> (SL \<noteq> {} \<and> SR \<noteq> {} \<and>
      (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut. merge_eval j s0 sL sR sOut) \<and>
      (okL \<and> okR \<longrightarrow>
        (okOut \<and> (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut)))))"
  by (auto simp: merge_ades_unfold Let_def)

text \<open>The lifted merge meets every merge condition, for every j.\<close>

lemma merge_ades_is_H1m [closure]: "merge_ades j is H1m"
  by (simp add: Healthy_def' merge_ades_def H1m_def; pred_auto)

lemma merge_ades_is_H2m [closure]: "merge_ades j is H2m"
  by (simp add: Healthy_def' H2m_def merge_ades_def seqr_assoc skip_d_absorb_J_1)

lemma merge_ades_is_HDM [closure]: "merge_ades j is HDM"
  by (rule HDM_intro[OF merge_ades_is_H1m merge_ades_is_H2m])

lemma merge_ades_is_H3m [closure]: "merge_ades j is H3m"
  by (simp add: Healthy_def' H3m_def)

lemma merge_ades_is_Am [closure]: "merge_ades j is Am"
proof -
  have "merge_slice (merge_ades j) l r is A" for l r
    apply (rule Healthy_intro, rule ades_obs_ext)
    apply (cases l; cases r)
    apply (simp add: A_obs merge_slice_def merge_ades_unfold Let_def)
    by blast
  then show ?thesis
    by (simp add: Am_slices)
qed

lemma merge_ades_is_A2m [closure]: "merge_ades j is A2m"
proof -
  have atoms: "merge_slice (merge_ades j) (ades_output a {x}) (ades_output d {y}) is A2"
    for a x d y
    by (rule Healthy_intro, rule ades_obs_ext;
        simp add: A2_obs merge_slice_obs merge_ades_obs[simplified]; blast)
  have reduce: "ades_merge_obs (merge_ades j) b s0 a {x} d {y} c Z"
    if "ades_merge_obs (merge_ades j) b s0 a L d R c Z" "L = {} \<or> x \<in> L" "R = {} \<or> y \<in> R"
    for b s0 a L d R c Z x y
    using that by (auto simp: merge_ades_obs[simplified]; blast)
  show ?thesis
    unfolding A2m_fixed A2m_atoms_obs A2m_reduce_obs
    using atoms reduce by blast
qed

subsection \<open>AD Parallel\<close>

text \<open>AD parallel retains the A3 wrapper for unconditional A3 closure.
  For H1-healthy operands, lifted parallel is already A3-healthy, so the wrapper
  is redundant. A2 closure requires only A2-healthy operands; the wrapper
  preserves A2 without any additional operand premises.\<close>

definition ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = A3 (P \<parallel>\<^bsub>merge_ades j\<^esub> Q)"

text \<open>Closure of parallel by the lifted merge follows from the generic rules.\<close>

lemma ades_par_lifted_A_closure:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A"
  by (rule A_par_by_merge[OF assms merge_ades_is_Am])

lemma ades_par_lifted_A2_closure:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A2"
  by (rule A2_par_by_merge[OF assms merge_ades_is_A2m])

lemma ades_par_lifted_A3_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A3"
  by (rule A3_par_by_merge[OF assms merge_ades_is_H1m merge_ades_is_H3m])

lemma ades_par_eq_lifted:
  assumes "P is H1" "Q is H1"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = P \<parallel>\<^bsub>merge_ades j\<^esub> Q"
  using ades_par_lifted_A3_closure[OF assms]
  by (simp add: ades_par_def Healthy_def')

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_def
  by (rule A3_preserves_A[OF ades_par_lifted_A_closure[OF assms]])

lemma ades_par_A2_closure [closure]:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  unfolding ades_par_def
  by (rule A3_preserves_A2[OF ades_par_lifted_A2_closure[OF assms]])

lemma ades_par_A3_closure [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  by (simp add: ades_par_def Healthy_def' A3_idem)

text \<open>A2 alone reduces accepted nonempty branch sets to singleton witnesses.
  Without H1, unstarted parallel still requires feasible observations from both
  operands; this requirement is independent of the final choice set.\<close>

lemma ades_par_lifted_obs_A2:
  fixes P Q :: "'s angelic_design"
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    (if ok0 then
      (\<exists>okL sL okR sR.
        P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
        (\<exists>sOut. merge_eval j s0 sL sR sOut) \<and>
        (okL \<and> okR \<longrightarrow> (okOut \<and> (\<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut))))
     else
      ((\<exists>okL SL. P (ades_obs False s0 okL SL)) \<and>
       (\<exists>okR SR. Q (ades_obs False s0 okR SR))))"
  apply (cases ok0; simp add: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified])
  apply (rule iffI)
  subgoal
    using A2_nonempty_singleton[OF assms(1)] A2_nonempty_singleton[OF assms(2)]
    by metis
  subgoal by (fastforce intro: exI[where x="{_}"])
  done

lemma ades_par_lifted_obs:
  fixes P Q :: "'s angelic_design"
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    (\<not> ok0 \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>sOut. merge_eval j s0 sL sR sOut) \<and>
      (okL \<and> okR \<longrightarrow> (okOut \<and> (\<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut)))))"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: A_healthy_components_iff)
  show ?thesis
    using operands_H1
    by (cases ok0; simp add: ades_par_lifted_obs_A2[OF assms(3,4)] H1_healthy_obs_iff)
qed

lemma ades_par_lifted_diverge:
  assumes "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 False X)"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 okOut Y)"
  using assms
  by (auto simp: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified]; blast)

lemma ades_par_obs_A2:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not>b \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>z. merge_eval j s0 sL sR z) \<and>
      (okL \<and> okR \<longrightarrow> (c \<and> (\<exists>z\<in>X. merge_eval j s0 sL sR z)))))"
  by (simp only: ades_par_def A3_obs ades_par_lifted_obs_A2[OF assms];
      auto; blast)

lemma ades_par_normalise_A:
  assumes "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q"
  by (rule ades_obs_ext;
      simp add: ades_par_obs_A2[OF assms]
        ades_par_obs_A2[OF A_preserves_A2[OF assms(1)] A_preserves_A2[OF assms(2)]]
        A_obs_A2[OF assms(1)] A_obs_A2[OF assms(2)] ex_bool_eq; blast)

lemma ades_par_eval:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    (\<exists>okL SL okR SR.
      P (ades_obs ok0 s0 okL SL) \<and> Q (ades_obs ok0 s0 okR SR) \<and>
      (\<not>ok0 \<or> (SL \<noteq> {} \<and> SR \<noteq> {} \<and>
        (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut. merge_eval j s0 sL sR sOut) \<and>
        (okL \<and> okR \<longrightarrow> (okOut \<and>
          (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut))))))"
  by (simp add: ades_par_eq_lifted[OF assms]
      ades_par_by_merge_eval choices_ex merge_ades_obs[simplified])

subsection \<open>Correspondence with Designs\<close>

text \<open>For A- and A2-healthy operands, converting with ac2p, composing by ordinary
  design parallel, and converting back with d2ac gives AD parallel.
  All four mapping laws below hold for any state merge j.\<close>

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
    apply (simp only: ades_par_eq_lifted[OF operands_H1]
      ades_par_lifted_obs[OF assms] d2ac_healthy_obs[OF des_par_H_closure[OF H_implies_H1[OF designs_H(1)] H_implies_H1[OF designs_H(2)]]]
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

text \<open>The same laws for parallel by the lifted merge, without the A3 wrapper.\<close>

lemma ades_par_lifted_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^bsub>merge_ades j\<^esub> Q) =
    (ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q)"
  using ades_par_ac2p[OF assms, where j=j] ades_par_eq_lifted[of P Q j] assms
  by (simp add: A_healthy_components_iff)

lemma ades_par_lifted_d2ac:
  assumes "D is \<^bold>H" "E is \<^bold>H"
  shows "(d2ac D) \<parallel>\<^bsub>merge_ades j\<^esub> (d2ac E) =
    d2ac (D \<parallel>\<^sub>D\<^bsub>j\<^esub> E)"
  using ades_par_d2ac[OF assms, where j=j]
    ades_par_eq_lifted[of "d2ac D" "d2ac E" j]
    d2ac_is_A[of D] d2ac_is_A[of E]
  by (simp add: A_healthy_components_iff)

subsection \<open>Algebraic Laws\<close>

subsubsection \<open>Monotonicity\<close>

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1) \<sqsubseteq> (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_def
  by (rule A3_mono; use assms in \<open>auto simp: pred_refine_iff ades_par_by_merge_eval split: prod.splits; blast\<close>)

subsubsection \<open>Chaos\<close>

text \<open>A nonterminating branch observation releases the output guarantee.
  Chaos in both branches therefore yields Chaos whenever the state merge has
  some merged state at every initial state.\<close>

lemma ades_par_lifted_chaos:
  assumes "\<And>s0. \<exists>sL sR sOut. merge_eval j s0 sL sR sOut"
  shows "(true \<parallel>\<^bsub>merge_ades j\<^esub> true :: 's angelic_design) = true"
proof (rule ades_obs_ext)
  fix b s0 c X
  obtain sL sR sOut where witness: "merge_eval j s0 sL sR sOut"
    using assms by blast
  have started: "\<exists>okL SL okR SR. SL \<noteq> {} \<and> SR \<noteq> {} \<and>
      (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut. merge_eval j s0 sL sR sOut) \<and>
      (okL \<and> okR \<longrightarrow>
        (c \<and> (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>X. merge_eval j s0 sL sR sOut)))"
    by (rule exI[of _ False], rule exI[of _ "{sL}"], rule exI[of _ False],
        rule exI[of _ "{sR}"]) (use witness in blast)
  show "(true \<parallel>\<^bsub>merge_ades j\<^esub> true :: 's angelic_design) (ades_obs b s0 c X) =
    (true :: 's angelic_design) (ades_obs b s0 c X)"
    using started
    by (simp add: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified] true_pred_def)
qed

lemma ades_par_chaos:
  assumes "\<And>s0. \<exists>sL sR sOut. merge_eval j s0 sL sR sOut"
  shows "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true :: 's angelic_design) = true"
  by (simp add: ades_par_def ades_par_lifted_chaos[OF assms] Healthy_def' A3_def; pred_auto)

subsubsection \<open>Commutativity\<close>

lemma SymMerge_ades:
  fixes M :: "'s ades_merge_rel"
  shows "M is SymMerge \<longleftrightarrow>
    (\<forall>obs0 obsL obsR obsOut. ades_merge_eval M obs0 obsL obsR obsOut = ades_merge_eval M obs0 obsR obsL obsOut)"
  by (simp add: Healthy_def' fun_eq_iff; pred_auto; blast)

lemma merge_ades_SymMerge [closure]:
  assumes "j is SymMerge"
  shows "merge_ades j is SymMerge"
  using assms
  by (simp add: Healthy_def' fun_eq_iff merge_ades_unfold; pred_auto; blast)

lemma ades_par_comm:
  assumes "j is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P)"
  unfolding ades_par_def
  by (rule arg_cong[where f=A3], rule par_by_merge_comm;
      use merge_ades_SymMerge[OF assms] in \<open>simp add: Healthy_def'\<close>)

subsubsection \<open>Associativity\<close>

text \<open>Associativity holds for A2-healthy operands under the merge premises of
  des_par_assoc_state: j is symmetric, associative, and mergeable.\<close>

lemma ades_par_assoc:
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and merge: "j is SymMerge" "AssocMerge j" "mergeable j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R =
    P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have AP: "A P is A" "A Q is A" "A R is A"
    by (simp_all add: Healthy_def' A_idem)
  have A2P: "A P is A2" "A Q is A2" "A R is A2"
    using operands by (auto intro: A_preserves_A2)
  have norm: "A (S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> T) = S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> T"
    if "S is A2" "T is A2" for S T
  proof -
    have "A S is H1" "A T is H1"
      by (simp_all add: Healthy_def' A_is_H1)
    then have "(A S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A T) is A"
      by (rule ades_par_A_closure)
    then show ?thesis
      by (simp only: ades_par_normalise_A[OF that] Healthy_def')
  qed
  have left:
    "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R =
     (A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R"
    apply (subst ades_par_normalise_A[OF ades_par_A2_closure[OF operands(1,2)] operands(3)])
    apply (subst norm[OF operands(1,2)])
    by (simp only: ades_par_normalise_A[OF operands(1,2)])
  have right:
    "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) =
     A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
    apply (subst ades_par_normalise_A[OF operands(1) ades_par_A2_closure[OF operands(2,3)]])
    apply (subst norm[OF operands(2,3)])
    by (simp only: ades_par_normalise_A[OF operands(2,3)])
  have inner_A: "(A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) is A"
    "(A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R) is A"
    by (rule ades_par_A_closure; simp add: Healthy_def' A_is_H1)+
  have inner_A2: "(A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) is A2"
    "(A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R) is A2"
    using A2P by (auto intro: ades_par_A2_closure)
  have assoc:
    "(A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R =
     A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
    by (simp only: ades_par_d2ac_ac2p[OF inner_A(1) AP(3) inner_A2(1) A2P(3)]
        ades_par_d2ac_ac2p[OF AP(1) inner_A(2) A2P(1) inner_A2(2)]
        ades_par_ac2p[OF AP(1,2) A2P(1,2)]
        ades_par_ac2p[OF AP(2,3) A2P(2,3)] des_par_assoc_state[OF merge])
  show ?thesis
    by (simp only: left right assoc)
qed

subsection \<open>Example: Skip Merge\<close>

text \<open>With two terminating branch observations, the skip state merge requires
  s0 in SOut. A nonterminating branch permits every output set, including empty.\<close>

lemma ades_par_skip_eval:
  assumes operands: "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    (\<not>ok0 \<or> (\<exists>okL SL okR SR.
      SL \<noteq> {} \<and> SR \<noteq> {} \<and>
      P (ades_obs True s0 okL SL) \<and> Q (ades_obs True s0 okR SR) \<and>
      (okL \<and> okR \<longrightarrow> (okOut \<and> s0 \<in> SOut))))"
  using operands[unfolded H1_healthy_obs_iff]
  by (cases ok0; simp add: ades_par_eq_lifted[OF operands]
      ades_par_by_merge_eval choices_ex merge_ades_obs[simplified] skip_merge_eval; blast)

lemma ades_par_skip_comm:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> P)"
  by (rule ades_par_comm; simp add: Healthy_def skip_merge_swap)

lemma ades_par_skip_assoc:
  assumes "P is A2" "Q is A2" "R is A2"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R) =
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R))"
proof (rule ades_par_assoc[OF assms])
  show "skip\<^sub>m is SymMerge"
    by (simp add: Healthy_def skip_merge_swap)
  show "AssocMerge skip\<^sub>m"
    by (simp add: AssocMerge_def skip\<^sub>m_def; pred_auto)
qed (simp add: skip_merge_eval)

end
