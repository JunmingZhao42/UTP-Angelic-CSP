theory tmp_pide_mcp_scratch_ades_merge_health
  imports tmp_pide_mcp_scratch_ades_generic_closure
begin

definition merge_health ::
  "('s angelic_design \<Rightarrow> 's angelic_design) \<Rightarrow>
   's ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "merge_health H M \<equiv> (\<lambda>(m,z).
  H (merge_slice M (mrg_left\<^sub>v m) (mrg_right\<^sub>v m))
    (mrg_prior\<^sub>v m,z))"

lemma slice_health:
  "merge_slice (merge_health H M) l r = H (merge_slice M l r)"
  by (auto simp: merge_slice_def merge_health_def fun_eq_iff)

lemma merge_slice_ext:
  assumes "\<And>l r. merge_slice M l r = merge_slice N l r"
  shows "M = N"
  using assms by (auto simp: merge_slice_def fun_eq_iff; metis (full_types) mrg.cases)

definition AM :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "AM M \<equiv> merge_health A M"

lemma AM_idem: "AM (AM M) = AM M"
  by (rule merge_slice_ext; simp add: AM_def slice_health A_idem)

lemma AM_fixed:
  "M is AM \<longleftrightarrow> (\<forall>l r. merge_slice M l r is A)"
  unfolding Healthy_def' AM_def
  by (metis slice_health merge_slice_ext)
lemma AM_mono:
  assumes "M \<sqsubseteq> N"
  shows "AM M \<sqsubseteq> AM N"
proof -
  have sl: "merge_slice M l r \<sqsubseteq> merge_slice N l r" for l r
    using assms by (auto simp: pred_refine_iff merge_slice_def)
  have al: "A (merge_slice M l r) \<sqsubseteq> A (merge_slice N l r)" for l r
    by (rule A_mono[OF sl])
  show ?thesis
    using al unfolding AM_def merge_health_def pred_refine_iff by auto
qed

definition atom_branch :: "'s achoices des_vars_ext \<Rightarrow> bool"
where "atom_branch l \<equiv> \<exists>b x. l = ades_output b {x}"

definition selects :: "'s achoices des_vars_ext \<Rightarrow> 's achoices des_vars_ext \<Rightarrow> bool"
where "selects l k \<equiv> \<exists>x.
  (achoices.ac\<^sub>v (des_vars.more l) = {} \<or> x \<in> achoices.ac\<^sub>v (des_vars.more l)) \<and>
  k = ades_output (des_vars.ok\<^sub>v l) {x}"

lemma selects_atom:
  "selects l k \<Longrightarrow> atom_branch k"
  by (auto simp: selects_def atom_branch_def)

lemma selects_from_atom:
  "atom_branch l \<Longrightarrow> (selects l k \<longleftrightarrow> k = l)"
  by (auto simp: selects_def atom_branch_def)

definition ATM :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "ATM M \<equiv> (\<lambda>(m,z).
  let l = mrg_left\<^sub>v m; r = mrg_right\<^sub>v m
  in (if atom_branch l \<and> atom_branch r
      then A2 (merge_slice M l r) (mrg_prior\<^sub>v m,z)
      else M (m,z)))"

lemma slice_ATM:
  "merge_slice (ATM M) l r =
    (if atom_branch l \<and> atom_branch r then A2 (merge_slice M l r) else merge_slice M l r)"
  by (auto simp: ATM_def merge_slice_def Let_def fun_eq_iff)

lemma ATM_idem: "ATM (ATM M) = ATM M"
  by (rule merge_slice_ext; simp add: slice_ATM A2_idem)

definition BRM :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "BRM M \<equiv> (\<lambda>(m,z).
  M (m,z) \<and> (\<forall>l r. selects (mrg_left\<^sub>v m) l \<and> selects (mrg_right\<^sub>v m) r
    \<longrightarrow> merge_slice M l r (mrg_prior\<^sub>v m,z)))"

lemma slice_BRM:
  "merge_slice (BRM M) l r =
    (\<lambda>obs. merge_slice M l r obs \<and>
      (\<forall>k t. selects l k \<and> selects r t \<longrightarrow> merge_slice M k t obs))"
  by (auto simp: BRM_def merge_slice_def fun_eq_iff)

lemma BRM_atoms:
  "\<lbrakk>atom_branch l; atom_branch r\<rbrakk> \<Longrightarrow>
   merge_slice (BRM M) l r = merge_slice M l r"
  by (simp add: slice_BRM selects_from_atom)

lemma BRM_idem: "BRM (BRM M) = BRM M"
proof -
  have inner: "merge_slice (BRM M) k t = merge_slice M k t"
    if "selects l k" "selects r t" for l r k t
    using BRM_atoms[OF selects_atom[OF that(1)] selects_atom[OF that(2)]] .
  show ?thesis
    apply (rule merge_slice_ext)
    apply (subst slice_BRM)
    apply (subst slice_BRM)
    using inner
    apply (simp only: slice_BRM fun_eq_iff)
    by fast
qed

definition A2M :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel"
where "A2M M \<equiv> BRM (ATM M)"

lemma ATM_BRM_ATM: "ATM (BRM (ATM M)) = BRM (ATM M)"
  apply (rule merge_slice_ext)
  apply (simp add: slice_ATM)
  using BRM_atoms slice_ATM A2_idem by metis

lemma A2M_idem: "A2M (A2M M) = A2M M"
  by (simp add: A2M_def ATM_BRM_ATM BRM_idem)

lemma ATM_mono:
  assumes "M \<sqsubseteq> N"
  shows "ATM M \<sqsubseteq> ATM N"
proof -
  have sl: "merge_slice M l r \<sqsubseteq> merge_slice N l r" for l r
    using assms by (auto simp: pred_refine_iff merge_slice_def)
  have al: "A2 (merge_slice M l r) \<sqsubseteq> A2 (merge_slice N l r)" for l r
    by (rule A2_mono[OF sl])
  show ?thesis
    using assms al unfolding ATM_def Let_def pred_refine_iff by auto
qed

lemma BRM_mono:
  "M \<sqsubseteq> N \<Longrightarrow> BRM M \<sqsubseteq> BRM N"
  by (auto simp: BRM_def merge_slice_def pred_refine_iff)

lemma A2M_mono:
  "M \<sqsubseteq> N \<Longrightarrow> A2M M \<sqsubseteq> A2M N"
  unfolding A2M_def by (intro BRM_mono ATM_mono)

lemma ATM_fixed:
  "M is ATM \<longleftrightarrow>
    (\<forall>l r. atom_branch l \<and> atom_branch r \<longrightarrow> merge_slice M l r is A2)"
proof -
  have eq: "ATM M = M \<longleftrightarrow> (\<forall>l r. merge_slice (ATM M) l r = merge_slice M l r)"
    by (metis merge_slice_ext)
  show ?thesis
    unfolding Healthy_def' using eq by (auto simp: slice_ATM split: if_splits)
qed

lemma BRM_fixed:
  "M is BRM \<longleftrightarrow> (\<forall>l r k t obs.
    merge_slice M l r obs \<and> selects l k \<and> selects r t \<longrightarrow>
    merge_slice M k t obs)"
proof -
  have eq: "BRM M = M \<longleftrightarrow> (\<forall>l r. merge_slice (BRM M) l r = merge_slice M l r)"
    by (metis merge_slice_ext)
  show ?thesis
    unfolding Healthy_def'
    apply (subst eq)
    apply (simp only: slice_BRM fun_eq_iff)
    by blast
qed

lemma A2M_fixed:
  "M is A2M \<longleftrightarrow> (M is ATM) \<and> (M is BRM)"
proof
  assume h: "M is A2M"
  have atom: "merge_slice M l r is A2" if "atom_branch l" "atom_branch r" for l r
  proof -
    have "merge_slice M l r = A2 (merge_slice M l r)"
      using h[unfolded Healthy_def' A2M_def]
      by (metis BRM_atoms slice_ATM that)
    then show ?thesis by (simp add: Healthy_def')
  qed
  have t: "M is ATM" using atom ATM_fixed by blast
  have b: "M is BRM" using h t by (simp add: Healthy_def' A2M_def)
  show "(M is ATM) \<and> (M is BRM)" using t b by blast
next
  assume "(M is ATM) \<and> (M is BRM)"
  then show "M is A2M" by (simp add: Healthy_def' A2M_def)
qed

lemma AM_Monotonic: "Monotonic AM"
  by (rule MonotonicI, rule AM_mono)
lemma AM_Idempotent: "Idempotent AM"
  by (simp add: Idempotent_def AM_idem)
lemma A2M_Monotonic: "Monotonic A2M"
  by (rule MonotonicI, rule A2M_mono)
lemma A2M_Idempotent: "Idempotent A2M"
  by (simp add: Idempotent_def A2M_idem)

lemma ATM_fixed_obs:
  "M is ATM \<longleftrightarrow> (\<forall>a x d y.
    merge_slice M (ades_output a {x}) (ades_output d {y}) is A2)"
  by (auto simp: ATM_fixed atom_branch_def)

lemma selects_output:
  "selects (ades_output a L) (ades_output b K) \<longleftrightarrow>
   (a = b \<and> (\<exists>x. (L = {} \<or> x \<in> L) \<and> K = {x}))"
  by (auto simp: selects_def)

lemma choices_all:
  "(\<forall>l :: 's achoices des_vars_ext. F l) \<longleftrightarrow> (\<forall>b X. F (ades_output b X))"
  using choices_ex[of "\<lambda>l. \<not> F l"] by blast

lemma obs_all:
  fixes F :: "'s angelic_design"
  shows "(\<forall>obs. F obs) \<longleftrightarrow> (\<forall>b s0 c Z. F (ades_obs b s0 c Z))"
  by pred_auto

lemma BRM_fixed_obs:
  "M is BRM \<longleftrightarrow> (\<forall>b s0 a L d R c Z x y.
    ades_merge_obs M b s0 a L d R c Z \<and> (L = {} \<or> x \<in> L) \<and> (R = {} \<or> y \<in> R)
    \<longrightarrow> ades_merge_obs M b s0 a {x} d {y} c Z)"
  unfolding BRM_fixed
  apply (simp only: choices_all obs_all selects_output slice_obs)
  by blast

lemma generic_AM_closure:
  assumes "P is H1" "Q is H1" "M is AM"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A"
  using assms AM_fixed by (blast intro: generic_A_slices)

lemma generic_A2M_closure:
  assumes "P is A2" "Q is A2" "M is A2M"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is A2"
  apply (rule generic_A2_atoms[OF assms(1,2)])
  using assms(3)[unfolded A2M_fixed BRM_fixed_obs ATM_fixed_obs]
  by blast+

lemma constructed_AM: "merge_ades j is AM"
  by (simp add: AM_fixed constructed_A_slices)

lemma constructed_A2M: "merge_ades j is A2M"
  unfolding A2M_fixed ATM_fixed_obs BRM_fixed_obs
  apply (intro conjI allI impI)
  apply (rule constructed_A2_atoms)
  apply (elim conjE)
  apply (rule constructed_reduce; assumption)
  done

end