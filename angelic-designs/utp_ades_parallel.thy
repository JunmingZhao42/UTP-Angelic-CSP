section \<open>Angelic Design Parallel-by-Merge\<close>

theory utp_ades_parallel
  imports utp_ades_designs

begin

subsection \<open>Parallel by Merge\<close>

text \<open>
  A merge sees the initial observation, both branch results, and the final
  result. It specifies how the branch choice sets relate to the final set.
\<close>

type_synonym 's ades_mrg =
  "('s astate des_vars_ext, 's achoices des_vars_ext, 's achoices des_vars_ext) mrg"

type_synonym 's ades_merge_rel = "('s ades_mrg, 's achoices des_vars_ext) urel"

abbreviation ades_merge_eval ::
  "'s ades_merge_rel \<Rightarrow> 's astate des_vars_ext \<Rightarrow>
   's achoices des_vars_ext \<Rightarrow> 's achoices des_vars_ext \<Rightarrow>
   's achoices des_vars_ext \<Rightarrow> bool"
where
"ades_merge_eval M s0 p q out \<equiv>
  M ((\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>
      :: 's ades_mrg), out)"

abbreviation ades_merge_obs where
  "ades_merge_obs M b s0 a X d Y c Z \<equiv>
    (\<lambda>(x,out). ades_merge_eval M x (ades_output a X) (ades_output d Y) out)
      (ades_obs b s0 c Z)"

text \<open>
  Parallel runs both branches from the same initial observation and uses M
  to relate their results to the final observation.
\<close>

abbreviation ades_par ::
  "'s angelic_design \<Rightarrow> 's ades_merge_rel \<Rightarrow>
   's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "ades_par P M Q \<equiv> P \<parallel>\<^bsub>M\<^esub> Q"

lemma ades_par_eval:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval M x p q out)"
  by (cases x; cases out;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

lemma ades_merge_refine:
  assumes "M \<sqsubseteq> N"
  shows "(\<lambda>(x,out). ades_merge_eval M x p q out) \<sqsubseteq> (\<lambda>(x,out). ades_merge_eval N x p q out)"
  using assms by (auto simp:  pred_refine_iff)

lemma ades_merge_refineI:
  fixes M N :: "'s ades_merge_rel"
  assumes "\<And>p q. (\<lambda>(x,out). ades_merge_eval M x p q out) \<sqsubseteq> (\<lambda>(x,out). ades_merge_eval N x p q out)"
  shows "M \<sqsubseteq> N"
  using assms
  by (simp add: pred_refine_iff; pred_auto)

lemma ades_merge_ext:
  fixes M N :: "'s ades_merge_rel"
  assumes "\<And>p q. (\<lambda>(x,out). ades_merge_eval M x p q out) = (\<lambda>(x,out). ades_merge_eval N x p q out)"
  shows "M = N"
  by (rule ref_antisym; rule ades_merge_refineI; simp add: assms)

subsection \<open>Merge Healthiness and Closure\<close>

text \<open>
  A0m, A1m and A2m apply the corresponding condition with the two branch
  results held fixed. Each merge condition supports a closure theorem for
  parallel.
\<close>

subsubsection \<open>A0\<close>

(* Fixing the branch results p and q gives a relation R from the initial
   observation to the final observation. A0m applies A0 to this relation
   for every pair of branch results. *)
definition A0m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A0m M \<equiv> (\<lambda>(m,out).
    let p = mrg_left\<^sub>v m;
        q = mrg_right\<^sub>v m;
        R = (\<lambda>(x,y). ades_merge_eval M x p q y)
    in A0 R (mrg_prior\<^sub>v m,out))"

lemma A0m_design:
  "(\<lambda>(x,out). ades_merge_eval (A0m M) x p q out) =
    A0 (\<lambda>(x,out). ades_merge_eval M x p q out)"
  by (simp add: A0m_def fun_eq_iff)

lemma A0m_healthy_iff:
  "M is A0m \<longleftrightarrow>
    (\<forall>p q. (\<lambda>(x,out). ades_merge_eval M x p q out) is A0)"
  unfolding Healthy_def' by (metis A0m_design ades_merge_ext)

lemma A0m_idem: "A0m (A0m M) = A0m M"
  by (rule ades_merge_ext; simp only: A0m_design A0_idem)

lemma A0m_Idempotent [closure]: "Idempotent (A0m)"
  by (simp add: Idempotent_def A0m_idem)

lemma A0m_mono: "M \<sqsubseteq> N \<Longrightarrow> A0m M \<sqsubseteq> A0m N"
  by (rule ades_merge_refineI; simp only: A0m_design;
      rule A0_mono, rule ades_merge_refine, assumption)

lemma A0m_Monotonic [closure]: "Monotonic (A0m)"
  by (rule MonotonicI, rule A0m_mono)

lemma A0m_healthy [closure]: "A0m M is A0m"
  by (simp add: Healthy_def' A0m_idem)

lemma ades_par_A0_closure [closure]:
  assumes "M is A0m"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A0"
  using assms
  by (auto simp only: A0m_healthy_iff A0_healthy_obs_iff ades_par_eval; blast)

subsubsection \<open>A1\<close>

definition A1m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A1m M \<equiv> (\<lambda>(m,out).
    let p = mrg_left\<^sub>v m;
        q = mrg_right\<^sub>v m;
        R = (\<lambda>(x,y). ades_merge_eval M x p q y)
    in A1 R (mrg_prior\<^sub>v m,out))"

lemma A1m_design:
  "(\<lambda>(x,out). ades_merge_eval (A1m M) x p q out) =
    A1 (\<lambda>(x,out). ades_merge_eval M x p q out)"
  by (simp add: A1m_def fun_eq_iff)

lemma A1m_healthy_iff:
  "M is A1m \<longleftrightarrow>
    (\<forall>p q. (\<lambda>(x,out). ades_merge_eval M x p q out) is A1)"
  unfolding Healthy_def' by (metis A1m_design ades_merge_ext)

lemma A1m_idem: "A1m (A1m M) = A1m M"
  by (rule ades_merge_ext; simp only: A1m_design A1_idem)

lemma A1m_Idempotent [closure]: "Idempotent (A1m)"
  by (simp add: Idempotent_def A1m_idem)

lemma A1m_mono: "M \<sqsubseteq> N \<Longrightarrow> A1m M \<sqsubseteq> A1m N"
  by (rule ades_merge_refineI; simp only: A1m_design;
      rule A1_mono, rule ades_merge_refine, assumption)

lemma A1m_Monotonic [closure]: "Monotonic (A1m)"
  by (rule MonotonicI, rule A1m_mono)

lemma A1m_healthy [closure]: "A1m M is A1m"
  by (simp add: Healthy_def' A1m_idem)

lemma ades_par_A1_distrib:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>A1m M\<^esub> Q) = A1 (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q)"
  apply (rule ades_obs_ext)
  subgoal for b s0 c X
    using assms[unfolded H1_healthy_obs_iff]
    by (cases b; simp add: ades_par_eval A1m_def A1_obs; blast)
  done

lemma ades_par_A1_closure [closure]:
  assumes "P is H1" "Q is H1" "M is A1m"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A1"
  by (simp only: Healthy_def' ades_par_A1_distrib[OF assms(1,2), symmetric]
      Healthy_if[OF assms(3)])

subsubsection \<open>A2\<close>

definition A2m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A2m M \<equiv> (\<lambda>(m,out).
    A2 (\<lambda>(x,out). ades_merge_eval M x (mrg_left\<^sub>v m) (mrg_right\<^sub>v m) out)
      (mrg_prior\<^sub>v m,out))"

lemma A2m_design:
  "(\<lambda>(x,out). ades_merge_eval (A2m M) x p q out) =
    A2 (\<lambda>(x,out). ades_merge_eval M x p q out)"
  by (simp add: A2m_def fun_eq_iff)

lemma A2m_healthy_iff:
  "M is A2m \<longleftrightarrow>
    (\<forall>p q. (\<lambda>(x,out). ades_merge_eval M x p q out) is A2)"
  unfolding Healthy_def' by (metis A2m_design ades_merge_ext)

lemma A2m_idem: "A2m (A2m M) = A2m M"
  by (rule ades_merge_ext; simp only: A2m_design A2_idem)

lemma A2m_Idempotent [closure]: "Idempotent (A2m)"
  by (simp add: Idempotent_def A2m_idem)

lemma A2m_mono: "M \<sqsubseteq> N \<Longrightarrow> A2m M \<sqsubseteq> A2m N"
  by (rule ades_merge_refineI; simp only: A2m_design;
      rule A2_mono, rule ades_merge_refine, assumption)

lemma A2m_Monotonic [closure]: "Monotonic (A2m)"
  by (rule MonotonicI, rule A2m_mono)

lemma A2m_healthy [closure]: "A2m M is A2m"
  by (simp add: Healthy_def' A2m_idem)

lemma ades_par_A2_distrib:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>A2m M\<^esub> Q) = A2 (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q)"
  by (rule ades_obs_ext; simp add: ades_par_eval A2m_def A2_obs; blast)

lemma ades_par_A2_closure [closure]:
  assumes "M is A2m"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A2"
  by (simp only: Healthy_def' ades_par_A2_distrib[symmetric] Healthy_if[OF assms])

subsubsection \<open>A3\<close>

text \<open>
  The function w :: 's \<Rightarrow> 's maps each initial state to a witness state.
  A3m uses the same witness w(s) for all branch results at initial state s.
  The modified output out_minus sets ok to False and removes w(s) from ac'.
  Terminating observations may also be accepted unchanged by M(m,out).

  This equates nontermination at {w(s)} and {}, giving A3 closure under
  the operand premises below. Other merges may preserve A3 too.
\<close>

definition A3m :: "('s \<Rightarrow> 's) \<Rightarrow> 's ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  "A3m w M \<equiv> (\<lambda>(m,out).
    let x0 = mrg_prior\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x0);
        ac' = achoices.ac\<^sub>v (des_vars.more out);
        out_minus = ades_output False (ac' - {w s0})
    in \<not> des_vars.ok\<^sub>v x0 \<or>
       M (m, out_minus) \<or>
       (des_vars.ok\<^sub>v out \<and> M (m, out)))"

lemma A3m_obs:
  "(\<lambda>(x,out). ades_merge_eval (A3m w M) x p q out) (ades_obs b s0 c X) =
    (\<not> b \<or>
      (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs b s0 False (X - {w s0})) \<or>
      (c \<and> (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs b s0 True X)))"
  by (cases c; simp add: A3m_def)

lemma A3m_witness:
  assumes "M is A3m w"
  shows "(\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs b s0 False {w s0}) =
    (\<lambda>(x,out). ades_merge_eval M x p q out) (ades_obs b s0 False {})"
  using A3m_obs[of w M p q b s0 False "{w s0}"]
    A3m_obs[of w M p q b s0 False "{}"]
  by (simp only: Healthy_if[OF assms]; simp)

lemma A3m_idem: "A3m w (A3m w M) = A3m w M"
  by (rule ades_merge_ext, rule ades_obs_ext; simp only: A3m_obs; auto)

lemma A3m_Idempotent [closure]: "Idempotent (A3m w)"
  by (simp add: Idempotent_def A3m_idem)

lemma A3m_mono: "M \<sqsubseteq> N \<Longrightarrow> A3m w M \<sqsubseteq> A3m w N"
  by (auto simp: A3m_def Let_def pred_refine_iff split: prod.splits)

lemma A3m_Monotonic [closure]: "Monotonic (A3m w)"
  by (rule MonotonicI, rule A3m_mono)

lemma A3m_healthy [closure]: "A3m w M is A3m w"
  by (simp add: Healthy_def' A3m_idem)

lemma ades_par_A3m_H1:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>A3m w M\<^esub> Q) is H1"
  using assms
  by (auto simp: H1_healthy_obs_iff ades_par_eval A3m_def; blast)

lemma ades_par_A3m_H2:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>A3m w M\<^esub> Q) is H2"
  apply (rule Healthy_intro, rule ades_obs_ext)
  subgoal for b s0 c X
    by (cases c; simp add: H2_obs ades_par_eval A3m_def; blast)
  done

lemma ades_par_A3_closure [closure]:
  assumes "P is H1" "Q is H1" "M is A3m w"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A3"
proof (rule A3_healthy_obsI)
  show "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is \<^bold>H"
    using ades_par_A3m_H1[OF assms(1,2), of w M] ades_par_A3m_H2[of P w M Q]
    by (simp only: Healthy_if[OF assms(3)]; simp add: Healthy_def' H1_H2_comp)
next
  fix s0
  show "\<not> (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) (ades_obs True s0 False {}) \<Longrightarrow>
    \<exists>z. \<not> (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) (ades_obs True s0 False {z})"
    by (rule exI[of _ "w s0"];
        simp add: ades_par_eval A3m_witness[OF assms(3), simplified])
qed

subsubsection \<open>Combined Angelic Healthiness\<close>

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1" "M is A0m" "M is A1m"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q is A"
  using ades_par_A0_closure[OF assms(3)]
    ades_par_A1_closure[OF assms(1,2,4)]
  by (simp add: Healthy_def' A_def)

subsection \<open>Combining the Merge Conditions\<close>

text \<open>
  A2m and A3m w preserve A0m and A1m healthiness. They also commute.
\<close>

lemma A3m_A0m_closure:
  assumes "M is A0m"
  shows "A3m w M is A0m"
  using assms
  by (simp only: A0m_healthy_iff A0_healthy_obs_iff A3m_obs; auto)

lemma A2m_A0m_closure:
  assumes "M is A0m"
  shows "A2m M is A0m"
  using assms
  by (simp add: A0m_healthy_iff A0_healthy_obs_iff A2m_design A2_obs)

lemma A3m_A2m_commute:
  "A3m w (A2m M) = A2m (A3m w M)"
proof -
  have singleton: "{z} - {u} = (if z = u then {} else {z})" for z u :: 's
    by auto
  show ?thesis
    apply (rule ades_merge_ext, rule ades_obs_ext)
    apply (simp only: A2m_design A2_obs A3m_obs)
    subgoal for p q b s0 c X
      by (cases c; auto simp: singleton split: if_splits)
    done
qed

lemma merge_subset_remove_twice:
  "(\<exists>Y\<subseteq>X. \<exists>Z\<subseteq>Y - {u}. F Z) \<longleftrightarrow>
    (\<exists>Z\<subseteq>X - {u}. F Z)"
  by (auto; blast intro: subset_trans)

lemma A3m_A1m_absorb:
  fixes M :: "'s ades_merge_rel"
  shows "A1m (A3m w (A1m M)) = A3m w (A1m M)"
proof -
  have subset_twice:
    "(\<exists>Y \<subseteq> X. \<exists>Z \<subseteq> Y. F Z) \<longleftrightarrow> (\<exists>Z \<subseteq> X. F Z)"
    for X :: "'s set" and F
    by (meson subset_refl subset_trans)
  show ?thesis
    apply (rule ades_merge_ext, rule ades_obs_ext)
    apply (simp only: A1m_design A1_obs A3m_obs)
    subgoal for p q b s0 c X
      by (cases b; cases c; simp add: ex_disj_distrib conj_disj_distribL
          subset_twice merge_subset_remove_twice)
    done
qed

lemma A2m_A1m_absorb:
  "A1m (A2m (A1m M)) = A2m (A1m M)"
  apply (rule ades_merge_ext, rule ades_obs_ext)
  apply (simp only: A1m_design A1_obs A2m_design A2_obs)
  subgoal for p q b s0 c X
    by (cases b; cases c; auto; blast intro: subset_trans)
  done

lemma A3m_A1m_closure:
  "M is A1m \<Longrightarrow> A3m w M is A1m"
  by (metis Healthy_def' A3m_A1m_absorb)

lemma A2m_A1m_closure:
  "M is A1m \<Longrightarrow> A2m M is A1m"
  by (metis Healthy_def' A2m_A1m_absorb)

lemma A3m_A2m_closure:
  "M is A2m \<Longrightarrow> A3m w M is A2m"
  by (simp add: Healthy_def' A3m_A2m_commute[symmetric])

subsection \<open>Algebraic Laws\<close>

text \<open>
  We use the library's SymMerge and AssocMerge conditions. The equations
  below express them through angelic observations. AssocMerge rotates three
  branches; with symmetry, this is equivalent to regrouping them.
\<close>

subsubsection \<open>Refinement and Choice\<close>

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2" "M1 \<sqsubseteq> M2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>M1\<^esub> Q1) \<sqsubseteq> (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>M2\<^esub> Q2)"
  using assms
  by (auto simp: pred_refine_iff ades_par_eval split: prod.splits; blast)

lemma ades_par_disj_left:
  "((P \<or> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) = ((P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) \<or> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R))"
  by (auto simp: fun_eq_iff ades_par_eval disj_pred_def split: prod.splits)

lemma ades_par_disj_right:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<or> R)) = ((P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<or> (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R))"
  by (auto simp: fun_eq_iff ades_par_eval disj_pred_def split: prod.splits)

subsubsection \<open>Symmetry\<close>

lemma SymMerge_ades:
  fixes M :: "'s ades_merge_rel"
  shows "M is SymMerge \<longleftrightarrow>
    (\<forall>x p q out. ades_merge_eval M x p q out = ades_merge_eval M x q p out)"
  by (simp add: Healthy_def' fun_eq_iff; pred_auto; blast)

lemma SymMerge_ades_observations:
  "M is SymMerge \<longleftrightarrow> (\<forall>p q. (\<lambda>(x,out). ades_merge_eval M x p q out) = (\<lambda>(x,out). ades_merge_eval M x q p out))"
  by (auto simp: SymMerge_ades fun_eq_iff split: prod.splits)

lemma ades_par_comm:
  assumes "M is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> P)"
  by (rule par_by_merge_comm; use assms in \<open>simp add: Healthy_def'\<close>)

lemma ades_par_comm_iff:
  "M is SymMerge \<longleftrightarrow> (\<forall>P Q. (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> P))"
proof
  assume "M is SymMerge"
  then show "\<forall>P Q. (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> P)"
    by (blast intro: ades_par_comm)
next
  assume comm: "\<forall>P Q. (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> P)"
  show "M is SymMerge"
  proof (unfold SymMerge_ades, intro allI)
    fix x p q out
    have eq: "((\<lambda>(x,r). r = p) \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> (\<lambda>(x,r). r = q)) =
        ((\<lambda>(x,r). r = q) \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> (\<lambda>(x,r). r = p))"
      using comm by blast
    from fun_cong[OF eq, of "(x,out)"]
    show "ades_merge_eval M x p q out = ades_merge_eval M x q p out"
      by (simp add: ades_par_eval)
  qed
qed

subsubsection \<open>Associativity\<close>

lemma AssocMerge_ades:
  fixes M :: "'s ades_merge_rel"
  shows "AssocMerge M \<longleftrightarrow>
    (\<forall>x p q r out.
      (\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
      (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x y p out))"
  by (simp add: AssocMerge_def ThreeWayMerge_def fun_eq_iff;
      pred_auto; blast)

lemma AssocMerge_ades_regroup:
  assumes "M is SymMerge"
  shows "AssocMerge M \<longleftrightarrow>
    (\<forall>x p q r out.
      (\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
      (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x p y out))"
  using assms unfolding AssocMerge_ades SymMerge_ades by blast

lemma ades_par_assoc:
  assumes "M is SymMerge" "AssocMerge M"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) =
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R))"
  using assms(2)[unfolded AssocMerge_ades_regroup[OF assms(1)]]
  by (auto simp: fun_eq_iff ades_par_eval; blast)

lemma ades_par_assoc_iff:
  assumes "M is SymMerge"
  shows "AssocMerge M \<longleftrightarrow>
    (\<forall>P Q R. ((P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) =
      (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R)))"
proof
  assume "AssocMerge M"
  then show "\<forall>P Q R. ((P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) =
      (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R))"
    by (blast intro: ades_par_assoc assms)
next
  assume assoc: "\<forall>P Q R. ((P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) =
      (P \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>M\<^esub> R))"
  show "AssocMerge M"
  proof (unfold AssocMerge_ades_regroup[OF assms], intro allI)
    fix x p q r out
    from fun_cong[OF assoc[rule_format,
      of "\<lambda>(x,u). u = p" "\<lambda>(x,u). u = q" "\<lambda>(x,u). u = r"],
      of "(x,out)"]
    show "(\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
        (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x p y out)"
      by (simp add: ades_par_eval)
  qed
qed

end
