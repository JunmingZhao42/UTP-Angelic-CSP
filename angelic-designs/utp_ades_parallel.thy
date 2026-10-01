section \<open>Angelic Parallel and Ordinary Designs\<close>

theory utp_ades_parallel
  imports utp_ades_designs
begin

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

lemma ades_par_raw_eval:
  "(P \<parallel>\<^bsub>M\<^esub> Q) (x,out) \<longleftrightarrow>
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> ades_merge_eval M x p q out)"
  by (cases x; cases out;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

lemma SymMerge_ades:
  fixes M :: "'s ades_merge_rel"
  shows "M is SymMerge \<longleftrightarrow>
    (\<forall>x p q out. ades_merge_eval M x p q out = ades_merge_eval M x q p out)"
  by (simp add: Healthy_def' fun_eq_iff; pred_auto; blast)


text \<open>Lift a state merge to choice sets and apply A3 to the parallel result.\<close>

subsection \<open>A Set Merge from a State Merge\<close>

text \<open>Each pair of branch states must have a merged state in the final set.
  The branch sets must be nonempty; infinite sets are allowed.
  The lifted merge also enforces startup and termination conditions.\<close>

definition lift_merge :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  [pred]: "lift_merge j \<equiv> (\<lambda>(m,out).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        X = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        Y = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        Z = achoices.ac\<^sub>v (des_vars.more out)
    in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
       (X \<noteq> {} \<and> Y \<noteq> {} \<and>
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)
          \<longrightarrow> des_vars.ok\<^sub>v out) \<and>
        (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z. merge_eval j s0 sL sR sOut)))"

lemma lift_merge_obs:
  "ades_merge_obs (lift_merge j) ok0 s0 okL X okR Y okOut Z \<longleftrightarrow>
    (\<not> ok0 \<or> (X \<noteq> {} \<and> Y \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> okOut) \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z. merge_eval j s0 sL sR sOut)))"
  by (auto simp: lift_merge_def Let_def)

lemma lift_merge_slice_A0:
  "(\<lambda>(x,out). ades_merge_eval (lift_merge j) x p q out) is A0"
  by (rule Healthy_intro; rule ades_obs_ext;
      auto simp: A0_obs lift_merge_def Let_def)

lemma lift_merge_slice_A1:
  "(\<lambda>(x,out). ades_merge_eval (lift_merge j) x p q out) is A1"
  by (rule Healthy_intro; rule ades_obs_ext;
      auto simp: A1_obs lift_merge_def Let_def; blast)

lemma ades_par_raw_A_closure:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^bsub>lift_merge j\<^esub> Q) is A"
proof -
  let ?R = "P \<parallel>\<^bsub>lift_merge j\<^esub> Q"
  have a0: "?R is A0"
    by (simp only: A0_healthy_obs_iff ades_par_raw_eval choices_ex
        lift_merge_obs[simplified]; auto)
  have merge:
    "(\<lambda>(x,out). ades_merge_eval (lift_merge j) x p q out) (ades_obs True s0 c Z) =
      ((\<exists>W\<subseteq>Z. (\<lambda>(x,out). ades_merge_eval (lift_merge j) x p q out) (ades_obs True s0 False W)) \<or>
       (c \<and> (\<exists>W\<subseteq>Z. (\<lambda>(x,out). ades_merge_eval (lift_merge j) x p q out) (ades_obs True s0 True W))))"
    for p q s0 c Z
    by (subst (1) Healthy_if[OF lift_merge_slice_A1, symmetric]; simp only: A1_obs; simp)
  have unstarted: "?R (ades_obs False s0 c Z)" for s0 c Z
    using assms[unfolded H1_healthy_obs_iff]
    by (simp add: ades_par_raw_eval choices_ex lift_merge_obs[simplified])
  have a1: "?R is A1"
    apply (rule Healthy_intro, rule ades_obs_ext)
    subgoal for b s0 c X
      apply (cases b)
      subgoal
        apply (simp add: A1_obs ades_par_raw_eval)
        using merge[of _ _ s0 c X, simplified]
        by auto
      subgoal by (simp add: A1_obs unstarted)
      done
    done
  show ?thesis using a0 a1 by (simp add: Healthy_def' A_def)
qed

subsection \<open>Choice-Set Correspondence\<close>

text \<open>A2 and upward closure give an accepted singleton in every accepted nonempty set.\<close>

lemma A2_nonempty_singleton:
  assumes "P is A" "P is A2" "X \<noteq> {}" "P (ades_obs ok0 s0 okOut X)"
  shows "\<exists>sL\<in>X. P (ades_obs ok0 s0 okOut {sL})"
proof -
  have up: "P (ades_obs ok0 s0 okOut {}) \<Longrightarrow> P (ades_obs ok0 s0 okOut {sL})" for sL
    using PBMH_ades_obs[of P ok0 s0 okOut "{sL}"]
    by (auto simp only: Healthy_if[OF A_is_PBMH_ades[OF assms(1)]]
        intro: exI[where x="{}"])
  show ?thesis
    using A2_obs[of P ok0 s0 okOut X] up assms(3,4)
    by (simp only: Healthy_if[OF assms(2)]; blast)
qed

text \<open>For A- and A2-healthy operands, a started parallel accepts a final set exactly
  when it contains an ordinary parallel result. Hence A2 is preserved and the
  empty set is rejected.\<close>

lemma ades_par_raw_obs:
  assumes "P is A" and "Q is A" and "P is A2" and "Q is A2"
  shows "(P \<parallel>\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 okOut Z) \<longleftrightarrow>
    (\<not> ok0 \<or> (\<exists>okL sL okR sR. \<exists>sOut\<in>Z.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      merge_eval j s0 sL sR sOut \<and> (okL \<and> okR \<longrightarrow> okOut)))"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1) assms(2) by (simp_all add: A_healthy_components_iff)
  show ?thesis
    using operands_H1
    apply (cases ok0; simp add: ades_par_raw_eval choices_ex
        lift_merge_obs[simplified] H1_healthy_obs_iff)
    apply (rule iffI)
    subgoal
      using A2_nonempty_singleton[OF assms(1) assms(3)] A2_nonempty_singleton[OF assms(2) assms(4)]
      by metis
    subgoal by (fastforce intro: exI[where x="{_}"])
    done
qed

lemma ades_par_raw_A2_closure:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^bsub>lift_merge j\<^esub> Q) is A2"
  by (rule Healthy_intro, rule ades_obs_ext;
      simp only: A2_obs ades_par_raw_obs[OF assms]; blast)


subsection \<open>A3-Completed Parallel from a State Merge\<close>

text \<open>Apply A3 after parallel. For H1-healthy operands, only empty final sets can change,
  and the lifted merge gives A closure. A- and A2-healthy operands give A2 closure.
  No H3 normality is required.\<close>

definition ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q =
    A3 (P \<parallel>\<^bsub>lift_merge j\<^esub> Q)"

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_def
  by (rule A3_preserves_A[OF ades_par_raw_A_closure[OF assms]])

lemma ades_par_A2_closure [closure]:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  unfolding ades_par_def
  by (rule A3_preserves_A2[OF ades_par_raw_A2_closure[OF assms]])

lemma ades_par_A3_closure [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  by (simp add: ades_par_def Healthy_def' A3_idem)

lemma ades_par_eval:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 okOut Z) \<longleftrightarrow>
    ((P \<parallel>\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 okOut Z) \<or>
      (Z = {} \<and> (\<forall>sOut.
        (P \<parallel>\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 False {sOut}))))"
proof -
  have designs_H: "(P \<parallel>\<^bsub>lift_merge j\<^esub> Q) is \<^bold>H"
    using ades_par_raw_A_closure[OF assms]
      A_is_H[of "P \<parallel>\<^bsub>lift_merge j\<^esub> Q"]
    by (simp add: Healthy_def')
  show ?thesis by (simp only: ades_par_def A3_obs_H[OF designs_H])
qed

lemma ades_par_nonempty:
  assumes "P is H1" "Q is H1" "Z \<noteq> {}"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 okOut Z) =
    (P \<parallel>\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 okOut Z)"
  by (simp only: ades_par_eval[OF assms(1,2)] assms(3); simp)

text \<open>For A- and A2-healthy operands, completed parallel equals ordinary parallel
  followed by d2ac. Both conversion laws hold for any state merge.\<close>

lemma ades_par_d2ac_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q =
    d2ac (ac2p P \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p Q)"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: A_healthy_components_iff)
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use assms(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    apply (rule ades_obs_ext)
    apply (simp only: ades_par_eval[OF operands_H1]
      ades_par_raw_obs[OF assms] d2ac_healthy_obs[OF des_par_H_closure[OF designs_H]]
      ordinary_parallel_obs ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(1)]]
      ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(2)]])
    by blast
qed

lemma ades_par_d2ac:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "d2ac P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> d2ac Q = d2ac (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)"
  by (simp only: ades_par_d2ac_ac2p[OF d2ac_is_A d2ac_is_A d2ac_is_A2 d2ac_is_A2]
      ac2p_d2ac[OF assms(1), simplified comp_apply]
      ac2p_d2ac[OF assms(2), simplified comp_apply])

lemma ades_par_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = ac2p P \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p Q"
proof -
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use assms(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    by (simp only: ades_par_d2ac_ac2p[OF assms]
        ac2p_d2ac[OF des_par_H_closure[OF designs_H], simplified comp_apply])
qed

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1) \<sqsubseteq>
    (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_def
  by (rule A3_mono; use assms in \<open>auto simp: pred_refine_iff ades_par_raw_eval split: prod.splits; blast\<close>)

lemma ades_par_comm:
  assumes "lift_merge j is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P)"
  unfolding ades_par_def
  by (rule arg_cong[where f=A3], rule par_by_merge_comm; use assms in \<open>simp add: Healthy_def'\<close>)

text \<open>Completion loses ordinary disjunction distribution. Associativity follows from
  associative state merging at the same initial state, with A- and A2-healthy
  operands. No H3 or extra A3 assumption is needed.\<close>

subsubsection \<open>Associativity of Completed Parallel\<close>

lemma ades_par_assoc:
  fixes P Q R :: "'s angelic_design" and j :: "'s merge"
  assumes "P is A" "Q is A" "R is A"
    and "P is A2" "Q is A2" "R is A2"
    and "\<And>s0 sL sR sThird sOut.
      (\<exists>sMid. merge_eval j s0 sL sR sMid \<and> merge_eval j s0 sMid sThird sOut) =
      (\<exists>sMid. merge_eval j s0 sR sThird sMid \<and> merge_eval j s0 sL sMid sOut)"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) =
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R))"
proof -
  have operands_H1: "P is H1" "Q is H1" "R is H1"
    using assms(1-3) by (simp_all add: A_healthy_components_iff)
  have pq: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
    by (rule ades_par_A_closure[OF operands_H1(1,2)])
  have qr: "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A"
    by (rule ades_par_A_closure[OF operands_H1(2,3)])
  have pq2: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
    by (rule ades_par_A2_closure[OF assms(1,2) assms(4,5)])
  have qr2: "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A2"
    by (rule ades_par_A2_closure[OF assms(2,3) assms(5,6)])
  show ?thesis
    by (simp only: ades_par_d2ac_ac2p[OF pq assms(3) pq2 assms(6)]
        ades_par_d2ac_ac2p[OF assms(1) qr assms(4) qr2]
        ades_par_ac2p[OF assms(1,2) assms(4,5)]
        ades_par_ac2p[OF assms(2,3) assms(5,6)]
        des_par_assoc_state[OF assms(7)])
qed

lemma ades_par_skip_assoc:
  assumes "P is A" "Q is A" "R is A" "P is A2" "Q is A2" "R is A2"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R) =
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R))"
  by (rule ades_par_assoc[OF assms]; simp add: skip_merge_eval)

subsection \<open>Skip Merge Example\<close>

text \<open>Skip requires sOut = s0, so its set lifting requires s0 in the final set.
\<close>

lemma lift_merge_skip_eval:
  "ades_merge_eval (lift_merge skip\<^sub>m) x p q out \<longleftrightarrow>
    (\<not> des_vars.ok\<^sub>v x \<or>
      (achoices.ac\<^sub>v (des_vars.more p) \<noteq> {} \<and>
       achoices.ac\<^sub>v (des_vars.more q) \<noteq> {} \<and>
       (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q \<longrightarrow> des_vars.ok\<^sub>v out) \<and>
       astate.s\<^sub>v (des_vars.more x) \<in> achoices.ac\<^sub>v (des_vars.more out)))"
  by (auto simp: lift_merge_def Let_def skip_merge_eval)

lemma lift_merge_skip_SymMerge: "lift_merge skip\<^sub>m is SymMerge"
  by (auto simp: SymMerge_ades lift_merge_skip_eval)

definition ades_bool_choice :: "bool \<Rightarrow> bool angelic_design" where
  [pred]: "ades_bool_choice sChoice \<equiv>
    (true \<turnstile>\<^sub>r (\<lambda>(s0, out). sChoice \<in> achoices.ac\<^sub>v out))"

lemma ades_bool_choice_eval:
  "ades_bool_choice sChoice (x,out) \<longleftrightarrow>
    (\<not> des_vars.ok\<^sub>v x \<or>
     (des_vars.ok\<^sub>v out \<and> sChoice \<in> achoices.ac\<^sub>v (des_vars.more out)))"
  by (simp add: ades_bool_choice_def; pred_auto)

lemma ades_bool_choice_healthy [closure]: "ades_bool_choice sChoice is A"
  by (rule Healthy_intro, rule ades_obs_ext;
      auto simp: A_obs ades_bool_choice_eval)

lemma ades_bool_choice_A2:
  "ades_bool_choice sChoice is A2"
  by (rule Healthy_intro, rule ades_obs_ext;
      auto simp: A2_obs ades_bool_choice_eval)

text \<open>Successful branches require termination and a final set containing the initial state.
  With Chaos on one branch, termination is unconstrained but the same state constraint remains.\<close>

lemma skip_completed_success:
  "(ades_bool_choice u \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> ades_bool_choice v)
    (ades_obs b s0 c Z) = (\<not>b \<or> (c \<and> s0 \<in> Z))"
proof -
  have bool_choice_H1: "ades_bool_choice k is H1" for k
    using ades_bool_choice_healthy[of k] by (simp add: A_healthy_components_iff)
  show ?thesis
    by (simp only: ades_par_eval[OF bool_choice_H1 bool_choice_H1]
        ades_par_raw_obs[OF ades_bool_choice_healthy ades_bool_choice_healthy
          ades_bool_choice_A2 ades_bool_choice_A2]
        ades_bool_choice_eval skip_merge_eval; auto)
qed

lemma skip_completed_failure:
  "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> ades_bool_choice v)
    (ades_obs b s0 c Z) = (\<not>b \<or> s0 \<in> Z)"
proof -
  have bool_choice_H1: "ades_bool_choice v is H1"
    using ades_bool_choice_healthy[of v] by (simp add: A_healthy_components_iff)
  have chaos_H1: "(true :: bool angelic_design) is H1"
    by (simp add: Healthy_def' H1_def; pred_auto)
  show ?thesis
    apply (simp only: ades_par_eval[OF chaos_H1 bool_choice_H1]
        ades_par_raw_eval choices_ex lift_merge_skip_eval ades_bool_choice_eval)
    apply (simp add: true_pred_def)
    by (cases b; cases s0; auto simp: ex_bool_eq intro!: exI[where x="{v}"])
qed

end
