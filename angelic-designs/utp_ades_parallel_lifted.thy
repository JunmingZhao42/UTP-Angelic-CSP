section \<open>Angelic Parallel and Ordinary Designs\<close>

theory utp_ades_parallel_lifted
  imports utp_ades_parallel
begin

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

lemma lift_merge_is_A0m: "lift_merge j is A0m"
  by (auto simp: A0m_healthy_iff A0_healthy_obs_iff lift_merge_obs[simplified]
      lift_merge_def Let_def)

lemma lift_merge_is_A1m: "lift_merge j is A1m"
  by (unfold A1m_healthy_iff; intro allI Healthy_intro; rule ades_obs_ext;
      auto simp: A1_obs lift_merge_def Let_def; blast)

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

lemma ades_par_lift_merge_obs:
  assumes "P is A" and "Q is A" and "P is A2" and "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 okOut Z) \<longleftrightarrow>
    (\<not> ok0 \<or> (\<exists>okL sL okR sR. \<exists>sOut\<in>Z.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      merge_eval j s0 sL sR sOut \<and> (okL \<and> okR \<longrightarrow> okOut)))"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1) assms(2) by (simp_all add: A_healthy_components_iff)
  show ?thesis
    using operands_H1
    apply (cases ok0; simp add: ades_par_eval choices_ex
        lift_merge_obs[simplified] H1_healthy_obs_iff)
    apply (rule iffI)
    subgoal
      using A2_nonempty_singleton[OF assms(1) assms(3)] A2_nonempty_singleton[OF assms(2) assms(4)]
      by metis
    subgoal by (fastforce intro: exI[where x="{_}"])
    done
qed

lemma lift_merge_ac2p:
  assumes "P is A" and "Q is A" and "P is A2" and "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) = ac2p P \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p Q"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1) assms(2) by (simp_all add: A_healthy_components_iff)
  have par_A: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) is A"
    by (rule ades_par_A_closure[OF operands_H1 lift_merge_is_A0m lift_merge_is_A1m])
  have obs: "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (\<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = okOut, \<dots> = sOut\<rparr>) =
      (ac2p P \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p Q) (\<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = okOut, \<dots> = sOut\<rparr>)"
    for ok0 s0 okOut sOut
    using operands_H1
    by (cases ok0; auto simp: ac2p_healthy_obs[OF A_is_PBMH_ades[OF par_A]]
        ades_par_lift_merge_obs[OF assms(1) assms(2) assms(3) assms(4)] ordinary_parallel_obs
        ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(1)]]
        ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(2)]] H1_healthy_obs_iff; blast)
  show ?thesis
    by (rule ext; metis obs des_vars.cases_scheme surj_pair)
qed

lemma ades_par_lift_merge_A2_closure:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) is A2"
  by (rule Healthy_intro, rule ades_obs_ext;
      simp only: A2_obs ades_par_lift_merge_obs[OF assms]; blast)


subsection \<open>A3-Completed Parallel from a State Merge\<close>

text \<open>Apply A3 after parallel. For H1-healthy operands, only empty final sets can change,
  and A0m/A1m give A closure. A- and A2-healthy operands give A2 closure.
  No A3m witness or H3 normality is required.\<close>

definition ades_par_lifted ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q =
    A3 (P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q)"

lemma ades_par_lift_merge_A_closure:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) is A"
  by (rule ades_par_A_closure[OF assms lift_merge_is_A0m lift_merge_is_A1m])

lemma ades_par_lifted_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_lifted_def
  by (rule A3_preserves_A[OF ades_par_lift_merge_A_closure[OF assms]])

lemma ades_par_lifted_A2_closure [closure]:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) is A2"
  unfolding ades_par_lifted_def
  by (rule A3_preserves_A2[OF ades_par_lift_merge_A2_closure[OF assms]])

lemma ades_par_lifted_A3_closure [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) is A3"
  by (simp add: ades_par_lifted_def Healthy_def' A3_idem)

lemma ades_par_lifted_eval:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 okOut Z) \<longleftrightarrow>
    ((P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 okOut Z) \<or>
      (Z = {} \<and> (\<forall>sOut.
        (P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 False {sOut}))))"
proof -
  have designs_H: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) is \<^bold>H"
    using ades_par_lift_merge_A_closure[OF assms]
      A_is_H[of "P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q"]
    by (simp add: Healthy_def')
  show ?thesis by (simp only: ades_par_lifted_def A3_obs_H[OF designs_H])
qed

lemma ades_par_lifted_nonempty:
  assumes "P is H1" "Q is H1" "Z \<noteq> {}"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 okOut Z) =
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 okOut Z)"
  by (simp only: ades_par_lifted_eval[OF assms(1,2)] assms(3); simp)

text \<open>The contract assumes H-healthiness, with no A2 or normality requirement.
  P_f s0 X and P_t s0 X fix initial ok to True and final ok to False/True;
  likewise for Q. The superscripts @{term "P\<^sup>f"} and @{term "P\<^sup>t"} set only final ok.
  M_j checks nonempty branch sets and the state merge.
  Fail covers failure of either branch, including both by H2; Finish uses P_t and Q_t.
  Pre excludes Fail at Z and at some singleton. For nonempty Z, excluding Fail at Z
  already gives the singleton condition. Post requires Finish while Pre holds.
  The quotes embed the HOL functions Fail and Finish, applied to the initial state
  and final choice set.\<close>

lemma ades_par_lifted_design:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
    and P_f P_t Q_f Q_t Fail Finish :: "'s \<Rightarrow> 's set \<Rightarrow> bool"
    and M_j :: "'s \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> bool"
    and Pre Post :: "'s angelic_rel"
  assumes "P is \<^bold>H" and "Q is \<^bold>H"
  defines "P_f \<equiv> \<lambda>s0 X. P (ades_obs True s0 False X)"
    and "P_t \<equiv> \<lambda>s0 X. P (ades_obs True s0 True X)"
    and "Q_f \<equiv> \<lambda>s0 Y. Q (ades_obs True s0 False Y)"
    and "Q_t \<equiv> \<lambda>s0 Y. Q (ades_obs True s0 True Y)"
    and "M_j \<equiv> \<lambda>s0 X Y Z. X \<noteq> {} \<and> Y \<noteq> {} \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z. merge_eval j s0 sL sR sOut)"
    and "Fail \<equiv> \<lambda>s0 Z. \<exists>X Y. M_j s0 X Y Z \<and>
      ((P_f s0 X \<and> Q_t s0 Y) \<or> (P_t s0 X \<and> Q_f s0 Y))"
    and "Finish \<equiv> \<lambda>s0 Z. \<exists>X Y. M_j s0 X Y Z \<and> P_t s0 X \<and> Q_t s0 Y"
    and "Pre \<equiv> (\<not> \<guillemotleft>Fail\<guillemotright> ($s\<^sup><) ($ac\<^sup>>) \<and> (\<exists>sOut. \<not> \<guillemotleft>Fail\<guillemotright> ($s\<^sup><) {sOut}))\<^sub>e"
    and "Post \<equiv> (\<guillemotleft>Finish\<guillemotright> ($s\<^sup><) ($ac\<^sup>>))\<^sub>e"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q = (Pre \<turnstile>\<^sub>r Post)"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1) assms(2) by (simp_all add: H_implies_H1)
  have operands_H2: "P is H2" "Q is H2"
    using assms(1) assms(2) by (simp_all add: H_implies_H2)
  have p_up: "P (ades_obs True s0 False X) \<Longrightarrow> P (ades_obs True s0 True X)" for s0 X
    using H2_obs[of P True s0 True X]
    by (simp only: Healthy_if[OF operands_H2(1)]; blast)
  have q_up: "Q (ades_obs True s0 False Y) \<Longrightarrow> Q (ades_obs True s0 True Y)" for s0 Y
    using H2_obs[of Q True s0 True Y]
    by (simp only: Healthy_if[OF operands_H2(2)]; blast)
  have started:
    "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (ades_obs True s0 okOut Z) \<longleftrightarrow>
      (\<exists>okL X okR Y. P (ades_obs True s0 okL X) \<and> Q (ades_obs True s0 okR Y) \<and>
        M_j s0 X Y Z \<and> (okL \<and> okR \<longrightarrow> okOut))" for s0 okOut Z
    by (simp only: ades_par_eval choices_ex lift_merge_obs[simplified] M_j_def; blast)
  have started_contract:
    "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (ades_obs True s0 okOut Z) \<longleftrightarrow>
      (Fail s0 Z \<or> (okOut \<and> Finish s0 Z))" for s0 okOut Z
    unfolding started Fail_def Finish_def P_f_def P_t_def Q_f_def Q_t_def
    using p_up q_up
    by (cases okOut; auto simp: ex_bool_eq)
  have raw_h1: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) is H1"
    using ades_par_lift_merge_A_closure[OF operands_H1]
    by (simp add: A_healthy_components_iff)
  have raw:
    "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>lift_merge j\<^esub> Q) (ades_obs ok0 s0 okOut Z) \<longleftrightarrow>
      (\<not>ok0 \<or> Fail s0 Z \<or> (okOut \<and> Finish s0 Z))" for ok0 s0 okOut Z
    using raw_h1 by (cases ok0; simp add: H1_healthy_obs_iff started_contract)
  have fail_upward: "Z \<subseteq> W \<Longrightarrow> Fail s0 Z \<Longrightarrow> Fail s0 W" for s0 Z W
    unfolding Fail_def M_j_def by (metis subset_eq)
  have all_fail: "(\<forall>sOut. Fail s0 {sOut}) \<Longrightarrow> Z \<noteq> {} \<Longrightarrow> Fail s0 Z" for s0 Z
  proof -
    assume every: "\<forall>sOut. Fail s0 {sOut}" and nonempty: "Z \<noteq> {}"
    obtain sOut where member: "sOut \<in> Z" using nonempty by blast
    show "Fail s0 Z"
      using fail_upward[of "{sOut}" Z s0] every member by auto
  qed
  show ?thesis
    unfolding Pre_def Post_def
    by (rule ades_obs_ext;
        simp only: ades_par_lifted_eval[OF operands_H1] raw; pred_auto; blast intro: all_fail)
qed

text \<open>For A- and A2-healthy operands, completed parallel equals ordinary parallel
  followed by d2ac. Both conversion laws hold for any state merge.\<close>

lemma ades_par_lifted_d2ac_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q =
    d2ac (ac2p P \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p Q)"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: A_healthy_components_iff)
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use assms(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    apply (rule ades_obs_ext)
    apply (simp only: ades_par_lifted_eval[OF operands_H1]
      ades_par_lift_merge_obs[OF assms] d2ac_healthy_obs[OF des_par_H_closure[OF designs_H]]
      ordinary_parallel_obs ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(1)]]
      ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(2)]])
    by blast
qed

lemma ades_par_lifted_d2ac:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "d2ac P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> d2ac Q = d2ac (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)"
  by (simp only: ades_par_lifted_d2ac_ac2p[OF d2ac_is_A d2ac_is_A d2ac_is_A2 d2ac_is_A2]
      ac2p_d2ac[OF assms(1), simplified comp_apply]
      ac2p_d2ac[OF assms(2), simplified comp_apply])

lemma ades_par_lifted_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) = ac2p P \<parallel>\<^sub>D\<^bsub>j\<^esub> ac2p Q"
proof -
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use assms(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    by (simp only: ades_par_lifted_d2ac_ac2p[OF assms]
        ac2p_d2ac[OF des_par_H_closure[OF designs_H], simplified comp_apply])
qed

lemma ades_par_lifted_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q1) \<sqsubseteq>
    (P2 \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_lifted_def
  by (rule A3_mono, rule ades_par_mono[OF assms]; simp)

lemma ades_par_lifted_comm:
  assumes "lift_merge j is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> P)"
  by (simp only: ades_par_lifted_def ades_par_comm[OF assms])

text \<open>Completion loses ordinary disjunction distribution. Associativity follows from
  associative state merging at the same initial state, with A- and A2-healthy
  operands. No H3 or extra A3 assumption is needed.\<close>

subsubsection \<open>Associativity of Completed Parallel\<close>

lemma ades_par_lifted_assoc:
  fixes P Q R :: "'s angelic_design" and j :: "'s merge"
  assumes "P is A" "Q is A" "R is A"
    and "P is A2" "Q is A2" "R is A2"
    and "\<And>s0 sL sR sThird sOut.
      (\<exists>sMid. merge_eval j s0 sL sR sMid \<and> merge_eval j s0 sMid sThird sOut) =
      (\<exists>sMid. merge_eval j s0 sR sThird sMid \<and> merge_eval j s0 sL sMid sOut)"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> R) =
    (P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> R))"
proof -
  have operands_H1: "P is H1" "Q is H1" "R is H1"
    using assms(1-3) by (simp_all add: A_healthy_components_iff)
  have pq: "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) is A"
    by (rule ades_par_lifted_A_closure[OF operands_H1(1,2)])
  have qr: "(Q \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> R) is A"
    by (rule ades_par_lifted_A_closure[OF operands_H1(2,3)])
  have pq2: "(P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> Q) is A2"
    by (rule ades_par_lifted_A2_closure[OF assms(1,2) assms(4,5)])
  have qr2: "(Q \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>j\<^esub> R) is A2"
    by (rule ades_par_lifted_A2_closure[OF assms(2,3) assms(5,6)])
  show ?thesis
    by (simp only: ades_par_lifted_d2ac_ac2p[OF pq assms(3) pq2 assms(6)]
        ades_par_lifted_d2ac_ac2p[OF assms(1) qr assms(4) qr2]
        ades_par_lifted_ac2p[OF assms(1,2) assms(4,5)]
        ades_par_lifted_ac2p[OF assms(2,3) assms(5,6)]
        des_par_assoc_state[OF assms(7)])
qed

lemma ades_par_lifted_skip_assoc:
  assumes "P is A" "Q is A" "R is A" "P is A2" "Q is A2" "R is A2"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>skip\<^sub>m\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>skip\<^sub>m\<^esub> R) =
    (P \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>skip\<^sub>m\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>skip\<^sub>m\<^esub> R))"
  by (rule ades_par_lifted_assoc[OF assms]; simp add: skip_merge_eval)

subsection \<open>Skip Merge Example\<close>

text \<open>Skip requires sOut = s0, so its set lifting requires s0 in the final set.
  A0m and A1m follow from the general lifting lemmas.\<close>

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

lemma bool_choice_H1: "ades_bool_choice k is H1"
  using ades_bool_choice_healthy[of k] by (simp add: A_healthy_components_iff)

lemma skip_completed_success:
  "(ades_bool_choice u \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>skip\<^sub>m\<^esub> ades_bool_choice v)
    (ades_obs b s0 c Z) = (\<not>b \<or> (c \<and> s0 \<in> Z))"
  by (simp only: ades_par_lifted_eval[OF bool_choice_H1 bool_choice_H1]
      ades_par_lift_merge_obs[OF ades_bool_choice_healthy ades_bool_choice_healthy
        ades_bool_choice_A2 ades_bool_choice_A2]
      ades_bool_choice_eval skip_merge_eval; auto)

lemma chaos_H1: "(true :: 's angelic_design) is H1"
  by (simp add: Healthy_def' H1_def; pred_auto)

lemma skip_completed_failure:
  "(true \<parallel>\<^sub>A\<^sub>D\<^sup>3\<^bsub>skip\<^sub>m\<^esub> ades_bool_choice v)
    (ades_obs b s0 c Z) = (\<not>b \<or> s0 \<in> Z)"
  apply (simp only: ades_par_lifted_eval[OF chaos_H1 bool_choice_H1]
      ades_par_eval choices_ex lift_merge_skip_eval ades_bool_choice_eval)
  apply (simp add: true_pred_def)
  by (cases b; cases s0; auto simp: ex_bool_eq intro!: exI[where x="{v}"])

end
