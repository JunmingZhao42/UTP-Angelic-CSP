section \<open>AD Parallel with a Lifted State Merge\<close>

theory utp_ades_parallel_lift
  imports utp_ades_parallel_laws
begin

text \<open>Lifting a state merge to AD, the AD parallel operator, and its
  correspondence with designs.\<close>

subsection \<open>Lifting a State Merge\<close>

subsubsection \<open>Construction\<close>

text \<open>The AD merge lifts the design merge of @{term j} through choice sets.\<close>

(* merge_ades j = H3m (H1m (ABm (ac'_lift_merge (merge_des_raw j)))) *)
definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "merge_ades j \<equiv> H3m (H1m (ABm (ac'_lift_merge (merge_des_raw j))))"

lemma merge_ades_completion [simp]: "merge_ades j ;; II\<^sub>D = merge_ades j"
  by (simp add: merge_ades_def H3m_def seqr_assoc)

subsubsection \<open>Evaluation\<close>

text \<open>Started merges require nonempty branch sets and a witness for every state pair.
  Both branches terminating requires witnesses in the final set; divergence releases it.\<close>

lemma merge_ades_obs:
  "ades_merge_obs (merge_ades j) ok0 s0 okL acL okR acR ok' ac' \<longleftrightarrow>
    (\<not> ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow>
        (ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
  unfolding merge_ades_def
  apply (simp only: ac'_lift_merge_completion_obs)
  apply (simp add: merge_des_raw_def)
  by (cases ok0; cases okL; cases okR; cases ok'; simp_all; blast intro: exI[where x=UNIV])

lemma merge_ades_design_lift:
  "merge_ades j = H3m (H1m (ABm (ac'_lift_merge (merge_des j))))"
  apply (rule ades_merge_ext)
  apply (rename_tac ok0 s0 okL acL okR acR ok' ac')
  apply (simp only: merge_ades_obs ac'_lift_merge_completion_obs merge_des_expand simp_thms)
  by (case_tac "okL \<and> okR"; auto; blast intro: exI[where x=UNIV])

lemma merge_ades_unfold:
  "merge_ades j = (\<lambda>(m,out).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        acL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        acR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        ac' = achoices.ac\<^sub>v (des_vars.more out)
    in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
       (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)
          \<longrightarrow> (des_vars.ok\<^sub>v out \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
  by (rule ades_merge_ext; simp add: merge_ades_obs[simplified] Let_def)

subsubsection \<open>Healthiness and Symmetry\<close>

text \<open>The lifted merge satisfies all the healthiness conditions above, for every j.\<close>

lemma merge_ades_is_H1m [closure]: "merge_ades j is H1m"
  by (simp add: Healthy_def' merge_ades_def H3m_def H1m_def; pred_auto)

lemma merge_ades_is_H2m [closure]: "merge_ades j is H2m"
  by (simp add: Healthy_def' H2m_def merge_ades_def H3m_def seqr_assoc skip_d_absorb_J_1)

lemma merge_ades_is_HDm [closure]: "merge_ades j is HDm"
  by (rule HDm_intro[OF merge_ades_is_H1m merge_ades_is_H2m])

lemma merge_ades_is_H3m [closure]: "merge_ades j is H3m"
  by (simp add: Healthy_def' merge_ades_def H3m_Idempotent[unfolded Idempotent_def])

lemma merge_ades_is_A0m [closure]: "merge_ades j is A0m"
  unfolding Healthy_def'
  by (rule ades_merge_ext)
     (auto simp: A0m_eval merge_ades_obs[simplified] Let_def; blast)

lemma merge_ades_is_A1m [closure]: "merge_ades j is A1m"
  unfolding Healthy_def'
  by (rule ades_merge_ext)
     (auto simp: A1m_eval merge_ades_obs[simplified] Let_def; blast)

lemma merge_ades_is_ADm [closure]: "merge_ades j is ADm"
  by (simp add: ADm_healthy_iff merge_ades_is_A0m merge_ades_is_A1m)

lemma merge_ades_is_A2m [closure]: "merge_ades j is A2m"
  unfolding Healthy_def'
  by (rule ades_merge_ext) (auto simp: A2m_obs[simplified] merge_ades_obs[simplified])

lemma merge_ades_SymMerge [closure]:
  assumes "j is SymMerge"
  shows "merge_ades j is SymMerge"
  using assms
  by (simp add: Healthy_def' fun_eq_iff merge_ades_unfold; pred_auto; blast)

subsection \<open>AD Parallel\<close>

subsubsection \<open>Definition and Evaluation\<close>

definition ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^bsub>merge_ades j\<^esub> Q"

text \<open>H1 handles unstarted observations; A2 reduces nonempty branch sets to singleton witnesses.\<close>

lemma ades_par_obs_A2:
  fixes P Q :: "'s angelic_design"
  assumes "P is A2" "Q is A2" "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not>ok0 \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> (\<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
proof -
  have pick: "\<exists>x\<in>X. R (ades_obs True s0 okL {x})"
    if "R is A2" "X \<noteq> {}" "R (ades_obs True s0 okL X)" for R :: "'s angelic_design" and okL X
  proof -
    have "R (ades_obs True s0 okL Y) \<longleftrightarrow>
        R (ades_obs True s0 okL {}) \<or> (\<exists>y\<in>Y. R (ades_obs True s0 okL {y}))" for Y
      using A2_obs[of R True s0 okL Y] by (simp only: Healthy_if[OF that(1)])
    then show ?thesis
      using that(2,3) by blast
  qed
  show ?thesis
    apply (cases ok0; simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified]
        assms(3,4)[unfolded H1_healthy_obs_iff])
    apply (rule iffI)
    subgoal using pick[OF assms(1)] pick[OF assms(2)] by metis
    subgoal by (fastforce intro: exI[where x="{_}"])
    done
qed

lemma ades_par_obs:
  fixes P Q :: "'s angelic_design"
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not> ok0 \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> (\<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: A_healthy_components_iff)
  show ?thesis
    by (rule ades_par_obs_A2[OF assms(3,4) operands_H1])
qed

lemma ades_par_normalise_A:
  assumes "P is A2" "Q is A2" "P is H1" "Q is H1"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q"
  by (rule ades_obs_ext;
      simp add: ades_par_obs_A2[OF assms]
        ades_par_obs_A2[OF A_preserves_A2[OF assms(1)] A_preserves_A2[OF assms(2)] A_is_H1[folded Healthy_def'] A_is_H1[folded Healthy_def']]
        A_obs_A2[OF assms(1)] A_obs_A2[OF assms(2)] ex_bool_eq; blast)

lemma ades_par_eval:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR.
      P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      (\<not>ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (okL \<and> okR \<longrightarrow> (ok' \<and>
          (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s'))))))"
  by (simp add: ades_par_def
      par_by_merge_eval choices_ex merge_ades_obs[simplified])

subsubsection \<open>Healthiness Closure\<close>

lemma ades_par_A0_closure [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0"
  unfolding ades_par_def
  by (rule A0_par_by_merge[OF merge_ades_is_A0m])

lemma ades_par_A1_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A1"
  unfolding ades_par_def
  by (rule A1_par_by_merge[OF assms merge_ades_is_A1m])

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_def
  by (rule A_par_by_merge[OF assms merge_ades_is_ADm])

lemma ades_par_A2_closure [closure]:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  unfolding ades_par_def
  by (rule A2_par_by_merge[OF assms merge_ades_is_A2m])

lemma ades_par_A3_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  unfolding ades_par_def
  by (rule A3_par_by_merge[OF assms merge_ades_is_H1m merge_ades_is_H3m])

subsubsection \<open>Correspondence with Designs\<close>

text \<open>For A- and A2-healthy operands, ac2p and d2ac preserve parallel by the
  lift of an HDm- and H3m-healthy design merge.\<close>

lemma ades_par_d2ac_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = d2ac ((ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q))"
  unfolding ades_par_def merge_ades_design_lift
  by (rule ades_par_by_merge_d2ac_ac2p[OF assms merge_des_is_HDm merge_des_is_H3m refl])

lemma ades_par_d2ac:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(d2ac P) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac Q) = d2ac (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)"
  by (simp only: ades_par_d2ac_ac2p[OF d2ac_is_A d2ac_is_A d2ac_is_A2 d2ac_is_A2]
      ac2p_d2ac[OF assms(1), simplified comp_apply]
      ac2p_d2ac[OF assms(2), simplified comp_apply])

lemma ades_par_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q)"
  unfolding ades_par_def
  by (rule ades_par_by_merge_ac2p[OF assms merge_des_is_HDm merge_des_is_H3m merge_ades_design_lift])

lemma ades_par_ac2p_d2ac:
  assumes "D is \<^bold>H" "E is \<^bold>H"
  shows "D \<parallel>\<^sub>D\<^bsub>j\<^esub> E = ac2p ((d2ac D) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac E))"
  by (simp only: ades_par_d2ac[OF assms]
      ac2p_d2ac[OF des_par_H_closure[OF H_implies_H1[OF assms(1)] H_implies_H1[OF assms(2)]], simplified comp_apply])

subsubsection \<open>Monotonicity\<close>

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1) \<sqsubseteq> (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_def
  using assms by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)

subsubsection \<open>Zero Laws\<close>

text \<open>A nonterminating branch observation releases the output guarantee.
  Chaos in both branches therefore yields Chaos whenever the state merge has
  some merged state at every initial state.\<close>

lemma ades_par_chaos:
  assumes "\<And>s0. \<exists>sL sR s'. merge_eval j s0 sL sR s'"
  shows "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true :: 's angelic_design) = true"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' X
  obtain sL sR s' where witness: "merge_eval j s0 sL sR s'"
    using assms by blast
  have started: "\<exists>okL acL okR acR. acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow>
        (ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>X. merge_eval j s0 sL sR s')))"
    by (rule exI[of _ False], rule exI[of _ "{sL}"], rule exI[of _ False],
        rule exI[of _ "{sR}"]) (use witness in blast)
  show "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true :: 's angelic_design) (ades_obs ok0 s0 ok' X) =
    (true :: 's angelic_design) (ades_obs ok0 s0 ok' X)"
    using started
    by (simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified] true_pred_def)
qed

lemma ades_par_miracle:
  assumes "P is H1"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>A\<^sub>D"
        "\<^bold>\<top>\<^sub>A\<^sub>D \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>D"
proof -
  have miracle: "(A false :: 's angelic_design) = \<top>\<^sub>D"
    by (rule ades_obs_ext; simp add: A_obs top_d_not_ok; pred_simp)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>A\<^sub>D"
       "\<^bold>\<top>\<^sub>A\<^sub>D \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>D"
    unfolding miracle ades_par_def
    by (rule par_by_merge_miracle[OF assms merge_ades_is_H1m])+
qed

subsubsection \<open>Commutativity\<close>

lemma ades_par_comm:
  assumes "j is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P)"
  unfolding ades_par_def
  by (rule par_by_merge_comm[OF merge_ades_SymMerge[OF assms]])

subsubsection \<open>Associativity\<close>

text \<open>Associativity of the design images transfers to the lifted merge.\<close>

lemma ades_lift_par_assoc_transfer:
  fixes M :: "'s des_merge"
  assumes ops: "P is A" "Q is A" "R is A" "P is A2" "Q is A2" "R is A2"
    and merge: "M is HDm" "M is H3m"
    and ordinary: "(ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) \<parallel>\<^bsub>M\<^esub> ac2p R = ac2p P \<parallel>\<^bsub>M\<^esub> (ac2p Q \<parallel>\<^bsub>M\<^esub> ac2p R)"
  shows "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R =
    P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> (Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R)"
proof -
  have pq: "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) is A" "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) is A2"
    and qr: "(Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R) is A" "(Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R) is A2"
    by (simp_all only: ades_par_by_merge_d2ac_ac2p[OF ops(1,2,4,5) merge refl]
        ades_par_by_merge_d2ac_ac2p[OF ops(2,3,5,6) merge refl] d2ac_is_A d2ac_is_A2)
  show ?thesis
    by (simp only: ades_par_by_merge_d2ac_ac2p[OF pq(1) ops(3) pq(2) ops(6) merge refl]
        ades_par_by_merge_d2ac_ac2p[OF ops(1) qr(1) ops(4) qr(2) merge refl]
        ades_par_by_merge_ac2p[OF ops(1,2,4,5) merge refl] ades_par_by_merge_ac2p[OF ops(2,3,5,6) merge refl]
        ordinary)
qed

lemma A_ac2p_NDD:
  assumes "P is A" "P is NDAD"
  shows "ac2p P is NDD"
proof -
  have "ac2p (A P) is NDD"
    using assms(2) unfolding NDD_healthy_iff preD_true_iff NDAD_healthy_obs_iff
    by (auto simp: ac2p_def A_PBMH_ades A_obs StateII_def)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)])
qed

text \<open>For H1 and A2 operands, AD parallel by @{term j} first normalises the
  operands with @{const A}.\<close>

lemma A_preserves_NDAD:
  assumes "P is A2" "P is NDAD"
  shows "A P is NDAD"
  using assms(2) unfolding NDAD_healthy_obs_iff
  by (simp add: A_obs_A2[OF assms(1)]; blast)

lemma ades_par_normalise_A3:
  assumes ops: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R"
    "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
proof -
  have pq: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A" "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2" "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
    and qr: "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A2" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is H1"
    using ades_par_A_closure[OF h1(1,2)] ades_par_A2_closure[OF ops(1,2)]
      ades_par_A_closure[OF h1(2,3)] ades_par_A2_closure[OF ops(2,3)]
    by (simp_all add: A_healthy_components_iff)
  show "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R"
    apply (subst ades_par_normalise_A[OF pq(2) ops(3) pq(3) h1(3)])
    apply (subst Healthy_if[OF pq(1)])
    by (subst ades_par_normalise_A[OF ops(1,2) h1(1,2)], rule refl)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
    apply (subst ades_par_normalise_A[OF ops(1) qr(2) h1(1) qr(3)])
    apply (subst Healthy_if[OF qr(1)])
    by (subst ades_par_normalise_A[OF ops(2,3) h1(2,3)], rule refl)
qed

lemma ades_par_assoc:
  fixes j :: "'s merge"
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and merge: "j is SymMerge" "AssocMerge j" "mergeable j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have a: "A S is A" for S :: "'s angelic_design"
    by (simp add: Healthy_def' A_idem)
  show ?thesis
    unfolding ades_par_normalise_A3[OF operands h1]
    unfolding ades_par_def merge_ades_design_lift
    by (rule ades_lift_par_assoc_transfer[OF a a a A_preserves_A2[OF operands(1)]
          A_preserves_A2[OF operands(2)] A_preserves_A2[OF operands(3)]
          merge_des_is_HDm merge_des_is_H3m des_par_assoc[OF merge]])
qed

lemma ades_par_assoc_nd:
  fixes j :: "'s merge"
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and nondiv: "P is NDAD" "Q is NDAD" "R is NDAD"
      and merge: "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have a: "A S is A" for S :: "'s angelic_design"
    by (simp add: Healthy_def' A_idem)
  show ?thesis
    unfolding ades_par_normalise_A3[OF operands h1]
    unfolding ades_par_def merge_ades_design_lift
    by (rule ades_lift_par_assoc_transfer[OF a a a A_preserves_A2[OF operands(1)]
          A_preserves_A2[OF operands(2)] A_preserves_A2[OF operands(3)]
          merge_des_is_HDm merge_des_is_H3m
          des_par_assoc_nd[OF
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(1) nondiv(1)]]
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(2) nondiv(2)]]
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(3) nondiv(3)]] merge]])
qed

text \<open>For a deterministic (Functional) merge we get associativity for all operands,
  without A2 or nondivergence: (P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R).
  At a started prior, P \<parallel> Q diverges when one side diverges and the other has an
  observation; otherwise it offers the merges of every pair of offered states.\<close>

context
begin

(* P may diverge from s0 with a nonempty set *)
private definition div_at :: "'s angelic_design \<Rightarrow> 's \<Rightarrow> bool" where
  "div_at P s0 \<equiv> (\<exists>X. X \<noteq> {} \<and> P (ades_obs True s0 False X))"

(* P terminates from s0 offering the nonempty set X *)
private definition term_at :: "'s angelic_design \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "term_at P s0 X \<equiv> X \<noteq> {} \<and> P (ades_obs True s0 True X)"

(* P has some started observation with a nonempty set *)
private definition obs_at :: "'s angelic_design \<Rightarrow> 's \<Rightarrow> bool" where
  "obs_at P s0 \<equiv> (\<exists>ok' X. X \<noteq> {} \<and> P (ades_obs True s0 ok' X))"

private lemma obs_at_iff: "obs_at P s0 \<longleftrightarrow> div_at P s0 \<or> (\<exists>X. term_at P s0 X)"
proof
  assume "obs_at P s0"
  then obtain ok' X where h: "X \<noteq> {}" "P (ades_obs True s0 ok' X)" unfolding obs_at_def by blast
  show "div_at P s0 \<or> (\<exists>X. term_at P s0 X)"
  proof (cases ok')
    case True
    then have "term_at P s0 X" using h unfolding term_at_def by simp
    then show ?thesis by (intro disjI2 exI)
  next
    case False
    then have "div_at P s0" using h unfolding div_at_def by (intro exI[where x=X]) simp
    then show ?thesis by (rule disjI1)
  qed
next
  assume "div_at P s0 \<or> (\<exists>X. term_at P s0 X)"
  then show "obs_at P s0"
  proof
    assume "div_at P s0"
    then obtain X where "X \<noteq> {}" "P (ades_obs True s0 False X)" unfolding div_at_def by blast
    then show "obs_at P s0" unfolding obs_at_def by (intro exI[where x=False] exI[where x=X]) simp
  next
    assume "\<exists>X. term_at P s0 X"
    then obtain X where "X \<noteq> {}" "P (ades_obs True s0 True X)" unfolding term_at_def by blast
    then show "obs_at P s0" unfolding obs_at_def by (intro exI[where x=True] exI[where x=X]) simp
  qed
qed

(* both branches start; a divergent pair releases everything *)
private abbreviation div_pair :: "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's \<Rightarrow> bool" where
  "div_pair P Q s0 \<equiv> (div_at P s0 \<and> obs_at Q s0) \<or> (obs_at P s0 \<and> div_at Q s0)"

private lemma par_obs_raw:
  fixes j :: "'s merge" and f :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  assumes f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR. P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      (ok0 \<longrightarrow> acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac'))))"
  by (cases ok0; simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified] f;
      blast)

private lemma par_obs_unstarted:
  fixes j :: "'s merge" and f :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  assumes f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs False s0 ok' ac') \<longleftrightarrow>
    (\<exists>k X. P (ades_obs False s0 k X)) \<and> (\<exists>k X. Q (ades_obs False s0 k X))"
  by (simp only: par_obs_raw[OF f]) blast

private lemma par_obs_started:
  fixes j :: "'s merge" and f :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  assumes f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 ok' ac') \<longleftrightarrow>
    div_pair P Q s0 \<or>
    (ok' \<and> (\<exists>acL acR. term_at P s0 acL \<and> term_at Q s0 acR \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac')))"
  (is "_ \<longleftrightarrow> ?R")
proof (simp only: par_obs_raw[OF f] simp_thms, rule iffI)
  assume "\<exists>okL acL okR acR. P (ades_obs True s0 okL acL) \<and> Q (ades_obs True s0 okR acR) \<and>
      acL \<noteq> {} \<and> acR \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac'))"
  then obtain okL acL okR acR where hP: "P (ades_obs True s0 okL acL)" and hQ: "Q (ades_obs True s0 okR acR)"
    and ne1: "acL \<noteq> {}" and ne2: "acR \<noteq> {}"
    and m: "okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac')"
    by blast
  have neP: "obs_at P s0" unfolding obs_at_def by (intro exI[where x=okL] exI[where x=acL] conjI ne1 hP)
  have neQ: "obs_at Q s0" unfolding obs_at_def by (intro exI[where x=okR] exI[where x=acR] conjI ne2 hQ)
  show ?R
  proof (cases okL)
    case False
    then have "div_at P s0" unfolding div_at_def using hP ne1 by (intro exI[where x=acL]) simp
    then show ?R using neQ by blast
  next
    case okl: True
    show ?R
    proof (cases okR)
      case False
      then have "div_at Q s0" unfolding div_at_def using hQ ne2 by (intro exI[where x=acR]) simp
      then show ?R using neP by blast
    next
      case True
      have "term_at P s0 acL" "term_at Q s0 acR" unfolding term_at_def using okl True hP hQ ne1 ne2 by simp_all
      moreover have "ok'" "\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac'" using m okl True by simp_all
      ultimately show ?R by (intro disjI2 conjI exI[where x=acL] exI[where x=acR]) simp_all
    qed
  qed
next
  assume r: ?R
  show "\<exists>okL acL okR acR. P (ades_obs True s0 okL acL) \<and> Q (ades_obs True s0 okR acR) \<and>
      acL \<noteq> {} \<and> acR \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac'))"
  proof -
    { assume "div_at P s0" "obs_at Q s0"
      then obtain X okR Y where "X \<noteq> {}" "P (ades_obs True s0 False X)"
          "Y \<noteq> {}" "Q (ades_obs True s0 okR Y)" unfolding div_at_def obs_at_def by blast
      then have ?thesis by (intro exI[where x=False] exI[where x=X] exI[where x=okR] exI[where x=Y]) simp }
    moreover
    { assume "obs_at P s0" "div_at Q s0"
      then obtain X okL Y where "Y \<noteq> {}" "Q (ades_obs True s0 False Y)"
          "X \<noteq> {}" "P (ades_obs True s0 okL X)" unfolding div_at_def obs_at_def by blast
      then have ?thesis by (intro exI[where x=okL] exI[where x=X] exI[where x=False] exI[where x=Y]) simp }
    moreover
    { assume "ok'" "\<exists>acL acR. term_at P s0 acL \<and> term_at Q s0 acR \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac')"
      then obtain acL acR where h: "term_at P s0 acL" "term_at Q s0 acR" "\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> ac'" by blast
      then have ?thesis using \<open>ok'\<close> unfolding term_at_def
        by (intro exI[where x=True] exI[where x=acL] exI[where x=True] exI[where x=acR]) simp }
    ultimately show ?thesis using r by blast
  qed
qed

private lemma ex_nonempty_set: "(\<exists>X::'a set. X \<noteq> {} \<and> D) \<longleftrightarrow> D"
  by (auto intro: exI[where x=UNIV])

private lemma div_at_par:
  fixes j :: "'s merge" and f :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  assumes f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
  shows "div_at (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) s0 \<longleftrightarrow> div_pair P Q s0"
  by (simp only: div_at_def[of "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"] par_obs_started[OF f] simp_thms ex_nonempty_set)

private lemma term_at_par:
  fixes j :: "'s merge" and f :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  assumes f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
  shows "term_at (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) s0 Y \<longleftrightarrow> Y \<noteq> {} \<and>
    (div_pair P Q s0 \<or> (\<exists>acL acR. term_at P s0 acL \<and> term_at Q s0 acR \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> Y)))"
  by (simp only: term_at_def[of "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"] par_obs_started[OF f] simp_thms)

private lemma obs_at_par:
  fixes j :: "'s merge" and f :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  assumes f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
  shows "obs_at (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) s0 \<longleftrightarrow> div_pair P Q s0 \<or> (\<exists>acL acR. term_at P s0 acL \<and> term_at Q s0 acR)"
  (is "_ \<longleftrightarrow> ?D \<or> ?T")
proof (simp only: obs_at_iff[of "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"] div_at_par[OF f] term_at_par[OF f], rule iffI)
  assume "?D \<or> (\<exists>Y. Y \<noteq> {} \<and> (?D \<or> (\<exists>acL acR. term_at P s0 acL \<and> term_at Q s0 acR \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> Y))))"
  then show "?D \<or> ?T" by blast
next
  assume "?D \<or> ?T"
  then show "?D \<or> (\<exists>Y. Y \<noteq> {} \<and> (?D \<or> (\<exists>acL acR. term_at P s0 acL \<and> term_at Q s0 acR \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> Y))))"
  proof
    assume ?T
    then have h: "\<exists>acL acR. term_at P s0 acL \<and> term_at Q s0 acR \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. f s0 sL sR \<in> UNIV)"
      by simp
    show ?thesis by (rule disjI2, rule exI[where x=UNIV]) (use h in simp)
  qed (rule disjI1)
qed

private lemma flat_left:
  assumes neP: "\<And>X. TP X \<Longrightarrow> X \<noteq> {}" and neQ: "\<And>X. TQ X \<Longrightarrow> X \<noteq> {}"
  shows "(\<exists>Y XC. (Y \<noteq> {} \<and> (D \<or> (\<exists>XL XR. TP XL \<and> TQ XR \<and> (\<forall>a\<in>XL. \<forall>b\<in>XR. f a b \<in> Y)))) \<and>
      TR XC \<and> (\<forall>u\<in>Y. \<forall>c\<in>XC. f u c \<in> Z)) \<longleftrightarrow>
   (D \<and> (\<exists>XC. TR XC \<and> (\<exists>Y. Y \<noteq> {} \<and> (\<forall>u\<in>Y. \<forall>c\<in>XC. f u c \<in> Z)))) \<or>
   (\<exists>XL XR XC. TP XL \<and> TQ XR \<and> TR XC \<and>
      (\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f (f a b) c \<in> Z))"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain Y XC where y: "Y \<noteq> {}"
    and dd: "D \<or> (\<exists>XL XR. TP XL \<and> TQ XR \<and> (\<forall>a\<in>XL. \<forall>b\<in>XR. f a b \<in> Y))"
    and tr: "TR XC" and z: "\<forall>u\<in>Y. \<forall>c\<in>XC. f u c \<in> Z"
    by blast
  from dd show ?R
  proof
    assume "D"
    with y tr z show ?R by (intro disjI1 conjI exI[where x=XC]) (auto intro!: exI[where x=Y])
  next
    assume "\<exists>XL XR. TP XL \<and> TQ XR \<and> (\<forall>a\<in>XL. \<forall>b\<in>XR. f a b \<in> Y)"
    then obtain XL XR where "TP XL" "TQ XR" and img: "\<forall>a\<in>XL. \<forall>b\<in>XR. f a b \<in> Y" by blast
    moreover have "\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f (f a b) c \<in> Z"
      using img z by simp
    ultimately show ?R using tr by (intro disjI2 exI[where x=XL] exI[where x=XR] exI[where x=XC] conjI)
  qed
next
  assume ?R
  then show ?L
  proof
    assume "D \<and> (\<exists>XC. TR XC \<and> (\<exists>Y. Y \<noteq> {} \<and> (\<forall>u\<in>Y. \<forall>c\<in>XC. f u c \<in> Z)))"
    then obtain XC Y where "D" "TR XC" "Y \<noteq> {}" "\<forall>u\<in>Y. \<forall>c\<in>XC. f u c \<in> Z" by blast
    then show ?L by (intro exI[where x=Y] exI[where x=XC] conjI disjI1)
  next
    assume "\<exists>XL XR XC. TP XL \<and> TQ XR \<and> TR XC \<and>
      (\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f (f a b) c \<in> Z)"
    then obtain XL XR XC where h: "TP XL" "TQ XR" "TR XC"
      and t: "\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f (f a b) c \<in> Z" by blast
    obtain a0 b0 where "a0 \<in> XL" "b0 \<in> XR" using neP[OF h(1)] neQ[OF h(2)] by blast
    then have img_ne: "{f a b | a b. a \<in> XL \<and> b \<in> XR} \<noteq> {}" by blast
    have img: "\<forall>a\<in>XL. \<forall>b\<in>XR. f a b \<in> {f a b | a b. a \<in> XL \<and> b \<in> XR}" by blast
    have z: "\<forall>u\<in>{f a b | a b. a \<in> XL \<and> b \<in> XR}. \<forall>c\<in>XC. f u c \<in> Z" using t by blast
    show ?L
      by (rule exI[where x="{f a b | a b. a \<in> XL \<and> b \<in> XR}"], rule exI[where x=XC])
         (use img_ne img z h in blast)
  qed
qed

private lemma flat_right:
  assumes neQ: "\<And>X. TQ X \<Longrightarrow> X \<noteq> {}" and neR: "\<And>X. TR X \<Longrightarrow> X \<noteq> {}"
  shows "(\<exists>XL Y. TP XL \<and> (Y \<noteq> {} \<and> (D \<or> (\<exists>XR XC. TQ XR \<and> TR XC \<and> (\<forall>b\<in>XR. \<forall>c\<in>XC. f b c \<in> Y)))) \<and>
      (\<forall>a\<in>XL. \<forall>v\<in>Y. f a v \<in> Z)) \<longleftrightarrow>
   (D \<and> (\<exists>XL. TP XL \<and> (\<exists>Y. Y \<noteq> {} \<and> (\<forall>a\<in>XL. \<forall>v\<in>Y. f a v \<in> Z)))) \<or>
   (\<exists>XL XR XC. TP XL \<and> TQ XR \<and> TR XC \<and>
      (\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f a (f b c) \<in> Z))"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  then obtain XL Y where tp: "TP XL" and y: "Y \<noteq> {}"
    and dd: "D \<or> (\<exists>XR XC. TQ XR \<and> TR XC \<and> (\<forall>b\<in>XR. \<forall>c\<in>XC. f b c \<in> Y))"
    and z: "\<forall>a\<in>XL. \<forall>v\<in>Y. f a v \<in> Z"
    by blast
  from dd show ?R
  proof
    assume "D"
    with y tp z show ?R by (intro disjI1 conjI exI[where x=XL]) (auto intro!: exI[where x=Y])
  next
    assume "\<exists>XR XC. TQ XR \<and> TR XC \<and> (\<forall>b\<in>XR. \<forall>c\<in>XC. f b c \<in> Y)"
    then obtain XR XC where "TQ XR" "TR XC" and img: "\<forall>b\<in>XR. \<forall>c\<in>XC. f b c \<in> Y" by blast
    moreover have "\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f a (f b c) \<in> Z"
      using img z by simp
    ultimately show ?R using tp by (intro disjI2 exI[where x=XL] exI[where x=XR] exI[where x=XC] conjI)
  qed
next
  assume ?R
  then show ?L
  proof
    assume "D \<and> (\<exists>XL. TP XL \<and> (\<exists>Y. Y \<noteq> {} \<and> (\<forall>a\<in>XL. \<forall>v\<in>Y. f a v \<in> Z)))"
    then obtain XL Y where "D" "TP XL" "Y \<noteq> {}" "\<forall>a\<in>XL. \<forall>v\<in>Y. f a v \<in> Z" by blast
    then show ?L by (intro exI[where x=XL] exI[where x=Y] conjI disjI1)
  next
    assume "\<exists>XL XR XC. TP XL \<and> TQ XR \<and> TR XC \<and>
      (\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f a (f b c) \<in> Z)"
    then obtain XL XR XC where h: "TP XL" "TQ XR" "TR XC"
      and t: "\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>c\<in>XC. f a (f b c) \<in> Z" by blast
    obtain b0 c0 where "b0 \<in> XR" "c0 \<in> XC" using neQ[OF h(2)] neR[OF h(3)] by blast
    then have img_ne: "{f b c | b c. b \<in> XR \<and> c \<in> XC} \<noteq> {}" by blast
    have img: "\<forall>b\<in>XR. \<forall>c\<in>XC. f b c \<in> {f b c | b c. b \<in> XR \<and> c \<in> XC}" by blast
    have z: "\<forall>a\<in>XL. \<forall>v\<in>{f b c | b c. b \<in> XR \<and> c \<in> XC}. f a v \<in> Z" using t by blast
    show ?L
      by (rule exI[where x=XL], rule exI[where x="{f b c | b c. b \<in> XR \<and> c \<in> XC}"])
         (use img_ne img z h in blast)
  qed
qed

private lemma ex_pair_split: "(\<exists>XL XR. G1 XL \<and> G2 XR) \<longleftrightarrow> (\<exists>X. G1 X) \<and> (\<exists>X. G2 X)"
  by blast

theorem ades_par_assoc_det:
  fixes j :: "'s merge" and P Q R :: "'s angelic_design"
  assumes det: "Functional j" and tot: "mergeable j"
    and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  obtain f where f: "\<And>s p q z. merge_eval j s p q z \<longleftrightarrow> z = f s p q"
    using mergeable_Functional_fun[OF tot det] by blast
  have fsym: "f s p q = f s q p" for s p q
    using sym f unfolding SymMerge_eval by metis
  have fassoc: "f s (f s a b) c = f s a (f s b c)" for s a b c
  proof -
    have "f s (f s a b) c = f s (f s b c) a"
      using assoc[unfolded AssocMerge_iff, rule_format, of s a b c "f s (f s a b) c"]
      by (simp add: f)
    then show ?thesis by (simp add: fsym[of s _ a])
  qed
  note obs = par_obs_unstarted[OF f] par_obs_started[OF f]
    div_at_par[OF f] term_at_par[OF f] obs_at_par[OF f]
  have term_nonempty: "term_at X s0 Y \<Longrightarrow> Y \<noteq> {}" for X :: "'s angelic_design" and s0 Y
    by (simp add: term_at_def)
  show ?thesis
  proof (rule ades_obs_ext)
    fix ok0 s0 ok' ac'
    show "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) (ades_obs ok0 s0 ok' ac') =
          (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)) (ades_obs ok0 s0 ok' ac')"
    proof (cases ok0)
      case False
      then show ?thesis by (simp only: obs) blast
    next
      case True
      let ?D3 = "(div_at P s0 \<and> obs_at Q s0 \<and> obs_at R s0) \<or> (obs_at P s0 \<and> div_at Q s0 \<and> obs_at R s0) \<or>
                 (obs_at P s0 \<and> obs_at Q s0 \<and> div_at R s0)"
      have left: "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) (ades_obs True s0 ok' ac') \<longleftrightarrow>
          ?D3 \<or> (ok' \<and> (\<exists>XL XR XC. term_at P s0 XL \<and> term_at Q s0 XR \<and> term_at R s0 XC \<and>
             (\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>e\<in>XC. f s0 (f s0 a b) e \<in> ac')))"
        apply (simp only: obs flat_left[where f="f s0", OF term_nonempty term_nonempty])
        apply (simp only: obs_at_iff ex_pair_split)
        by blast
      have right: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)) (ades_obs True s0 ok' ac') \<longleftrightarrow>
          ?D3 \<or> (ok' \<and> (\<exists>XL XR XC. term_at P s0 XL \<and> term_at Q s0 XR \<and> term_at R s0 XC \<and>
             (\<forall>a\<in>XL. \<forall>b\<in>XR. \<forall>e\<in>XC. f s0 a (f s0 b e) \<in> ac')))"
        apply (simp only: obs flat_right[where f="f s0", OF term_nonempty term_nonempty])
        apply (simp only: obs_at_iff ex_pair_split)
        by blast
      show ?thesis
        using True by (simp only: left right fassoc)
    qed
  qed
qed

end

subsubsection \<open>Example: Skip Merge\<close>

text \<open>With two terminating branch observations, the skip state merge requires
  s in ac'. A nonterminating branch permits every output set, including empty.\<close>

lemma ades_par_skip_eval:
  assumes operands: "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not>ok0 \<or> (\<exists>okL acL okR acR.
      acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      P (ades_obs True s0 okL acL) \<and> Q (ades_obs True s0 okR acR) \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> s0 \<in> ac'))))"
  using operands[unfolded H1_healthy_obs_iff]
  by (cases ok0; simp add: ades_par_def
      par_by_merge_eval choices_ex merge_ades_obs[simplified] skip_merge_eval; blast)

lemma ades_par_skip_comm:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> P)"
  by (rule ades_par_comm; simp add: Healthy_def skip_merge_swap)

lemma ades_par_skip_assoc:
  assumes "P is A2" "Q is A2" "R is A2" "P is H1" "Q is H1" "R is H1"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R) =
  (P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R))"
proof (rule ades_par_assoc[OF assms])
  show "skip\<^sub>m is SymMerge"
    by (simp add: Healthy_def skip_merge_swap)
  show "AssocMerge skip\<^sub>m"
    by (simp add: AssocMerge_def skip\<^sub>m_def; pred_auto)
qed (simp add: skip_merge_eval)

end
