section \<open>Angelic Parallel and Ordinary Designs\<close>

theory utp_ades_parallel
  imports utp_ades_designs
begin

subsection \<open>Lifting State Merge\<close>

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

subsubsection \<open>Design Merge Healthiness\<close>

text \<open>ADH1m and ADH2m follow H1m and H2m on the AD merge observation types;
  ADHM follows HDM. They handle H1/H2 behaviour, not A1, A2, or A3.\<close>

definition ADH1m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ADH1m M = (M \<or> (\<lambda>(m,obsOut). \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m)))"

definition ADH2m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ADH2m M = M ;; J"

text \<open>ADH3m is right completion with design skip on the AD merge type.
  It is the merge counterpart of H3, distinct from the angelic condition A3.
  ADHM retains its H1/H2-style meaning.\<close>

definition ADH3m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ADH3m M \<equiv> M ;; II\<^sub>D"

lemma ADH3m_idem: "ADH3m (ADH3m M) = ADH3m M"
  by (simp add: ADH3m_def seqr_assoc)

definition ADHM :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ADHM = ADH1m \<circ> ADH2m"

definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "merge_ades j \<equiv> ADH1m (ades_lift_merge j) ;; II\<^sub>D"

lemma ADH1m_idem: "ADH1m (ADH1m M) = ADH1m M"
  by (simp add: ADH1m_def disj_pred_def sup_assoc)

lemma ADH2m_idem: "ADH2m (ADH2m M) = ADH2m M"
  by (simp add: ADH2m_def seqr_assoc J_idem)

lemma ADH1m_ADH2m_commute: "ADH1m (ADH2m M) = ADH2m (ADH1m M)"
  by (simp add: ADH1m_def ADH2m_def; pred_auto)

lemma ADHM_idem: "ADHM (ADHM M) = ADHM M"
  by (simp add: ADHM_def ADH1m_ADH2m_commute ADH1m_idem ADH2m_idem)

lemma ADHM_mono: "M \<sqsubseteq> N \<Longrightarrow> ADHM M \<sqsubseteq> ADHM N"
  by (simp add: ADHM_def ADH1m_def ADH2m_def; pred_auto; blast)

lemma ADHM_healthy [closure]: "ADHM M is ADHM"
  by (simp add: Healthy_def' ADHM_idem)

lemma merge_ades_ADH1m [closure]: "merge_ades j is ADH1m"
  by (simp add: Healthy_def' merge_ades_def ADH1m_def; pred_auto)

lemma merge_ades_ADH2m [closure]: "merge_ades j is ADH2m"
  by (simp add: Healthy_def' ADH2m_def merge_ades_def seqr_assoc skip_d_absorb_J_1)

lemma merge_ades_ADHM [closure]: "merge_ades j is ADHM"
  using merge_ades_ADH1m[of j] merge_ades_ADH2m[of j]
  by (simp add: Healthy_def' ADHM_def)

lemma merge_ades_completion [simp]: "merge_ades j ;; II\<^sub>D = merge_ades j"
  by (simp add: merge_ades_def seqr_assoc)

lemma merge_ades_ADH3m [closure]: "merge_ades j is ADH3m"
  by (simp add: Healthy_def' ADH3m_def)

text \<open>merge_ades adds unstarted behaviour to the raw lift, then completes with
  design skip. Its merge healthiness holds for every j; operand healthiness and
  parallel closure are separate results below.
  When ok0 is false, the completed merge imposes no constraints.
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
  by (simp add: merge_ades_def ades_lift_merge_def ADH1m_def Let_def;
      pred_auto; metis UNIV_I ex_in_conv)

lemma merge_ades_obs:
  "ades_merge_obs (merge_ades j) ok0 s0 okL SL okR SR okOut SOut \<longleftrightarrow>
    (\<not> ok0 \<or> (SL \<noteq> {} \<and> SR \<noteq> {} \<and>
      (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut. merge_eval j s0 sL sR sOut) \<and>
      (okL \<and> okR \<longrightarrow>
        (okOut \<and> (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut)))))"
  by (auto simp: merge_ades_unfold Let_def)

subsection \<open>Lifted Parallel\<close>

lemma ades_par_by_merge_eval:
  "(P \<parallel>\<^bsub>M\<^esub> Q) (obs0,obsOut) \<longleftrightarrow>
    (\<exists>obsL obsR. P (obs0,obsL) \<and> Q (obs0,obsR) \<and> ades_merge_eval M obs0 obsL obsR obsOut)"
  by (cases obs0; cases obsOut;
      simp add: par_by_merge_def par_sep_def; pred_auto; blast)

lemma ades_par_lifted_A_closure:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A"
proof -
  let ?R = "P \<parallel>\<^bsub>merge_ades j\<^esub> Q"
  have up: "?R (ades_obs True s0 okOut SSub) \<Longrightarrow> SSub \<subseteq> SOut \<Longrightarrow>
    (okOut \<longrightarrow> okOut') \<Longrightarrow> ?R (ades_obs True s0 okOut' SOut)"
    for s0 okOut okOut' SSub SOut
    by (auto simp: ades_par_by_merge_eval merge_ades_unfold Let_def; blast)
  have empty: "?R (ades_obs True s0 okOut {}) \<Longrightarrow> ?R (ades_obs True s0 False {})"
    for s0 okOut
    by (auto simp: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified]; blast)
  have unstarted: "?R (ades_obs False s0 okOut SOut)" for s0 okOut SOut
    using assms[unfolded H1_healthy_obs_iff]
    by (simp add: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified])
  show ?thesis
    apply (rule Healthy_intro, rule ades_obs_ext)
    subgoal for ok0 s0 okOut SOut
      by (cases ok0; cases okOut; auto simp: A_obs unstarted empty intro: up)
    done
qed

text \<open>A2 alone reduces accepted nonempty branch sets to singleton witnesses.
  Without H1, unstarted parallel still requires feasible observations from both
  operands; this requirement is independent of the final choice set.\<close>

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


lemma ades_par_lifted_A2_closure:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A2"
  by (rule Healthy_intro, rule ades_obs_ext;
      simp only: A2_obs ades_par_lifted_obs_A2[OF assms]; auto split: if_splits; blast)


lemma ades_par_lifted_diverge:
  assumes "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 False X)"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 okOut Y)"
  using assms
  by (auto simp: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified]; blast)

lemma ades_par_lifted_A3_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A3"
proof -
  have H: "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is \<^bold>H"
    using A_is_H[of "P \<parallel>\<^bsub>merge_ades j\<^esub> Q"] ades_par_lifted_A_closure[OF assms]
    by (simp add: Healthy_def')
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext;
        simp only: A3_obs_H[OF H]; blast intro: ades_par_lifted_diverge)
qed

subsection \<open>AD Parallel by Merge\<close>

text \<open>AD parallel retains the A3 wrapper for unconditional A3 closure.
  For H1-healthy operands, lifted parallel is already A3-healthy, so the wrapper
  is redundant. A2 closure requires only A2-healthy operands; the wrapper
  preserves A2 without any additional operand premises.\<close>

definition ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = A3 (P \<parallel>\<^bsub>merge_ades j\<^esub> Q)"

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

subsection \<open>Algebraic Properties\<close>

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1) \<sqsubseteq> (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_def
  by (rule A3_mono; use assms in \<open>auto simp: pred_refine_iff ades_par_by_merge_eval split: prod.splits; blast\<close>)

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

text \<open>Associativity holds for A2-healthy operands under the merge premises of
  des_par_assoc_state: j is symmetric, associative, and mergeable.\<close>

subsubsection \<open>Associativity of AD Parallel\<close>

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

subsection \<open>Lifted Mapping Laws\<close>

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

subsection \<open>Chaos\<close>

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

subsection \<open>Skip Merge Example\<close>

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
