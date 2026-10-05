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

text \<open>lift_merge lifts a state merge to the AD merge observation types.
  SL and SR must be nonempty, and each pair (sL,sR) must have an sOut in SOut
  satisfying j. The termination flags satisfy okOut = (okL \<and> okR).\<close>

definition lift_merge :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  [pred]: "lift_merge j \<equiv> (\<lambda>(m,obsOut).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        SL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        SR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        SOut = achoices.ac\<^sub>v (des_vars.more obsOut)
    in SL \<noteq> {} \<and> SR \<noteq> {} \<and>
       (des_vars.ok\<^sub>v obsOut =
         (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m))) \<and>
       (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut))"

lemma lift_merge_obs:
  "ades_merge_obs (lift_merge j) ok0 s0 okL SL okR SR okOut SOut \<longleftrightarrow>
    (SL \<noteq> {} \<and> SR \<noteq> {} \<and> okOut = (okL \<and> okR) \<and>
      (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut))"
  by (auto simp: lift_merge_def Let_def)

subsubsection \<open>Design Merge Healthiness\<close>

text \<open>ADH1m and ADH2m follow H1m and H2m on the AD merge observation types;
  ADHM follows HDM. They handle H1/H2 behaviour, not A1, A2, or A3.\<close>

definition ADH1m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ADH1m M = (M \<or> (\<lambda>(m,obsOut). \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m)))"

definition ADH2m :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ADH2m M = M ;; J"

definition ADHM :: "'s ades_merge_rel \<Rightarrow> 's ades_merge_rel" where
  [pred]: "ADHM = ADH1m \<circ> ADH2m"

abbreviation merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "merge_ades j \<equiv> ADHM (lift_merge j)"

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

text \<open>merge_ades applies ADHM to lift_merge. When ok0 is false, it imposes no constraints.
  When ok0 is true, it requires (okL \<and> okR) \<longrightarrow> okOut and an output witness
  for each pair of branch states, so SOut cannot be empty even when okOut is false.\<close>

lemma merge_ades_unfold:
  "merge_ades j = (\<lambda>(m,obsOut).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        SL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        SR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        SOut = achoices.ac\<^sub>v (des_vars.more obsOut)
    in \<not> des_vars.ok\<^sub>v (mrg_prior\<^sub>v m) \<or>
       (SL \<noteq> {} \<and> SR \<noteq> {} \<and>
        (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)
          \<longrightarrow> des_vars.ok\<^sub>v obsOut) \<and>
        (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut)))"
  by (simp add: ADHM_def ADH1m_def ADH2m_def lift_merge_def Let_def; pred_auto)

lemma merge_ades_obs:
  "ades_merge_obs (merge_ades j) ok0 s0 okL SL okR SR okOut SOut \<longleftrightarrow>
    (\<not> ok0 \<or> (SL \<noteq> {} \<and> SR \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> okOut) \<and>
      (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut)))"
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
  have empty: "\<not> ?R (ades_obs True s0 okOut {})" for s0 okOut
    by (auto simp: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified])
  have unstarted: "?R (ades_obs False s0 okOut SOut)" for s0 okOut SOut
    using assms[unfolded H1_healthy_obs_iff]
    by (simp add: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified])
  show ?thesis
    apply (rule Healthy_intro, rule ades_obs_ext)
    subgoal for ok0 s0 okOut SOut
      by (cases ok0; cases okOut; auto simp: A_obs unstarted empty intro: up)
    done
qed

text \<open>For A- and A2-healthy operands, a started lifted parallel accepts SOut exactly
  when singleton branch observations can merge to some sOut in SOut.
  This gives A2 closure; the empty output set is still rejected.\<close>

lemma ades_par_lifted_obs:
  fixes P Q :: "'s angelic_design"
  assumes "P is A" and "Q is A" and "P is A2" and "Q is A2"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    (\<not> ok0 \<or> (\<exists>okL sL okR sR. \<exists>sOut\<in>SOut.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      merge_eval j s0 sL sR sOut \<and> (okL \<and> okR \<longrightarrow> okOut)))"
proof -
  have singleton: "\<exists>sOut\<in>SOut. R (ades_obs ok0 s0 okOut {sOut})"
    if "R is A" "R is A2" "SOut \<noteq> {}" "R (ades_obs ok0 s0 okOut SOut)"
    for R :: "'s angelic_design" and ok0 s0 okOut SOut
  proof -
    have up: "R (ades_obs ok0 s0 okOut {}) \<Longrightarrow> R (ades_obs ok0 s0 okOut {sOut})" for sOut
      using PBMH_ades_obs[of R ok0 s0 okOut "{sOut}"]
      by (auto simp only: Healthy_if[OF A_is_PBMH_ades[OF that(1)]]
          intro: exI[where x="{}"])
    show ?thesis
      using A2_obs[of R ok0 s0 okOut SOut] up that(3,4)
      by (simp only: Healthy_if[OF that(2)]; blast)
  qed
  have operands_H1: "P is H1" "Q is H1"
    using assms(1) assms(2) by (simp_all add: A_healthy_components_iff)
  show ?thesis
    using operands_H1
    apply (cases ok0; simp add: ades_par_by_merge_eval choices_ex
        merge_ades_obs[simplified] H1_healthy_obs_iff)
    apply (rule iffI)
    subgoal
      using singleton[OF assms(1) assms(3)] singleton[OF assms(2) assms(4)]
      by metis
    subgoal by (fastforce intro: exI[where x="{_}"])
    done
qed

lemma ades_par_lifted_A2_closure:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^bsub>merge_ades j\<^esub> Q) is A2"
  by (rule Healthy_intro, rule ades_obs_ext;
      simp only: A2_obs ades_par_lifted_obs[OF assms]; blast)

subsection \<open>AD Parallel by Merge\<close>

text \<open>AD parallel applies A3 to lifted parallel. For H1-healthy operands, A3 only
  adds empty-set observations; all other observations are unchanged.
  AD parallel is A-healthy for H1-healthy operands, A2-healthy for A- and
  A2-healthy operands, and A3-healthy without operand assumptions.\<close>

definition ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = A3 (P \<parallel>\<^bsub>merge_ades j\<^esub> Q)"

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_def
  by (rule A3_preserves_A[OF ades_par_lifted_A_closure[OF assms]])

lemma ades_par_A2_closure [closure]:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  unfolding ades_par_def
  by (rule A3_preserves_A2[OF ades_par_lifted_A2_closure[OF assms]])

lemma ades_par_A3_closure [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  by (simp add: ades_par_def Healthy_def' A3_idem)

lemma ades_par_eval:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    ((P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<or>
      (SOut = {} \<and> (\<forall>sOut.
        (P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs ok0 s0 False {sOut}))))"
  using A_is_H[of "P \<parallel>\<^bsub>merge_ades j\<^esub> Q"]
    ades_par_lifted_A_closure[OF assms]
  by (simp add: ades_par_def A3_obs_H Healthy_def')

subsection \<open>ac2p/d2ac Mapping Laws\<close>

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
    apply (simp only: ades_par_eval[OF operands_H1]
      ades_par_lifted_obs[OF assms] d2ac_healthy_obs[OF des_par_H_closure[OF designs_H]]
      ordinary_parallel_obs ac2p_healthy_obs[OF A_is_PBMH_ades[OF assms(1)]]
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
        ac2p_d2ac[OF des_par_H_closure[OF designs_H], simplified comp_apply])
qed

lemma ades_par_ac2p_d2ac:
  assumes "D is \<^bold>H" "E is \<^bold>H"
  shows "D \<parallel>\<^sub>D\<^bsub>j\<^esub> E = ac2p ((d2ac D) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac E))"
  by (simp only: ades_par_d2ac[OF assms]
      ac2p_d2ac[OF des_par_H_closure[OF assms], simplified comp_apply])

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

lemma ades_par_comm:
  assumes "merge_ades j is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P)"
  unfolding ades_par_def
  by (rule arg_cong[where f=A3], rule par_by_merge_comm; use assms in \<open>simp add: Healthy_def'\<close>)

text \<open>Associativity holds for A- and A2-healthy operands when state merging is
  associative at the same initial state. SymMerge and AssocMerge provide
  sufficient merge conditions in ades_par_assoc.\<close>

subsubsection \<open>Associativity of AD Parallel\<close>

lemma ades_par_assoc_state:
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
  have par_A: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A"
    using operands_H1 by (auto intro: ades_par_A_closure)
  have par_A2: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A2"
    using assms(1-6) by (auto intro: ades_par_A2_closure)
  show ?thesis
    by (simp only: ades_par_d2ac_ac2p[OF par_A(1) assms(3) par_A2(1) assms(6)]
        ades_par_d2ac_ac2p[OF assms(1) par_A(2) assms(4) par_A2(2)]
        ades_par_ac2p[OF assms(1,2) assms(4,5)]
        ades_par_ac2p[OF assms(2,3) assms(5,6)]
        des_par_assoc_state[OF assms(7)])
qed

lemma ades_par_assoc:
  assumes "P is A" "Q is A" "R is A"
    "P is A2" "Q is A2" "R is A2"
    "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  apply (rule ades_par_assoc_state[OF assms(1-6)])
  using assms(7,8)
  by (simp add: Healthy_def' AssocMerge_def fun_eq_iff; pred_auto; blast)

subsection \<open>When A3 Changes Parallel\<close>

text \<open>For H1-healthy operands, the two design forms share the commitment Success.
  A3 changes the precondition from \<not>Failure to \<not>Failure \<and> \<not>Empty.
  At a fixed s0, if every singleton admits nontermination, the precondition
  becomes false at the empty set, accepting it for either value of okOut.\<close>

context
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
    and Failure Success Empty :: "'s angelic_rel"
  assumes operands: "P is H1" "Q is H1"
  defines "Failure \<equiv> (\<lambda>(obs0,obsOut). (P \<parallel>\<^bsub>merge_ades j\<^esub> Q)
    (ades_obs True (astate.s\<^sub>v obs0) False (achoices.ac\<^sub>v obsOut)))"
    and "Success \<equiv> (\<lambda>(obs0,obsOut). (P \<parallel>\<^bsub>merge_ades j\<^esub> Q)
    (ades_obs True (astate.s\<^sub>v obs0) True (achoices.ac\<^sub>v obsOut)))"
    and "Empty \<equiv> (\<lambda>(obs0,obsOut). achoices.ac\<^sub>v obsOut = {} \<and>
      (\<forall>sOut. Failure (obs0, \<lparr>achoices.ac\<^sub>v = {sOut}\<rparr>)))"
begin

lemma ades_par_lifted_rdesign:
  "P \<parallel>\<^bsub>merge_ades j\<^esub> Q = ((\<not> Failure) \<turnstile>\<^sub>r Success)"
proof -
  have H: "\<^bold>H (P \<parallel>\<^bsub>merge_ades j\<^esub> Q) = P \<parallel>\<^bsub>merge_ades j\<^esub> Q"
    using A_is_H[of "P \<parallel>\<^bsub>merge_ades j\<^esub> Q"]
      ades_par_lifted_A_closure[OF operands]
    by (simp add: Healthy_def')
  have slices:
    "pre\<^sub>D R = (\<not> (\<lambda>(obs0,obsOut). R
      (ades_obs True (astate.s\<^sub>v obs0) False (achoices.ac\<^sub>v obsOut))))"
    "post\<^sub>D R = (\<lambda>(obs0,obsOut). R
      (ades_obs True (astate.s\<^sub>v obs0) True (achoices.ac\<^sub>v obsOut)))"
    for R :: "'s angelic_design"
    by (pred_simp; auto simp: des_vars_collapse)+
  show ?thesis
    using H1_H2_eq_rdesign[of "P \<parallel>\<^bsub>merge_ades j\<^esub> Q", unfolded H]
    by (simp only: slices Failure_def Success_def)
qed

lemma ades_par_rdesign:
  "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = ((\<not> Failure \<and> \<not> Empty) \<turnstile>\<^sub>r Success)"
  unfolding Empty_def
  by (rule ades_obs_ext;
      simp only: ades_par_eval[OF operands] ades_par_lifted_rdesign;
      pred_simp; auto simp: des_vars_collapse)

lemma ades_par_ne_lifted_iff:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<noteq> P \<parallel>\<^bsub>merge_ades j\<^esub> Q) \<longleftrightarrow>
    (\<exists>s0. Empty (\<lparr>astate.s\<^sub>v = s0\<rparr>, \<lparr>achoices.ac\<^sub>v = {}\<rparr>))"
proof -
  have empty: "\<not> (P \<parallel>\<^bsub>merge_ades j\<^esub> Q) (ades_obs True s0 okOut {})"
    for s0 okOut
    by (auto simp: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified])
  show ?thesis
    by (subst arg_cong2[where f = "(\<noteq>)",
          OF ades_par_rdesign ades_par_lifted_rdesign];
        expr_simp add: rdesign_def design_def conj_pred_def not_pred_def impl_pred_def
          Empty_def Failure_def Success_def empty;
        auto simp: ex_bool_eq empty intro!: exI[of _ "{}"])
qed

end

subsubsection \<open>Chaos Example\<close>

text \<open>Chaos is the predicate @{term true}, equivalently a design with a false
  precondition. With an always-true state merge, lifted parallel rejects exactly
  the started empty-set observations; A3 completion restores Chaos.\<close>

lemma ades_par_lifted_chaos:
  "(true \<parallel>\<^bsub>merge_ades true\<^esub> true :: 's angelic_design) =
    (($ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e \<turnstile>\<^sub>r ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
  by (rule ades_obs_ext;
      simp only: ades_par_by_merge_eval choices_ex merge_ades_obs[simplified];
      pred_simp; auto simp: ex_bool_eq intro!: exI[where x=UNIV])

lemma ades_par_chaos:
  "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>true\<^esub> true :: 's angelic_design) = true"
  by (rule ades_obs_ext;
      simp only: ades_par_def ades_par_lifted_chaos A3_obs_H[OF rdesign_is_H1_H2];
      pred_simp; auto)

subsection \<open>Skip Merge Example\<close>

text \<open>The skip state merge requires sOut = s0, so a started lifted parallel
  requires s0 in SOut. A3 adds the empty output set when s0 is the only
  possible state and both branches admit nonempty choice sets with at least
  one termination flag false. This added observation does not satisfy the
  lifted merge itself. With at least two states, the empty-set clause is false.\<close>

lemma ades_par_skip_eval:
  assumes operands: "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    (\<not>ok0 \<or> (\<exists>okL SL okR SR.
      SL \<noteq> {} \<and> SR \<noteq> {} \<and>
      P (ades_obs True s0 okL SL) \<and> Q (ades_obs True s0 okR SR) \<and>
      ((s0 \<in> SOut \<and> (okL \<and> okR \<longrightarrow> okOut)) \<or>
       (SOut = {} \<and> (\<forall>s'. s' = s0) \<and> \<not>(okL \<and> okR)))))"
proof -
  have lifted: "(P \<parallel>\<^bsub>merge_ades skip\<^sub>m\<^esub> Q) (ades_obs ok0 s0 okOut SOut) \<longleftrightarrow>
    (\<not>ok0 \<or> (s0 \<in> SOut \<and> (\<exists>okL SL okR SR.
      SL \<noteq> {} \<and> SR \<noteq> {} \<and> P (ades_obs True s0 okL SL) \<and>
      Q (ades_obs True s0 okR SR) \<and> (okL \<and> okR \<longrightarrow> okOut))))"
    for ok0 okOut SOut
    using operands[unfolded H1_healthy_obs_iff]
    by (cases ok0; simp add: ades_par_by_merge_eval choices_ex
        merge_ades_obs[simplified] skip_merge_eval; blast)
  show ?thesis
    by (cases ok0; cases "s0 \<in> SOut"; cases "SOut = {}";
        cases "\<forall>s'. s' = s0"; simp add: ades_par_eval[OF operands] lifted eq_commute; blast)
qed

lemma ades_par_skip_comm:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> P)"
  by (rule ades_par_comm;
      auto simp: SymMerge_ades merge_ades_unfold Let_def skip_merge_eval)

lemma ades_par_skip_assoc:
  assumes "P is A" "Q is A" "R is A" "P is A2" "Q is A2" "R is A2"
  shows "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R) =
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> R))"
  by (rule ades_par_assoc_state[OF assms]; simp add: skip_merge_eval)

end
