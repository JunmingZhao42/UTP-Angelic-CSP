section \<open>Reactive angelic design parallel with a lifted merge\<close>

theory utp_rad_parallel_lift
  imports utp_rad_parallel_laws "UTP-Angelic-Designs.utp_ades_parallel_lift"
    "UTP-Reactive-Designs.utp_rdes_parallel_lift"
begin

(* The ordinary parallel import restores this notation; retain the RAD meaning. *)
no_notation wait_f ("_\<^sub>f" [1000] 1000)

subsection \<open>Basic RAD merge\<close>

(* Waiting uses II_Rac; unstarted observations admit trace extensions.
   Active observations synchronise trace contributions and disjoin waiting flags; refusals are unrestricted. *)
definition rad_basic_merge :: "('t::trace, 'e) rad_merge_rel" where
  "rad_basic_merge \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; p = mrg_left\<^sub>v m; q = mrg_right\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x);
        acL = achoices.ac\<^sub>v (des_vars.more p);
        acR = achoices.ac\<^sub>v (des_vars.more q);
        ac' = achoices.ac\<^sub>v (des_vars.more z)
    in acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (if rad_wait\<^sub>v s0 then II_Rac (x,z)
       else if \<not> des_vars.ok\<^sub>v x then rad_trace_extensions s0 \<inter> ac' \<noteq> {}
       else ((des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<longrightarrow> des_vars.ok\<^sub>v z) \<and>
         (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
           rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
           rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR))))"

lemma rad_basic_merge_obs:
  "ades_merge_obs rad_basic_merge ok0 s0 okL acL okR acR ok' ac' =
    (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (if rad_wait\<^sub>v s0 then II_Rac (ades_obs ok0 s0 ok' ac')
       else if \<not> ok0 then rad_trace_extensions s0 \<inter> ac' \<noteq> {}
       else ((okL \<and> okR) \<longrightarrow> ok') \<and>
         (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
           rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
           rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR))))"
  by (simp add: rad_basic_merge_def Let_def)

lemma rad_basic_merge_RA1m [closure]: "rad_basic_merge is RA1m"
  unfolding Healthy_def'
  by (rule ades_merge_ext;
      auto simp: RA1m_obs[simplified] rad_basic_merge_obs[simplified]
        II_Rac_eval rad_trace_extensions_def; blast)

lemma rad_basic_merge_RA2m [closure]:
  "(rad_basic_merge :: ('t::trace, 'e) rad_merge_rel) is RA2m"
proof -
  have normalise:
    "(\<exists>s'\<in>rad_normalise_choices s0 ac'.
       rad_tr\<^sub>v s' = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
       rad_tr\<^sub>v s' = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
       rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR)) =
     (\<exists>s'\<in>ac'.
       rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
       rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
       rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
       rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR))"
    for s0 sL sR :: "('t::trace, 'e) rad_state" and ac'
    by (auto simp: rad_normalise_choices_def rad_trace_difference_def)
  show ?thesis
    unfolding Healthy_def'
    apply (rule ades_merge_ext)
    apply (simp add: RA2m_obs[simplified] rad_basic_merge_obs[simplified]
        II_Rac_eval rad_zero_trace_extensions rad_zero_trace_in_normalise
        rad_normalise_choices_nonempty)
    apply (simp add: rad_zero_trace_def rad_trace_difference_def normalise)
    by (auto simp: rad_trace_extensions_def)
qed

lemma rad_basic_merge_RA3m [closure]: "rad_basic_merge is RA3m"
  unfolding Healthy_def'
  by (rule ades_merge_ext; simp add: RA3m_obs[simplified] rad_basic_merge_obs[simplified])

lemma rad_basic_merge_CSPA1m [closure]: "rad_basic_merge is CSPA1m"
  unfolding Healthy_def'
  by (rule ades_merge_ext;
      auto simp: CSPA1m_obs[simplified] rad_basic_merge_obs[simplified] II_Rac_eval)

lemma rad_basic_merge_CSPA2m [closure]: "rad_basic_merge is CSPA2m"
  unfolding Healthy_def'
  by (rule ades_merge_ext;
      auto simp: H2m_ades_obs[simplified] rad_basic_merge_obs[simplified] II_Rac_eval)

lemma rad_basic_merge_PBMHm [closure]:
  "(rad_basic_merge :: ('t::trace, 'e) rad_merge_rel) is PBMHm"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  subgoal for ok0 s0 okL acL okR acR ok' ac'
    by (cases "rad_wait\<^sub>v s0"; cases ok0;
        simp add: PBMHm_obs[simplified] rad_basic_merge_obs[simplified]
          II_Rac_eval rad_trace_extensions_def; blast)
  done

lemma rad_basic_merge_ABm [closure]:
  "(rad_basic_merge :: ('t::trace, 'e) rad_merge_rel) is ABm"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  subgoal for ok0 s0 okL acL okR acR ok' ac'
    by (cases "rad_wait\<^sub>v s0"; cases ok0;
        simp add: ABm_obs[simplified] rad_basic_merge_obs[simplified]; blast)
  done

lemma rad_basic_merge_RADm [closure]: "rad_basic_merge is RADm"
  by (simp add: RADm_healthy_iff rad_basic_merge_RA1m rad_basic_merge_RA2m
      rad_basic_merge_RA3m rad_basic_merge_CSPA1m rad_basic_merge_CSPA2m
      rad_basic_merge_PBMHm rad_basic_merge_ABm)

subsection \<open>Choice-set lifting\<close>

text \<open>Every pair of branch states must have a merged output in the final set.
  The ordinary merge supplies the control, trace, waiting and refusal policy.\<close>

(* Lift ordinary reactive observations to nonempty branch choice sets. *)
definition rad_lift_merge ::
  "('t::trace, 'e set) rp merge \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "rad_lift_merge \<equiv> ABm \<circ> ac'_lift_merge"

lemma rad_lift_merge_obs:
  "ades_merge_obs (rad_lift_merge M) ok0 s0 okL X okR Y ok' Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
      merge_eval M (\<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>)
        (\<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>)
        (\<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>)
        (\<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)))"
  by (simp add: rad_lift_merge_def ABm_ac'_lift_merge_obs[simplified])

lemma rad_lift_merge_mono:
  "M \<sqsubseteq> N \<Longrightarrow> rad_lift_merge M \<sqsubseteq> rad_lift_merge N"
  unfolding rad_lift_merge_def comp_apply
  by (rule pred_ref_monoD[OF ABm_Monotonic];
      auto simp: pred_refine_iff ac'_lift_merge_def Let_def split: prod.splits; blast)

lemma rad_lift_merge_SymMerge:
  "M is SymMerge \<Longrightarrow> rad_lift_merge M is SymMerge"
proof -
  assume assms: "M is SymMerge"
  have sym: "merge_eval M x p q z = merge_eval M x q p z" for x p q z
    using assms by (simp add: SymMerge_eval)
  show ?thesis
    by (simp add: SymMerge_eval des_vars.splits astate.splits achoices.splits
        rad_lift_merge_obs[simplified] sym; blast)
qed

subsubsection \<open>ORDm lift facts\<close>

lemma rad_lift_merge_CSPA2m:
  assumes "M is RD2"
  shows "rad_lift_merge M is CSPA2m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp only: H2m_ades_obs rad_lift_merge_obs)
  using RD2_ok_up[OF assms]
  apply auto
  by blast

lemma ORDm_div_eval:
  assumes "M is ORDm" "\<not> b" "s' \<in> rad_trace_extensions s0"
  shows "merge_eval M \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
    \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
proof -
  have "merge_eval M \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> =
    merge_eval (ORDm M) \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    using assms(1) by (simp add: Healthy_def')
  also have "... = (rea_vars.tr\<^sub>v \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> \<le>
      rea_vars.tr\<^sub>v \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>)"
    using assms(2) by (simp add: ORDm_unstarted)
  finally show ?thesis
    using assms(3) by (metis rad_tr_record rad_trace_extensions_def mem_Collect_eq)
qed

lemma ORDm_ext_eval:
  assumes "M is ORDm"
    and "merge_eval M \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
  shows "s' \<in> rad_trace_extensions s0"
proof -
  have h: "M is R1m" by (rule ORDm_R1m[OF assms(1)])
  have growth: "merge_eval M x p q z \<Longrightarrow>
      rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z" for x p q z
    using h by (metis Healthy_def' R1m_merge_eval)
  show ?thesis using growth assms(2)
    by (metis rad_tr_record rad_trace_extensions_def mem_Collect_eq)
qed

lemma R2m_rad_eval:
  assumes "M is R2m"
  shows "merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> =
    (s' \<in> rad_trace_extensions s0 \<and>
     merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = rad_zero_trace s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = rad_trace_difference s0 sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = rad_trace_difference s0 sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = rad_trace_difference s0 s'\<rparr>)"
proof -
  have "merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> =
    merge_eval (R2m M)
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    using assms by (simp add: Healthy_def')
  also have "... = (s' \<in> rad_trace_extensions s0 \<and>
     merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = rad_zero_trace s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = rad_trace_difference s0 sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = rad_trace_difference s0 sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = rad_trace_difference s0 s'\<rparr>)"
    by (cases s0; cases sL; cases sR; cases s';
        simp add: R2m_merge_eval rad_zero_trace_def
          rad_trace_difference_def rad_trace_extensions_def)
  finally show ?thesis .
qed

subsection \<open>Lifted merge healthiness\<close>

lemma R2m_choice_normalise:
  assumes "M is R2m"
  shows "(\<exists>s'\<in>Z. merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>) =
    (\<exists>z\<in>rad_normalise_choices s0 Z. merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = rad_zero_trace s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = rad_trace_difference s0 sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = rad_trace_difference s0 sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>)"
  by (subst R2m_rad_eval[OF assms];
      auto simp: rad_normalise_choices_def rad_trace_extensions_def)

lemma rad_lift_merge_RA1m:
  assumes "M is ORDm"
  shows "rad_lift_merge M is RA1m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp add: RA1m_obs[simplified] rad_lift_merge_obs[simplified])
  using ORDm_ext_eval[OF assms] by blast

lemma rad_lift_merge_RA2m:
  assumes "M is R2m"
  shows "rad_lift_merge M is RA2m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp only: RA2m_obs rad_lift_merge_obs)
  apply (subst (2) R2m_choice_normalise[OF assms])
  apply simp
  by fast

lemma rad_lift_merge_CSPA1m:
  assumes "M is ORDm"
  shows "rad_lift_merge M is CSPA1m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp add: CSPA1m_obs[simplified] rad_lift_merge_obs[simplified])
  using ORDm_div_eval[OF assms] by blast

lemma rad_lift_merge_RA3m:
  assumes "M is ORDm"
  shows "rad_lift_merge M is RA3m"
proof -
  have div: "merge_eval M \<lparr>ok\<^sub>v = False, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> = (s' \<in> rad_trace_extensions s0)" for s0 p q c s'
    using ORDm_div_eval[OF assms, where b=False, simplified]
      ORDm_ext_eval[OF assms, where b=False]
    by blast
  have h: "M is R3cm" using assms by (simp add: ORDm_healthy_iff)
  have waiting: "merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> = (c \<and> s' = s0)"
    if "rad_wait\<^sub>v s0" for s0 p q c s'
    by (subst Healthy_if[OF h, symmetric]; simp add: R3cm_eval that)
  show ?thesis
    unfolding Healthy_def'
    apply (rule ades_merge_ext)
    subgoal for ok0 s0 okL X okR Y ok' Z
      apply (cases "rad_wait\<^sub>v s0"; cases ok0)
      apply (simp_all add: RA3m_obs[simplified] rad_lift_merge_obs[simplified]
          II_Rac_eval waiting div)
      apply blast
      apply (simp add: rad_trace_extensions_def)
      by blast
    done
qed

lemma rad_lift_merge_PBMHm [closure]:
  "rad_lift_merge M is PBMHm"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp add: PBMHm_obs[simplified] rad_lift_merge_obs[simplified])
  by blast

lemma rad_lift_merge_ABm [closure]:
  "rad_lift_merge M is ABm"
  by (simp add: Healthy_def' rad_lift_merge_def ABm_idem)

lemma rad_lift_merge_RADm:
  assumes "M is ORDm"
  shows "rad_lift_merge M is RADm"
  using assms unfolding RADm_healthy_iff
  by (auto simp: ORDm_healthy_iff intro: rad_lift_merge_RA1m rad_lift_merge_RA2m
      rad_lift_merge_RA3m rad_lift_merge_CSPA1m rad_lift_merge_PBMHm
      rad_lift_merge_ABm rad_lift_merge_CSPA2m)

subsection \<open>RAD parallel by merge\<close>

lemma rad_lift_par_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
  shows "p2ac P \<parallel>\<^bsub>rad_lift_merge M\<^esub> p2ac Q = p2ac (P \<parallel>\<^bsub>M\<^esub> Q)"
  apply (rule ades_obs_ext)
  apply (simp only: rad_p2ac_obs par_by_merge_eval
      choices_ex rad_lift_merge_obs[simplified])
  apply (simp only: des_vars.splits)
  by (blast intro: exI[where x="{_}"])

lemma rad_par_by_merge_form:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
    and "AM = rad_lift_merge M"
  shows "P \<parallel>\<^bsub>AM\<^esub> Q =
    p2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
  using rad_lift_par_p2ac[where P="ac2p P" and Q="ac2p Q" and M=M]
  by (simp only: assms(5) rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

lemma rad_par_by_merge_ac2p:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
    and "AM = rad_lift_merge M"
  shows "ac2p (P \<parallel>\<^bsub>AM\<^esub> Q) =
    ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q"
  by (simp only: rad_par_by_merge_form[OF assms] rad_ac2p_p2ac_inverse')

(* merge_rad j = rad_lift_merge (merge_rdes j) *)
abbreviation merge_rad :: "('t::trace \<times> 'e set) merge \<Rightarrow> ('t, 'e) rad_merge_rel"
  where "merge_rad j \<equiv> rad_lift_merge (merge_rdes j)"

(* P \<parallel>\<^sub>R\<^sub>A\<^sub>D[j] Q = P \<parallel>[merge_rad j] Q. *)
abbreviation rad_par_lift ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t \<times> 'e set) merge \<Rightarrow>
    ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<equiv>
    P \<parallel>\<^bsub>merge_rad j\<^esub> Q"

lemma rad_par_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
    and j :: "('t \<times> 'e set) merge"
  shows "p2ac P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> p2ac Q =
    p2ac (P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q)"
  by (rule rad_lift_par_p2ac)

lemma rad_par_form:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q =
    p2ac (ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p Q)"
  by (rule rad_par_by_merge_form[OF assms refl])

lemma rad_par_ac2p:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) =
    ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p Q"
  by (rule rad_par_by_merge_ac2p[OF assms refl])

lemma rad_par_ac2p_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
    and j :: "('t \<times> 'e set) merge"
  shows "P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q =
    ac2p (p2ac P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> p2ac Q)"
  by (simp only: rad_par_p2ac rad_ac2p_p2ac_inverse')

lemma rad_par_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  by (simp add: rad_par_form[OF assms] Healthy_def')

lemma rad_par_RAD [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RAD"
  by (rule rad_par_by_merge_RAD[OF assms rad_lift_merge_RADm[OF merge_rdes_ORDm]])

lemma rad_par_NDRAD [closure]:
  assumes rad: "P is RAD" "Q is RAD"
      and a2: "P is A2" "Q is A2"
      and nondiv: "P is NDRAD" "Q is NDRAD"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is NDRAD"
proof -
  have rd: "ac2p P is RD" "ac2p Q is RD"
    using rad a2 by (blast intro: rad_ac2p_RD)+
  have nd: "ac2p P is NDRD" "ac2p Q is NDRD"
    using rad a2 nondiv by (blast intro: rad_ac2p_NDRD)+
  have "(ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p Q) is NDRD"
    by (rule rdes_lift_parallel_NDRD[OF rd nd])
  from rad_p2ac_NDRAD[OF this] show ?thesis
    by (simp only: rad_par_form[OF rad a2])
qed

subsection \<open>Algebra\<close>

lemma rad_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "P1 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1 \<sqsubseteq> P2 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2"
  using assms
  by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)

lemma rad_par_comm:
  assumes "j is SymMerge"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P"
  by (rule par_by_merge_comm[OF rad_lift_merge_SymMerge[OF merge_rdes_SymMerge[OF assms]]])

text \<open>Associativity of the lifted merge transfers from the ordinary
  nondivergent law through @{const p2ac}. The premises on @{term M} are those of
  @{thm [source] par_by_merge_assoc_NDRD}.\<close>

lemma par_by_rad_lift_merge_assoc_NDRAD:
  fixes M :: "('t::trace, 'e set) rp merge"
  assumes rad: "P is RAD" "Q is RAD" "R is RAD"
      and a2: "P is A2" "Q is A2" "R is A2"
      and nondiv: "P is NDRAD" "Q is NDRAD" "R is NDRAD"
      and merge: "M is SymMerge" "M is NDRDm"
        "AssocMerge (merge_guard (\<lambda>x z. ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z) M)"
  shows "(P \<parallel>\<^bsub>rad_lift_merge M\<^esub> Q) \<parallel>\<^bsub>rad_lift_merge M\<^esub> R =
    P \<parallel>\<^bsub>rad_lift_merge M\<^esub> (Q \<parallel>\<^bsub>rad_lift_merge M\<^esub> R)"
proof -
  have rd: "ac2p P is RD" "ac2p Q is RD" "ac2p R is RD"
    using rad a2 by (blast intro: rad_ac2p_RD)+
  have nd: "ac2p P is NDRD" "ac2p Q is NDRD" "ac2p R is NDRD"
    using rad a2 nondiv by (blast intro: rad_ac2p_NDRD)+
  have ordinary: "(ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) \<parallel>\<^bsub>M\<^esub> ac2p R =
      ac2p P \<parallel>\<^bsub>M\<^esub> (ac2p Q \<parallel>\<^bsub>M\<^esub> ac2p R)"
    by (rule par_by_merge_assoc_NDRD[OF rd nd merge])
  show ?thesis
    using arg_cong[OF ordinary, of p2ac]
    by (simp only: rad_lift_par_p2ac[symmetric]
        rad_p2ac_ac2p_RAD_A2'[OF rad(1) a2(1)]
        rad_p2ac_ac2p_RAD_A2'[OF rad(2) a2(2)]
        rad_p2ac_ac2p_RAD_A2'[OF rad(3) a2(3)])
qed

lemma rad_par_assoc:
  assumes rad: "P is RAD" "Q is RAD" "R is RAD"
      and a2: "P is A2" "Q is A2" "R is A2"
      and nondiv: "P is NDRAD" "Q is NDRAD" "R is NDRAD"
      and merge: "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R =
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (rule par_by_rad_lift_merge_assoc_NDRAD[OF rad a2 nondiv
        merge_rdes_SymMerge[OF merge(1)] merge_rdes_NDRDm
        merge_rdes_guard_AssocMerge[OF merge(2)]])

end
