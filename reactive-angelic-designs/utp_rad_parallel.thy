section \<open>Reactive angelic design parallel by merge\<close>

theory utp_rad_parallel
  imports utp_rad_csp "UTP-Angelic-Designs.utp_ades_parallel"
    "UTP-Reactive-Designs.utp_rdes_parallel"
begin

(* The ordinary parallel import restores this notation; retain the RAD meaning. *)
no_notation wait_f ("_\<^sub>f" [1000] 1000)

type_synonym ('t, 'e) rad_merge_rel =
  "(('t, 'e) rad_state) ades_merge_rel"

lemma RA1_obs:
  "RA1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c (rad_trace_extensions s0 \<inter> X)) \<and>
      rad_trace_extensions s0 \<inter> X \<noteq> {})"
  by (simp add: RA1_def Let_def)

lemma CSPA1_obs:
  "CSPA1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 c X) \<or>
      (\<not> b \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}))"
  by (simp add: CSPA1_def RA1_not_ok_eval; pred_auto)

definition basic_merge_state ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow>
   ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> bool"
where
  "basic_merge_state s0 l r z \<longleftrightarrow>
    rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v z \<and>
    rad_tr\<^sub>v z = rad_tr\<^sub>v l \<and>
    rad_tr\<^sub>v z = rad_tr\<^sub>v r \<and>
    rad_wait\<^sub>v z = (rad_wait\<^sub>v l \<or> rad_wait\<^sub>v r)"


text \<open>Parallel uses a lifted merge on complete reactive observations.
  RAD and A2 operands yield a RAD-healthy result when the merge is RADm-healthy.
  The ordinary correspondence uses p2ac rather than d2ac.\<close>

subsection \<open>Empty choice sets\<close>

lemma RAD_empty:
  assumes "P is RAD"
  shows "\<not> P (ades_obs ok0 s0 okOut {})"
  by (subst Healthy_if[OF assms, symmetric]; simp add: RAD_def RA_def RA1_obs)

lemma rad_d2ac_not_RAD:
  "\<not> (d2ac D is RAD)"
proof
  assume "d2ac D is RAD"
  then have "\<not> d2ac D (ades_obs False s0 True {})" for s0
    by (rule RAD_empty)
  then show False
    by (simp add: d2ac_def; pred_auto)
qed

lemma A3_not_RAD:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "\<not> (A3 P is RAD)"
proof
  assume "A3 P is RAD"
  then have "\<not> A3 P (ades_obs False s0 True {})" for s0
    by (rule RAD_empty)
  then show False
    by (simp add: A3_def; pred_auto)
qed

subsection \<open>Ordinary Reactive Merge Healthiness\<close>

text \<open>The merge argument is an ordinary merge on complete reactive observations.
  R2m enforces trace growth and removes the common history. RD1m supplies
  unstarted behaviour, RD2 permits a false output flag to become true, and
  R3cm supplies the waiting behaviour of R3c. These do not impose normality.
  The local split declaration ensures that ordinary reactive records are
  expanded before their design-record parent.\<close>

context
begin

declare des_vars.splits [alpha_splits del]

lemma par_by_merge_eval:
  fixes P Q :: "'s hrel"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) (x,z) = (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> merge_eval M x p q z)"
  by (simp add: par_by_merge_def; pred_auto)

lemma SymMerge_eval:
  fixes M :: "'s merge"
  shows "(M is SymMerge) \<longleftrightarrow> (\<forall>x p q z. merge_eval M x p q z = merge_eval M x q p z)"
  by (simp add: Healthy_def' fun_eq_iff; pred_auto; blast)

lemma AssocMerge_eval:
  fixes M :: "'s merge"
  assumes "M is SymMerge" "AssocMerge M"
  shows "(\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z) =
    (\<exists>u. merge_eval M x q r u \<and> merge_eval M x p u z)"
  using assms by (simp add: Healthy_def' AssocMerge_def fun_eq_iff; pred_auto; blast)

definition R3cm :: "('t::trace, 'a) rp merge \<Rightarrow> ('t, 'a) rp merge" where
  [pred]: "R3cm M = (\<lambda>(m,z). if rea_vars.wait\<^sub>v (mrg_prior\<^sub>v m)
    then RD1m skip\<^sub>m (m,z) else M (m,z))"

lemma RD1m_eval:
  "merge_eval (RD1m M) x p q z \<longleftrightarrow>
    merge_eval M x p q z \<or> (\<not> des_vars.ok\<^sub>v x \<and> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z)"
  by (pred_auto)

lemma R3cm_eval:
  "merge_eval (R3cm M) x p q z =
    (if rea_vars.wait\<^sub>v x then
      z = x \<or> (\<not> des_vars.ok\<^sub>v x \<and> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z)
     else merge_eval M x p q z)"
  by (pred_auto)

lemma RD1m_idem: "RD1m (RD1m M) = RD1m M"
  by (pred_auto)

lemma RD1m_mono: "M \<sqsubseteq> N \<Longrightarrow> RD1m M \<sqsubseteq> RD1m N"
  by (pred_auto)

lemma RD1m_Idempotent [closure]: "Idempotent RD1m"
  by (simp add: Idempotent_def RD1m_idem)

lemma RD1m_Monotonic [closure]: "Monotonic RD1m"
  by (auto simp: Monotonic_refine intro: RD1m_mono)

lemma R3cm_idem: "R3cm (R3cm M) = R3cm M"
  by (pred_auto)

lemma R3cm_mono: "M \<sqsubseteq> N \<Longrightarrow> R3cm M \<sqsubseteq> R3cm N"
  by (pred_auto)

lemma R3cm_Idempotent [closure]: "Idempotent R3cm"
  by (simp add: Idempotent_def R3cm_idem)

lemma R3cm_Monotonic [closure]: "Monotonic R3cm"
  by (auto simp: Monotonic_refine intro: R3cm_mono)

lemma RD1m_R3cm_commute: "RD1m (R3cm M) = R3cm (RD1m M)"
  by (pred_auto)

lemma RD1m_R2m_commute: "RD1m (R2m M) = R2m (RD1m M)"
  by (pred_auto)

lemma R2m_R3cm_commute: "R2m (R3cm M) = R3cm (R2m M)"
  by (pred_auto; metis minus_zero_eq)

lemma RD2_RD1m_commute: "RD2 (RD1m M) = RD1m (RD2 M)"
  by (simp add: RD2_def H2_split; pred_auto)

lemma RD2_R3cm_commute: "RD2 (R3cm M) = R3cm (RD2 M)"
  by (simp add: RD2_def H2_split; pred_auto)

lemma RD2_R2m_commute: "RD2 (R2m M) = R2m (RD2 M)"
  by (simp add: RD2_def H2_split; pred_auto)

end

text \<open>The four components commute. Their composite RADm is monotone and
  idempotent; its fixed points satisfy all four component conditions.
  The resulting ordinary parallel is RD-healthy for RD operands.\<close>

context
begin

declare des_vars.splits [alpha_splits del]

definition RADm :: "('t::trace, 'a) rp merge \<Rightarrow> ('t, 'a) rp merge" where
  "RADm M = RD1m (R3cm (R2m (RD2 M)))"

lemma RADm_idem: "RADm (RADm M) = RADm M"
  by (simp add: RADm_def RD2_RD1m_commute RD2_R3cm_commute RD2_R2m_commute
      RD1m_R2m_commute[symmetric] R2m_R3cm_commute RD1m_R3cm_commute[symmetric]
      RD1m_idem R3cm_idem R2m_idem RD2_idem)

lemma RADm_mono: "M \<sqsubseteq> N \<Longrightarrow> RADm M \<sqsubseteq> RADm N"
  by (simp add: RADm_def RD1m_mono R3cm_mono R2m_mono RD2_mono)

lemma RADm_healthy [closure]: "RADm M is RADm"
  by (simp add: Healthy_def' RADm_idem)

lemma RADm_Idempotent [closure]: "Idempotent RADm"
  by (simp add: Idempotent_def RADm_idem)

lemma RADm_Monotonic [closure]: "Monotonic RADm"
  by (auto simp: Monotonic_refine intro: RADm_mono)

lemma RADm_healths:
  "RADm M is RD1m" "RADm M is R3cm" "RADm M is R2m" "RADm M is RD2"
  by (simp_all add: Healthy_def' RADm_def
      RD2_RD1m_commute RD2_R3cm_commute RD2_R2m_commute
      RD1m_R2m_commute[symmetric] RD1m_R3cm_commute
      R2m_R3cm_commute RD1m_idem R3cm_idem R2m_idem RD2_idem)

lemma RADm_healthy_iff:
  "(M is RADm) \<longleftrightarrow> ((M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2))"
proof
  assume M: "M is RADm"
  show "(M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2)"
    using RADm_healths[of M] by (simp only: Healthy_if[OF M])
next
  assume "(M is RD1m) \<and> (M is R3cm) \<and> (M is R2m) \<and> (M is RD2)"
  then show "M is RADm" by (simp add: Healthy_def' RADm_def)
qed

lemma RADm_R1m:
  assumes "M is RADm"
  shows "M is R1m"
proof -
  have h: "M is R2m" using assms by (simp add: RADm_healthy_iff)
  have "R1m M = R1m (R2m M)" by (simp only: Healthy_if[OF h])
  also have "... = R2m M" by (simp add: R2m_def R1m_idem)
  also have "... = M" by (rule Healthy_if[OF h])
  finally show ?thesis by (simp only: Healthy_def')
qed

lemma R3cm_par_by_merge:
  fixes P Q :: "('t::trace, 'a) rp_hrel" and M :: "('t, 'a) rp merge"
  assumes "P is R3c" "Q is R3c" "M is R3cm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c"
proof -
  have wait: "R3c P (x,z) =
      (if rea_vars.wait\<^sub>v x then
        z = x \<or> (\<not> des_vars.ok\<^sub>v x \<and> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z)
       else P (x,z))" for P :: "('t,'a) rp_hrel" and x z
    by (pred_auto)
  have "R3c (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q) = (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q)"
  proof (rule ext)
    fix obs :: "('t, 'a) rp \<times> ('t, 'a) rp"
    obtain x z where obs: "obs = (x,z)" by (cases obs) auto
    show "R3c (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q) obs = (R3c P \<parallel>\<^bsub>R3cm M\<^esub> R3c Q) obs"
      unfolding obs
      by (cases "rea_vars.wait\<^sub>v x"; simp add: wait par_by_merge_eval R3cm_eval; blast intro: exI[where x=x])
  qed
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)]
        Healthy_if[OF assms(3)] Healthy_def')
qed

lemma RD_par_by_RADm [closure]:
  assumes "P is RD" "Q is RD" "M is RADm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD"
proof -
  have m: "M is RD1m" "M is R3cm" "M is R2m" "M is RD2" "M is R1m"
    using assms(3) RADm_R1m unfolding RADm_healthy_iff by auto
  have h: "(P \<parallel>\<^bsub>M\<^esub> Q) is R1" "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
    "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c" "(P \<parallel>\<^bsub>M\<^esub> Q) is RD1" "(P \<parallel>\<^bsub>M\<^esub> Q) is RD2"
    using assms(1,2) m
    by (auto intro: R1_par_by_merge R2_par_by_merge R3cm_par_by_merge
        RD1_par_by_merge RD2_par_by_merge RD_healths)
  show ?thesis
    using h R2_implies_R2c[OF h(2)]
    by (simp add: Healthy_def' RD_alt_def RH_def)
qed

lemma RADm_SymMerge:
  assumes "M is SymMerge"
  shows "RADm M is SymMerge"
  using assms
  by (simp add: RADm_def Healthy_def' fun_eq_iff RD2_def H2_split; pred_auto; blast)

lemma RADm_unstarted:
  assumes "\<not> des_vars.ok\<^sub>v x"
  shows "merge_eval (RADm M) x p q z \<longleftrightarrow> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z"
  using assms by (simp add: RADm_def R3cm_def; pred_auto)

end

subsection \<open>Choice-set lifting\<close>

text \<open>Every pair of branch states must have a merged output in the final set.
  The ordinary merge supplies the control, trace, waiting and refusal policy.\<close>

definition rad_lift_merge ::
  "('t::trace, 'e set) rp merge \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "rad_lift_merge M = (\<lambda>(m,out).
    let x = mrg_prior\<^sub>v m;
        p = mrg_left\<^sub>v m;
        q = mrg_right\<^sub>v m;
        X = achoices.ac\<^sub>v (des_vars.more p);
        Y = achoices.ac\<^sub>v (des_vars.more q);
        Z = achoices.ac\<^sub>v (des_vars.more out);
        s0 = astate.s\<^sub>v (des_vars.more x)
    in X \<noteq> {} \<and> Y \<noteq> {} \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z.
        merge_eval M
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v x, \<dots> = s0\<rparr>)
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v p, \<dots> = sL\<rparr>)
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v q, \<dots> = sR\<rparr>)
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v out, \<dots> = sOut\<rparr>)))"

lemma rad_p2ac_obs:
  "p2ac P (ades_obs ok0 s0 okOut Z) =
    (\<exists>sOut\<in>Z. P (\<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>,
                   \<lparr>ok\<^sub>v = okOut, \<dots> = sOut\<rparr>))"
  by (simp add: p2ac_def)

lemma rad_lift_merge_obs:
  "ades_merge_obs (rad_lift_merge M) ok0 s0 okL X okR Y okOut Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z.
      merge_eval M (\<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>)
        (\<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>)
        (\<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>)
        (\<lparr>ok\<^sub>v = okOut, \<dots> = sOut\<rparr>)))"
  by (simp add: rad_lift_merge_def Let_def)

lemma rad_lift_merge_mono:
  assumes "M \<sqsubseteq> N"
  shows "rad_lift_merge M \<sqsubseteq> rad_lift_merge N"
  using assms
  by (auto simp: pred_refine_iff rad_lift_merge_def Let_def split: prod.splits; blast)

lemma rad_lift_merge_SymMerge:
  assumes "M is SymMerge"
  shows "rad_lift_merge M is SymMerge"
proof -
  have sym: "merge_eval M x p q z = merge_eval M x q p z" for x p q z
    using assms by (simp add: SymMerge_eval)
  show ?thesis
    by (simp add: SymMerge_ades rad_lift_merge_def Let_def sym; blast)
qed

lemma rad_p2ac_RD1:
  "p2ac (RD1 P) = CSPA1 (p2ac P)"
  apply (rule ades_obs_ext)
  subgoal for b s c X
    by (cases b; cases c;
        auto simp: p2ac_def CSPA1_obs RD1_def rad_trace_extensions_def
          expr_defs lens_defs alpha_defs disj_pred_def conj_pred_def)
  done

lemma rad_p2ac_RD2:
  "p2ac (RD2 P) = CSPA2 (p2ac P)"
  apply (rule ades_obs_ext)
  apply (simp add: rad_p2ac_obs CSPA2_def RD2_def H2_obs H2_split)
  by (auto simp: expr_defs lens_defs des_vars.ok_def p2ac_def
        disj_pred_def conj_pred_def)

lemma rad_p2ac_RD:
  "p2ac (RD P) = RAD (p2ac P)"
  unfolding RD_alt_def RD2_RH_commute RD1_RH_commute
  by (simp only: rad_p2ac_R' rad_p2ac_RD1 rad_p2ac_RD2 RAD_def comp_apply
      Healthy_if[OF rad_p2ac_PBMH_ades])

lemma rad_p2ac_RD_closure:
  assumes "P is RD"
  shows "p2ac P is RAD"
  by (simp only: Healthy_def' rad_p2ac_RD[symmetric] Healthy_if[OF assms])

subsection \<open>RAD parallel by merge\<close>

definition rad_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e set) rp merge \<Rightarrow>
    ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = (P \<parallel>\<^bsub>rad_lift_merge M\<^esub> Q)"

lemma rad_par_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
  shows "p2ac P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> p2ac Q = p2ac (P \<parallel>\<^bsub>M\<^esub> Q)"
  unfolding rad_par_def
  apply (rule ades_obs_ext)
  apply (simp only: rad_p2ac_obs par_by_merge_eval
      ades_par_by_merge_eval choices_ex rad_lift_merge_obs[simplified])
  apply (simp only: des_vars.splits)
  by (blast intro: exI[where x="{_}"])

lemma rad_par_form:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = p2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
  using rad_par_p2ac[of "ac2p P" M "ac2p Q"]
  by (simp only: rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

lemma rad_par_ac2p:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) = (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
  by (simp only: rad_par_form[OF assms] rad_ac2p_p2ac_inverse')

lemma rad_par_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A2"
  by (simp add: rad_par_form[OF assms] Healthy_def')

text \<open>Closure transfers from ordinary RD parallel through p2ac. RADm is
  sufficient; no normality premise or excluded-output witness is required.\<close>

lemma rad_ac2p_RD:
  assumes "P is RAD" "P is A2"
  shows "ac2p P is RD"
proof -
  have "p2ac (RD (ac2p P)) = P"
    by (simp only: rad_p2ac_RD rad_p2ac_ac2p_RAD_A2'[OF assms] Healthy_if[OF assms(1)])
  then have "RD (ac2p P) = ac2p P"
    by (metis rad_ac2p_p2ac_inverse')
  then show ?thesis by (simp only: Healthy_def')
qed

lemma rad_par_RAD [closure]:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2" "M is RADm"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is RAD"
  unfolding rad_par_form[OF assms(1-4)]
  by (rule rad_p2ac_RD_closure,
      rule RD_par_by_RADm[OF rad_ac2p_RD[OF assms(1,3)] rad_ac2p_RD[OF assms(2,4)] assms(5)])

subsection \<open>Algebra\<close>

lemma rad_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "P1 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q1 \<sqsubseteq> P2 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q2"
  unfolding rad_par_def
  using assms
  by (auto simp: pred_refine_iff ades_par_by_merge_eval split: prod.splits; blast)

lemma rad_par_comm:
  assumes "rad_lift_merge M is SymMerge"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> P"
  unfolding rad_par_def
  by (rule par_by_merge_comm; use assms in \<open>simp add: Healthy_def'\<close>)

lemma rad_par_comm_merge:
  assumes "M is SymMerge"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> P"
  by (rule rad_par_comm[OF rad_lift_merge_SymMerge[OF assms]])

lemma rad_par_assoc_state:
  assumes "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2"
    "M is RADm"
    and assoc: "\<And>x p q r z.
      (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z) =
      (\<exists>u. merge_eval M x q r u \<and> merge_eval M x p u z)"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R)"
proof -
  have ordinary: "((D \<parallel>\<^bsub>M\<^esub> E) \<parallel>\<^bsub>M\<^esub> F) = (D \<parallel>\<^bsub>M\<^esub> (E \<parallel>\<^bsub>M\<^esub> F))" for D E F
    by (rule ext; simp only: split_paired_all par_by_merge_eval; use assoc in blast)
  have pq: "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is RAD" "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A2"
    by (simp_all add: rad_par_RAD[OF assms(1,2,4,5,7)] rad_par_A2[OF assms(1,2,4,5)])
  have qr: "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) is RAD" "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) is A2"
    by (simp_all add: rad_par_RAD[OF assms(2,3,5,6,7)] rad_par_A2[OF assms(2,3,5,6)])
  show ?thesis
    by (simp only: rad_par_form[OF pq(1) assms(3) pq(2) assms(6)]
        rad_par_form[OF assms(1) qr(1) assms(4) qr(2)]
        rad_par_ac2p[OF assms(1,2,4,5)]
        rad_par_ac2p[OF assms(2,3,5,6)] ordinary)
qed

lemma rad_par_assoc:
  assumes "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2"
    "M is RADm" "M is SymMerge" "AssocMerge M"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R)"
  by (rule rad_par_assoc_state[OF assms(1-7) AssocMerge_eval[OF assms(8,9)]])


subsection \<open>Basic merge example\<close>

definition rad_basic_merge :: "('t::trace, 'e set) rp merge" where
  "rad_basic_merge = (\<lambda>(m,out).
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
      des_vars.ok\<^sub>v (mrg_right\<^sub>v m) \<longrightarrow> des_vars.ok\<^sub>v out) \<and>
    basic_merge_state
      (des_vars.more (mrg_prior\<^sub>v m))
      (des_vars.more (mrg_left\<^sub>v m))
      (des_vars.more (mrg_right\<^sub>v m))
      (des_vars.more out))"

lemma rad_lift_basic_merge_obs:
  "ades_merge_obs (rad_lift_merge rad_basic_merge) ok0 s0 okL X okR Y okOut Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> okOut) \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z. basic_merge_state s0 sL sR sOut))"
  apply (simp only: rad_lift_merge_obs)
  by (simp add: rad_basic_merge_def; blast)

lemma rad_lift_basic_trace_agreement:
  assumes "ades_merge_obs (rad_lift_merge rad_basic_merge)
      ok0 s0 okL X okR Y okOut Z"
    "sL \<in> X" "sR \<in> Y"
  shows "rad_tr\<^sub>v sL = rad_tr\<^sub>v sR"
  using assms
  apply (simp only: rad_lift_basic_merge_obs)
  unfolding basic_merge_state_def
  by fastforce

lemma rad_lift_basic_singletons:
  "ades_merge_obs (rad_lift_merge rad_basic_merge)
      ok0 s0 True {sL} True {sR} True Z =
    (\<exists>sOut\<in>Z. basic_merge_state s0 sL sR sOut)"
  by (simp add: rad_lift_basic_merge_obs[simplified])

lemma rad_lift_basic_same:
  "ades_merge_obs (rad_lift_merge rad_basic_merge)
    ok0 s0 True {s0} True {s0} True {s0}"
  by (simp add: rad_lift_basic_merge_obs[simplified] basic_merge_state_def)


subsubsection \<open>Repairing the Basic Merge\<close>

text \<open>The basic merge is not RADm-healthy. Applying RADm repairs unstarted
  and waiting behaviour. On started, non-waiting observations it preserves the
  original policy when both branch traces extend the initial trace. These
  trace premises hold for outputs admitted by R1-healthy operands.\<close>

context
begin

declare des_vars.splits [alpha_splits del]

lemma rad_basic_merge_not_RADm:
  "\<not> ((rad_basic_merge :: ('t::trace, 'e set) rp merge) is RADm)"
proof -
  have "\<not> ((rad_basic_merge :: ('t, 'e set) rp merge) is RD1m)"
    apply (simp add: Healthy_def' fun_eq_iff rad_basic_merge_def basic_merge_state_def)
    apply (pred_simp)
    by (metis (mono_tags, lifting) order_refl)
  then show ?thesis by (simp add: RADm_healthy_iff)
qed

lemma rad_basic_merge_RD2: "rad_basic_merge is RD2"
  by (simp add: Healthy_def' RD2_def H2_split rad_basic_merge_def basic_merge_state_def; pred_auto)

lemma rad_basic_merge_R2m:
  assumes "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p" "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v q"
  shows "merge_eval (R2m rad_basic_merge) x p q z = merge_eval rad_basic_merge x p q z"
  using assms
  apply (simp add: rad_basic_merge_def basic_merge_state_def)
  apply (pred_simp)
  by (metis diff_add_cancel_left')

lemma RADm_basic_merge_running:
  assumes "des_vars.ok\<^sub>v x" "\<not> rea_vars.wait\<^sub>v x"
    "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p" "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v q"
  shows "merge_eval (RADm rad_basic_merge) x p q z = merge_eval rad_basic_merge x p q z"
  using assms
  by (simp add: RADm_def Healthy_if[OF rad_basic_merge_RD2]
      RD1m_eval R3cm_eval rad_basic_merge_R2m[OF assms(3,4)])

lemma RADm_basic_merge_waiting:
  assumes "des_vars.ok\<^sub>v x" "rea_vars.wait\<^sub>v x"
  shows "merge_eval (RADm rad_basic_merge) x p q z \<longleftrightarrow> z = x"
  using assms by (simp add: RADm_def R3cm_def RD1m_def; pred_auto)

end

subsubsection \<open>Post-State-Dependent Failure\<close>

text \<open>The seed below constrains the final refusal set, including on failure.
  With RD true as each operand, started running parallel accepts an output
  exactly when its trace extends the initial trace and its refusal set is empty.
  In particular, the failure slice still depends on the post-state. The raw
  p2ac correspondence transfers this example to RAD and A2 operands.\<close>

context
begin

declare des_vars.splits [alpha_splits del]

lemma RADm_post_ref_example:
  fixes x z :: "('t::trace, 'e set) rp"
  assumes "des_vars.ok\<^sub>v x" "\<not> rea_vars.wait\<^sub>v x"
  shows "(RD true \<parallel>\<^bsub>RADm (\<lambda>(m,out). rea_vars.more out = {})\<^esub> RD true) (x,z) \<longleftrightarrow>
    rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z \<and> rea_vars.more z = {}"
proof -
  let ?N = "RADm (\<lambda>(m,out). rea_vars.more out = {})"
  have d: "RD true (x,p) \<longleftrightarrow> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p" for p
    using assms by (cases x; cases p; simp add: RD2_def H2_split; pred_auto)
  have n: "merge_eval ?N x p q z \<longleftrightarrow> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z \<and> rea_vars.more z = {}"
    for p q
    using assms by (cases x; cases z; simp add: RADm_def RD2_def H2_split; pred_auto)
  show ?thesis
    by (simp only: par_by_merge_eval d n; blast intro: exI[where x=x])
qed

end

end
