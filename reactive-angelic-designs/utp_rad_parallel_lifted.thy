section \<open>Lifting reactive merges to choice sets\<close>

theory utp_rad_parallel_lifted
  imports utp_rad_parallel_examples utp_rad_csp
begin

text \<open>This candidate lifts full reactive merge observations. It uses p2ac rather
  than d2ac, and applies RAD after parallel. The correspondence therefore has
  RD after ordinary parallel too. It does not replace the generic rad_par.\<close>

subsection \<open>Why the AD completion cannot be reused directly\<close>

lemma RAD_empty:
  assumes "P is RAD"
  shows "\<not> P (ades_obs ok0 s0 okOut {})"
  by (subst Healthy_if[OF assms, symmetric]; simp add: RAD_def RA_def RA1_obs)

lemma rad_d2ac_not_RAD:
  "\<not> (rad_d2ac D is RAD)"
proof
  assume "rad_d2ac D is RAD"
  then have "\<not> rad_d2ac D (ades_obs False s0 True {})" for s0
    by (rule RAD_empty)
  then show False
    by (simp add: rad_d2ac_def d2ac_def; pred_auto)
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

subsection \<open>Choice-set lifting and raw correspondence\<close>

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
          (rad2csp_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v x, \<dots> = s0\<rparr>)
          (rad2csp_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v p, \<dots> = sL\<rparr>)
          (rad2csp_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v q, \<dots> = sR\<rparr>)
          (rad2csp_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v out, \<dots> = sOut\<rparr>)))"

lemma rad_p2ac_obs:
  "rad_p2ac P (ades_obs ok0 s0 okOut Z) =
    (\<exists>sOut\<in>Z. P (rad2csp_obs \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>,
                  rad2csp_obs \<lparr>ok\<^sub>v = okOut, \<dots> = sOut\<rparr>))"
  by (simp add: rad_p2ac_def p2ac_def csp2rad_rel_def)

lemma rad_lift_merge_obs:
  "ades_merge_obs (rad_lift_merge M) ok0 s0 okL X okR Y okOut Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z.
      merge_eval M (rad2csp_obs \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>)
        (rad2csp_obs \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>)
        (rad2csp_obs \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>)
        (rad2csp_obs \<lparr>ok\<^sub>v = okOut, \<dots> = sOut\<rparr>)))"
  by (simp add: rad_lift_merge_def Let_def)

lemma csp_obs_ex:
  "(\<exists>p :: ('t::trace, 'e set) rp. F p) =
    (\<exists>okL sL. F (rad2csp_obs \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>))"
proof
  assume "\<exists>p. F p"
  then obtain p where "F p" by blast
  have rep: "rad2csp_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v (csp2rad_obs p),
    \<dots> = des_vars.more (csp2rad_obs p)\<rparr> = p"
    by (simp add: csp2rad_obs_def rad2csp_obs_def)
  show "\<exists>okL sL. F (rad2csp_obs \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>)"
    using \<open>F p\<close> rep by metis
next
  assume "\<exists>okL sL. F (rad2csp_obs \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>)"
  then show "\<exists>p. F p" by blast
qed

lemma flat_parallel_obs:
  "(P \<parallel>\<^bsub>M\<^esub> Q) (x,out) =
    (\<exists>p q. P (x,p) \<and> Q (x,q) \<and> merge_eval M x p q out)"
  by (simp add: par_by_merge_def; pred_auto)

lemma rad_lift_merge_p2ac:
  "rad_p2ac (P \<parallel>\<^bsub>M\<^esub> Q) =
    (rad_p2ac P \<parallel>\<^sub>A\<^sub>D\<^bsub>rad_lift_merge M\<^esub> rad_p2ac Q)"
  apply (rule ades_obs_ext)
  apply (simp only: rad_p2ac_obs flat_parallel_obs csp_obs_ex
    ades_par_eval choices_ex rad_lift_merge_obs[simplified])
  by (blast intro: exI[where x="{_}"])

lemma rad_lift_merge_ac2p:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "rad_ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>rad_lift_merge M\<^esub> Q) =
    (rad_ac2p P \<parallel>\<^bsub>M\<^esub> rad_ac2p Q)"
  using arg_cong[where f=rad_ac2p,
    OF rad_lift_merge_p2ac[of "rad_ac2p P" M "rad_ac2p Q"]]
  by (simp only: rad_ac2p_p2ac_inverse'
      rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)] rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

lemma rad_lift_merge_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>rad_lift_merge M\<^esub> Q) is A2"
proof -
  have form: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>rad_lift_merge M\<^esub> Q) =
      rad_p2ac (rad_ac2p P \<parallel>\<^bsub>M\<^esub> rad_ac2p Q)"
    by (simp only: rad_lift_merge_p2ac rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
        rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])
  show ?thesis by (simp add: form rad_p2ac_def Healthy_def')
qed

subsection \<open>Reactive-design healthiness and completed parallel\<close>

lemma rad_p2ac_RD1:
  "rad_p2ac (RD1 P) = CSPA1 (rad_p2ac P)"
  apply (rule ades_obs_ext)
  apply (simp add: rad_p2ac_obs CSPA1_obs RD1_def rad2csp_obs_def
        rad_trace_extensions_def)
  by (auto simp: pred expr_simps des_vars.ok_def rea_vars.tr_def
      subst_app_def subst_upd_def subst_id_def)

lemma rad_p2ac_RD2:
  "rad_p2ac (RD2 P) = CSPA2 (rad_p2ac P)"
  apply (rule ades_obs_ext)
  apply (simp add: rad_p2ac_obs CSPA2_def RD2_def H2_obs H2_split
        rad2csp_obs_def)
  by (auto simp: expr_defs lens_defs des_vars.ok_def rad_p2ac_def p2ac_def
      csp2rad_rel_def rad2csp_obs_def disj_pred_def conj_pred_def)

lemma rad_p2ac_RD:
  "rad_p2ac (RD P) = RAD (rad_p2ac P)"
  unfolding RD_alt_def RD2_RH_commute RD1_RH_commute
  by (simp only: rad_p2ac_R' rad_p2ac_RD1 rad_p2ac_RD2 RAD_def comp_apply
      Healthy_if[OF rad_p2ac_PBMH_ades])

lemma rad_p2ac_RD_closure:
  assumes "P is RD"
  shows "rad_p2ac P is RAD"
  by (simp only: Healthy_def' rad_p2ac_RD[symmetric] Healthy_if[OF assms])

definition rad_par_lifted ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e set) rp merge \<Rightarrow>
    ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
where
  "rad_par_lifted P M Q = RAD (P \<parallel>\<^sub>A\<^sub>D\<^bsub>rad_lift_merge M\<^esub> Q)"

lemma rad_par_lifted_RAD:
  "rad_par_lifted P M Q is RAD"
  by (simp add: rad_par_lifted_def RAD_healthy)

lemma rad_par_lifted_p2ac:
  "rad_par_lifted (rad_p2ac P) M (rad_p2ac Q) =
    rad_p2ac (RD (P \<parallel>\<^bsub>M\<^esub> Q))"
  by (simp only: rad_par_lifted_def rad_lift_merge_p2ac[symmetric]
      rad_p2ac_RD)

lemma rad_par_lifted_form:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "rad_par_lifted P M Q =
    rad_p2ac (RD (rad_ac2p P \<parallel>\<^bsub>M\<^esub> rad_ac2p Q))"
  using rad_par_lifted_p2ac[of "rad_ac2p P" M "rad_ac2p Q"]
  by (simp only: rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

lemma rad_par_lifted_ac2p:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "rad_ac2p (rad_par_lifted P M Q) =
    RD (rad_ac2p P \<parallel>\<^bsub>M\<^esub> rad_ac2p Q)"
  by (simp only: rad_par_lifted_form[OF assms] rad_ac2p_p2ac_inverse')

lemma rad_par_lifted_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "rad_par_lifted P M Q is A2"
  by (simp add: rad_par_lifted_form[OF assms] rad_p2ac_def Healthy_def')

subsection \<open>Lifting merge healthiness operators\<close>

text \<open>Restricting a lifted merge to singleton observations recovers the ordinary
  merge. This lets us transfer idempotence and monotonicity. These algebraic
  facts alone do not establish a parallel closure law for a chosen condition.\<close>

definition rad_lower_merge ::
  "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e set) rp merge"
where
  "rad_lower_merge N = (\<lambda>(m,out).
    let x = csp2rad_obs (mrg_prior\<^sub>v m);
        p = csp2rad_obs (mrg_left\<^sub>v m);
        q = csp2rad_obs (mrg_right\<^sub>v m);
        z = csp2rad_obs out
    in ades_merge_obs N (des_vars.ok\<^sub>v x) (des_vars.more x)
        (des_vars.ok\<^sub>v p) {des_vars.more p}
        (des_vars.ok\<^sub>v q) {des_vars.more q}
        (des_vars.ok\<^sub>v z) {des_vars.more z})"

lemma rad_lower_lift_merge [simp]:
  "rad_lower_merge (rad_lift_merge M) = M"
  apply (rule ext)
  apply (auto simp: rad_lower_merge_def rad_lift_merge_obs[simplified]
      Let_def csp2rad_obs_def rad2csp_obs_def split: prod.splits)
  by (metis (mono_tags, lifting) mrg.surjective old.unit.exhaust rea_vars.surjective)+

lemma rad_lift_merge_mono:
  assumes "M \<sqsubseteq> N"
  shows "rad_lift_merge M \<sqsubseteq> rad_lift_merge N"
  using assms by (auto simp: pred_refine_iff rad_lift_merge_def Let_def split: prod.splits; blast)

lemma rad_lower_merge_mono:
  assumes "M \<sqsubseteq> N"
  shows "rad_lower_merge M \<sqsubseteq> rad_lower_merge N"
  using assms by (auto simp: pred_refine_iff rad_lower_merge_def Let_def split: prod.splits)

definition rad_lift_health where
  "rad_lift_health H M = rad_lift_merge (H (rad_lower_merge M))"

lemma rad_lift_health_idem:
  assumes "Idempotent H"
  shows "rad_lift_health H (rad_lift_health H M) = rad_lift_health H M"
  using assms by (simp add: rad_lift_health_def Idempotent_def)

lemma rad_lift_health_mono:
  assumes "Monotonic H" "M \<sqsubseteq> N"
  shows "rad_lift_health H M \<sqsubseteq> rad_lift_health H N"
  unfolding rad_lift_health_def
  by (rule rad_lift_merge_mono;
      use assms rad_lower_merge_mono[OF assms(2)] in
        \<open>auto simp: Monotonic_refine\<close>)

text \<open>The remaining closure obligation is on ordinary parallel. If it is
  RD-healthy, the raw lifted parallel is already RAD-healthy.\<close>

lemma rad_lift_merge_RAD:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
    "(rad_ac2p P \<parallel>\<^bsub>M\<^esub> rad_ac2p Q) is RD"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>rad_lift_merge M\<^esub> Q) is RAD"
  using rad_p2ac_RD_closure[OF assms(5)]
  by (simp only: rad_lift_merge_p2ac
      rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

lemma rad_par_lifted_ac2p_RD:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
    "(rad_ac2p P \<parallel>\<^bsub>M\<^esub> rad_ac2p Q) is RD"
  shows "rad_ac2p (rad_par_lifted P M Q) =
    (rad_ac2p P \<parallel>\<^bsub>M\<^esub> rad_ac2p Q)"
  by (simp only: rad_par_lifted_ac2p[OF assms(1-4)] Healthy_if[OF assms(5)])

lemma rad_lift_health_lift:
  "rad_lift_health H (rad_lift_merge M) = rad_lift_merge (H M)"
  by (simp add: rad_lift_health_def)

lemma rad_lift_health_fixed:
  assumes "M is H"
  shows "rad_lift_merge M is rad_lift_health H"
  by (simp only: Healthy_def' rad_lift_health_lift Healthy_if[OF assms])

lemma rad_lift_R1m_Idempotent:
  "Idempotent (rad_lift_health R1m)"
  using rad_lift_health_idem[OF R1m_Idempotent]
  by (auto simp: Idempotent_def)

lemma rad_lift_R1m_Monotonic:
  "Monotonic (rad_lift_health R1m)"
  using rad_lift_health_mono[OF R1m_Monotonic]
  by (auto simp: Monotonic_refine)

subsection \<open>Basic trace merge\<close>

text \<open>This policy keeps the state constraint on failure and allows okOut when
  either branch fails. Refusals are unconstrained. The lemmas check the raw
  lifting; startup and waiting healthiness still come from the outer RAD.
  This is not a correspondence theorem for the library's stateful rdes_par.\<close>

definition rad_basic_merge :: "('t::trace, 'e set) rp merge" where
  "rad_basic_merge = (\<lambda>(m,out).
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
      des_vars.ok\<^sub>v (mrg_right\<^sub>v m) \<longrightarrow> des_vars.ok\<^sub>v out) \<and>
    basic_merge_state
      (des_vars.more (csp2rad_obs (mrg_prior\<^sub>v m)))
      (des_vars.more (csp2rad_obs (mrg_left\<^sub>v m)))
      (des_vars.more (csp2rad_obs (mrg_right\<^sub>v m)))
      (des_vars.more (csp2rad_obs out)))"

lemma rad_lift_basic_merge_obs:
  "ades_merge_obs (rad_lift_merge rad_basic_merge) ok0 s0 okL X okR Y okOut Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> okOut) \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z. basic_merge_state s0 sL sR sOut))"
  apply (simp only: rad_lift_merge_obs)
  apply (simp add: rad_basic_merge_def csp2rad_obs_def rad2csp_obs_def basic_merge_state_def)
  by blast

lemma rad_lift_basic_trace_agreement:
  assumes "ades_merge_obs (rad_lift_merge rad_basic_merge)
      ok0 s0 okL X okR Y okOut Z"
    "sL \<in> X" "sR \<in> Y"
  shows "rad_state.tr\<^sub>v sL = rad_state.tr\<^sub>v sR"
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

end
