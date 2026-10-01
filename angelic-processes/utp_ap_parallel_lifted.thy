section \<open>Investigating lifted parallel for angelic processes\<close>

theory utp_ap_parallel_lifted
  imports utp_ap_parallel utp_ap_nd
    "UTP-Reactive-Angelic-Designs.utp_rad_parallel_lifted"
begin

text \<open>We reuse rad_lift_merge because AP and RAD share the observation alphabet.
  The existing ap_par has merge-based AP closure. The separate ap_par_via_rad
  below gives correspondence by construction, but identifies processes with
  the same RA1 image. No equality between these two operators is claimed.\<close>

subsection \<open>Conversions and their limits\<close>

text \<open>H1 maps RAD into AP; RA1 maps AP into RAD. The reverse round trip is
  generally a refinement. Chaos shows why equality needs a premise.\<close>

lemma rad_p2ac_not_AP:
  "\<not> (rad_p2ac D is AP)"
proof
  assume "rad_p2ac D is AP"
  then have "rad_p2ac D (ades_obs False s0 True {})" for s0
    by (rule AP_healthy_not_ok_eval; simp)
  then show False by (simp add: rad_p2ac_obs)
qed

lemma ap_rad_roundtrip_refine:
  assumes "P is AP"
  shows "P \<sqsubseteq> H1 (RA1 P)"
  using H1_RA1_AP_refine[of P]
  by (simp only: comp_apply Healthy_if[OF assms])

lemma ap_rad_roundtrip_NDAP:
  assumes "P is AP" "P is NDAP"
  shows "H1 (RA1 P) = P"
  using H1_RA1_NDAP_AP[of P]
  by (simp only: comp_apply Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])

lemma ap_ac2p_via_RA1:
  assumes "P is AP"
  shows "rad_ac2p (RA1 P) = R1 (rad_ac2p P)"
  by (rule rad_ac2p_RA1[OF AP_is_PBMH_ades[OF assms], simplified comp_apply])

lemma Chaos_AP_RA1:
  "RA1 (Chaos\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design) =
    Chaos\<^sub>R\<^sub>A\<^sub>D"
  by (simp only: Chaos_AP_def RA1_AP_RAD[simplified comp_apply]
      design_false_pre Chaos_RAD_RAD)

lemma Chaos_AP_roundtrip:
  "H1 (RA1 (Chaos\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design)) =
    ChaosCSP\<^sub>A\<^sub>P"
  by (simp only: Chaos_AP_RA1 H1_Chaos_RAD)

lemma Chaos_AP_empty:
  assumes "\<not> rad_state.wait\<^sub>v s0"
  shows "Chaos\<^sub>A\<^sub>P (ades_obs True s0 True {})"
  using assms
  by (simp add: Chaos_AP_design; pred_auto)

lemma ChaosCSP_AP_empty:
  "\<not> ChaosCSP\<^sub>A\<^sub>P (ades_obs True s0 True {})"
  by (simp add: ChaosCSP_AP_design RA1_obs; pred_auto)

lemma Chaos_AP_neq_ChaosCSP:
  "(Chaos\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design) \<noteq> ChaosCSP\<^sub>A\<^sub>P"
proof
  let ?s0 = "\<lparr>rad_state.tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = False\<rparr> :: ('t, 'e) rad_state"
  assume eq: "(Chaos\<^sub>A\<^sub>P :: ('t, 'e) reactive_angelic_design) = ChaosCSP\<^sub>A\<^sub>P"
  have "Chaos\<^sub>A\<^sub>P (ades_obs True ?s0 True {})"
    by (rule Chaos_AP_empty; simp)
  then show False using eq ChaosCSP_AP_empty[of ?s0] by simp
qed

lemma Chaos_AP_same_RAD:
  "RA1 (Chaos\<^sub>A\<^sub>P :: ('t::trace, 'e) reactive_angelic_design) =
    RA1 ChaosCSP\<^sub>A\<^sub>P"
  by (simp only: Chaos_AP_RA1 RA1_ChaosCSP_AP)

subsection \<open>Ordinary reactive-design correspondence\<close>

text \<open>The ordinary-to-AP map is H1 after rad_p2ac. The AP-to-ordinary map is
  rad_ac2p after RA1. Non-divergence is sufficient for the AP round trip;
  it is not required by the parallel construction below.\<close>

lemma H1_A2_closure:
  assumes "P is A2"
  shows "H1 P is A2"
  apply (rule Healthy_intro, rule ades_obs_ext)
  apply (simp only: A2_obs H1_obs)
  using A2_obs[of P, simplified Healthy_if[OF assms]]
  by blast

lemma ap_from_RD:
  assumes "P is RD"
  shows "H1 (rad_p2ac P) is AP"
  by (rule H1_RAD_AP_closure[OF rad_p2ac_RD_closure[OF assms]])

lemma ap_RD_roundtrip:
  assumes "P is RD"
  shows "rad_ac2p (RA1 (H1 (rad_p2ac P))) = P"
  by (simp only: RA1_H1_RAD_healthy[OF rad_p2ac_RD_closure[OF assms],
        simplified comp_apply] rad_ac2p_p2ac_inverse')

lemma ap_RD_reverse_roundtrip:
  assumes "P is AP" "P is A2"
  shows "H1 (rad_p2ac (rad_ac2p (RA1 P))) = H1 (RA1 P)"
  by (simp only: rad_p2ac_ac2p_RAD_A2'[
      OF RA1_AP_RAD_closure[OF assms(1)] RA1_A2_closure[OF assms(2)]])

lemma ap_RD_reverse_roundtrip_NDAP:
  assumes "P is AP" "P is A2" "P is NDAP"
  shows "H1 (rad_p2ac (rad_ac2p (RA1 P))) = P"
  by (simp only: ap_RD_reverse_roundtrip[OF assms(1,2)]
      ap_rad_roundtrip_NDAP[OF assms(1,3)])

subsection \<open>Parallel transported through RAD\<close>

text \<open>This construction uses the existing RAD candidate without a new set lift.
  Its ordinary correspondence retains RD after parallel.\<close>

definition ap_par_via_rad ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e set) rp merge \<Rightarrow>
   ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
where
  "ap_par_via_rad P M Q = H1 (rad_par_lifted (RA1 P) M (RA1 Q))"

lemma ap_par_via_rad_AP:
  "ap_par_via_rad P M Q is AP"
  unfolding ap_par_via_rad_def
  by (rule H1_RAD_AP_closure[OF rad_par_lifted_RAD])

lemma ap_par_via_rad_RA1:
  "RA1 (ap_par_via_rad P M Q) = rad_par_lifted (RA1 P) M (RA1 Q)"
  unfolding ap_par_via_rad_def
  by (rule RA1_H1_RAD_healthy[OF rad_par_lifted_RAD, simplified comp_apply])

lemma ap_par_via_rad_H1:
  assumes "P is RAD" "Q is RAD"
  shows "ap_par_via_rad (H1 P) M (H1 Q) = H1 (rad_par_lifted P M Q)"
  by (simp only: ap_par_via_rad_def
      RA1_H1_RAD_healthy[OF assms(1), simplified comp_apply]
      RA1_H1_RAD_healthy[OF assms(2), simplified comp_apply])

lemma ap_par_via_rad_A2:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2"
  shows "ap_par_via_rad P M Q is A2"
  unfolding ap_par_via_rad_def
  by (rule H1_A2_closure, rule rad_par_lifted_A2;
      simp add: assms RA1_AP_RAD_closure RA1_A2_closure)

lemma ap_par_via_rad_ac2p:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2"
  shows "rad_ac2p (RA1 (ap_par_via_rad P M Q)) =
    RD (rad_ac2p (RA1 P) \<parallel>\<^bsub>M\<^esub> rad_ac2p (RA1 Q))"
  unfolding ap_par_via_rad_RA1
  by (rule rad_par_lifted_ac2p;
      simp add: assms RA1_AP_RAD_closure RA1_A2_closure)

lemma ap_par_via_rad_p2ac:
  assumes "P is RD" "Q is RD"
  shows "ap_par_via_rad (H1 (rad_p2ac P)) M (H1 (rad_p2ac Q)) =
    H1 (rad_p2ac (RD (P \<parallel>\<^bsub>M\<^esub> Q)))"
  by (simp only: ap_par_via_rad_H1[OF rad_p2ac_RD_closure[OF assms(1)]
        rad_p2ac_RD_closure[OF assms(2)]] rad_par_lifted_p2ac)

lemma ap_par_via_rad_roundtrip:
  "H1 (RA1 (ap_par_via_rad P M Q)) = ap_par_via_rad P M Q"
  by (subst ap_par_via_rad_RA1; simp only: ap_par_via_rad_def)

lemma ap_par_via_rad_normalise_operands:
  "ap_par_via_rad (H1 (RA1 (AP P))) M (H1 (RA1 (AP Q))) =
    ap_par_via_rad (AP P) M (AP Q)"
  by (simp only: ap_par_via_rad_def
    RA1_H1_RAD_healthy[OF RA1_AP_RAD_closure[OF AP_healthy], simplified comp_apply])

lemma ap_par_via_rad_Chaos:
  "ap_par_via_rad Chaos\<^sub>A\<^sub>P M Q = ap_par_via_rad ChaosCSP\<^sub>A\<^sub>P M Q"
  by (simp only: ap_par_via_rad_def Chaos_AP_same_RAD)

subsection \<open>The existing AP operator with a lifted basic merge\<close>

text \<open>APOKM is already monotone and idempotent and gives AP closure. For the
  basic merge, it leaves the lifted policy unchanged at a started, nonwaiting
  prior with zero trace. The global correspondence of this operator remains
  open. In particular, the rule below rejects an empty final set even when a
  branch fails; this must be considered when choosing the failure semantics.\<close>

lemma ap_lift_merge_APOKM:
  "APOKM (rad_lift_merge M) is APOKM"
  by (rule APOKM_healthy)

lemma ap_lift_merge_AP:
  assumes "P is AP" "Q is AP"
  shows "ap_par P (rad_lift_merge M) Q is AP"
  by (rule ap_par_AP_closure[OF assms])

lemma ap_lift_basic_active:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "ades_merge_obs (APOKM (rad_lift_merge rad_basic_merge))
    True s0 okL X okR Y okOut Z =
    ades_merge_obs (rad_lift_merge rad_basic_merge)
      True s0 okL X okR Y okOut Z"
  by (auto simp: APOKM_active[simplified, OF assms]
      rad_lift_basic_merge_obs[simplified]; blast)

lemma ap_par_lift_basic_active:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "ap_par P (rad_lift_merge rad_basic_merge) Q (ades_obs True s0 okOut Z) =
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>rad_lift_merge rad_basic_merge\<^esub> Q)
      (ades_obs True s0 okOut Z)"
  by (simp only: ap_par_eval ades_par_eval choices_ex
      ap_lift_basic_active[OF assms, simplified])

lemma ap_par_lift_basic_empty:
  assumes "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "\<not> ap_par P (rad_lift_merge rad_basic_merge) Q
    (ades_obs True s0 okOut {})"
  by (subst ap_par_lift_basic_active[OF assms];
      auto simp: ades_par_eval choices_ex rad_lift_basic_merge_obs[simplified])

lemma PBMH_A2_nonempty_singleton:
  assumes "P is PBMH_ades" "P is A2" "X \<noteq> {}"
    "P (ades_obs ok0 s0 okOut X)"
  shows "\<exists>sL\<in>X. P (ades_obs ok0 s0 okOut {sL})"
proof -
  have up: "P (ades_obs ok0 s0 okOut {}) \<Longrightarrow>
      P (ades_obs ok0 s0 okOut {sL})" for sL
    using PBMH_ades_obs[of P ok0 s0 okOut "{sL}"]
    by (auto simp only: Healthy_if[OF assms(1)] intro: exI[where x="{}"])
  show ?thesis
    using A2_obs[of P ok0 s0 okOut X] up assms(3,4)
    by (simp only: Healthy_if[OF assms(2)]; blast)
qed

lemma ap_par_lift_basic_active_obs:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2"
    "rad_state.tr\<^sub>v s0 = 0" "\<not> rad_state.wait\<^sub>v s0"
  shows "ap_par P (rad_lift_merge rad_basic_merge) Q (ades_obs True s0 okOut Z) =
    (\<exists>okL sL okR sR. \<exists>sOut\<in>Z.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (okL \<and> okR \<longrightarrow> okOut) \<and> basic_merge_state s0 sL sR sOut)"
  apply (subst ap_par_lift_basic_active[OF assms(5,6)])
  apply (simp only: ades_par_eval choices_ex rad_lift_basic_merge_obs[simplified])
  apply (rule iffI)
  subgoal
    using PBMH_A2_nonempty_singleton[OF AP_is_PBMH_ades[OF assms(1)] assms(3)]
      PBMH_A2_nonempty_singleton[OF AP_is_PBMH_ades[OF assms(2)] assms(4)]
    by metis
  subgoal by (fastforce intro: exI[where x="{_}"])
  done

end
