section \<open>Angelic process parallel by merge\<close>

theory utp_ap_parallel
  imports utp_ap_nd
    "UTP-Reactive-Angelic-Designs.utp_rad_parallel"
begin

text \<open>This branch uses parallel through RAD as the sole AP operator.
  It has ordinary reactive-design mapping laws, but can identify distinct
  divergent processes. No equivalence with the former direct operator is claimed.\<close>
subsection \<open>Parallel transported through RAD\<close>

text \<open>This construction uses the RAD parallel operator without a new set lift.
  Closure follows from healthy operands and an ORDm-healthy merge.\<close>

definition ap_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e set) rp merge \<Rightarrow>
   ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>P\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "ap_par P M Q = H1 (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> RA1 Q)"

lemma ap_par_AP:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2" "M is ORDm"
  shows "ap_par P M Q is AP"
  unfolding ap_par_def
  by (rule H1_RAD_AP_closure, rule rad_par_RAD;
      simp add: assms RA1_AP_RAD_closure RA1_A2_closure)

lemma ap_par_RA1:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2" "M is ORDm"
  shows "RA1 (ap_par P M Q) = (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> RA1 Q)"
  unfolding ap_par_def
  by (rule RA1_H1_RAD_healthy[simplified comp_apply], rule rad_par_RAD;
      simp add: assms RA1_AP_RAD_closure RA1_A2_closure)

lemma ap_par_H1:
  assumes "P is RAD" "Q is RAD"
  shows "ap_par (H1 P) M (H1 Q) = H1 (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q)"
  by (simp only: ap_par_def
      RA1_H1_RAD_healthy[OF assms(1), simplified comp_apply]
      RA1_H1_RAD_healthy[OF assms(2), simplified comp_apply])

lemma ap_par_A2:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2"
  shows "ap_par P M Q is A2"
  unfolding ap_par_def
  by (rule H1_A2_closure, rule rad_par_A2;
      simp add: assms RA1_AP_RAD_closure RA1_A2_closure)

lemma ap_par_ac2p:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2" "M is ORDm"
  shows "ac2p (RA1 (ap_par P M Q)) =
    (ac2p (RA1 P) \<parallel>\<^bsub>M\<^esub> ac2p (RA1 Q))"
  unfolding ap_par_RA1[OF assms]
  by (rule rad_par_ac2p;
      simp add: assms RA1_AP_RAD_closure RA1_A2_closure)

lemma ap_par_p2ac:
  assumes "P is RD" "Q is RD"
  shows "ap_par (H1 (p2ac P)) M (H1 (p2ac Q)) =
    H1 (p2ac (P \<parallel>\<^bsub>M\<^esub> Q))"
  by (simp only: ap_par_H1[OF rad_p2ac_RD_closure[OF assms(1)]
        rad_p2ac_RD_closure[OF assms(2)]] rad_par_p2ac)

lemma ap_par_roundtrip:
  assumes "P is AP" "Q is AP" "P is A2" "Q is A2" "M is ORDm"
  shows "H1 (RA1 (ap_par P M Q)) = ap_par P M Q"
  by (subst ap_par_RA1[OF assms]; simp only: ap_par_def)

lemma ap_par_normalise_operands:
  "ap_par (H1 (RA1 (AP P))) M (H1 (RA1 (AP Q))) =
    ap_par (AP P) M (AP Q)"
  by (simp only: ap_par_def
    RA1_H1_RAD_healthy[OF RA1_AP_RAD_closure[OF AP_healthy], simplified comp_apply])

lemma ap_par_Chaos:
  "ap_par Chaos\<^sub>A\<^sub>P M Q = ap_par ChaosCSP\<^sub>A\<^sub>P M Q"
  by (simp only: ap_par_def Chaos_AP_same_RAD)


subsection \<open>Algebra\<close>

lemma ap_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "ap_par P1 M Q1 \<sqsubseteq> ap_par P2 M Q2"
  unfolding ap_par_def
  by (rule H1_monotone, rule rad_par_mono;
      rule RA1_mono; fact)

lemma ap_par_comm:
  assumes "rad_lift_merge M is SymMerge"
  shows "ap_par P M Q = ap_par Q M P"
  by (simp only: ap_par_def rad_par_comm[OF assms])

end
