section \<open>Reactive Angelic Designs\<close>

theory utp_rad_designs
  imports utp_rad_healthy
begin

subsection \<open>CSP healthiness counterparts (Paper Definitions 33 and 34)\<close>

definition CSPA1 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where
"CSPA1 P = (\<lambda> (x, y).
  P (x, y) \<or> RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x) (x, y))"

lemma CSPA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA1 P \<sqsubseteq> CSPA1 Q"
  by (simp add: CSPA1_def, pred_auto)

lemma CSPA1_Monotonic [closure]: "Monotonic CSPA1"
  by (rule MonotonicI, rule CSPA1_mono)

definition CSPA2 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where
"CSPA2 P = H2 P"

lemma CSPA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> CSPA2 P \<sqsubseteq> CSPA2 Q"
  using Continuous_Monotonic[OF H2_Continuous]
  by (simp add: CSPA2_def Monotonic_refine; blast)

lemma CSPA2_Monotonic [closure]: "Monotonic CSPA2"
  unfolding CSPA2_def
  by (rule Continuous_Monotonic[OF H2_Continuous])

subsection \<open>Reactive angelic designs (Paper Definition 35)\<close>

definition RAD ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where
"RAD = RA \<circ> CSPA1 \<circ> CSPA2 \<circ> PBMH_ades"

lemma RAD_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RAD P \<sqsubseteq> RAD Q"
  by (simp add: RAD_def RA_mono CSPA1_mono CSPA2_mono PBMH_ades_mono)

lemma RAD_Monotonic [closure]: "Monotonic RAD"
  unfolding RAD_def
  by (intro Monotonic_comp RA_Monotonic CSPA1_Monotonic
      CSPA2_Monotonic PBMH_ades_Monotonic)

end
