section \<open>Angelic Processes\<close>

theory utp_ap_healthy
  imports "UTP-Reactive-Angelic-Designs.utp_rad"
begin

subsection \<open>Healthiness Conditions\<close>

subsubsection \<open>The identity of angelic processes\<close>

(* Paper Definition 47: II_AP = H1 (ok' \<and> s \<in> ac'). *)
definition II_AP :: "('t::trace, 'e) reactive_angelic_design" where
[pred]: "II_AP = H1 (ok\<^sup>> \<and> ades_state_choice)"

lemma II_AP_is_H1 [closure]: "II_AP is H1"
  by (simp add: Healthy_def II_AP_def H1_idem)

subsubsection \<open>RA3AP: Waiting\<close>

(* Paper Definition 48: RA3AP (P) = II_AP \<triangleleft> s.wait \<triangleright> P. *)
definition RA3AP ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "RA3AP P = (II_AP \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)"

lemma RA3AP_idem: "RA3AP (RA3AP P) = RA3AP P"
  by (simp add: RA3AP_def)

lemma RA3AP_Idempotent [closure]: "Idempotent RA3AP"
  by (simp add: Idempotent_def RA3AP_idem)

lemma RA3AP_II_AP: "RA3AP II_AP = II_AP"
  by (simp add: RA3AP_def)

lemma II_AP_is_RA3AP [closure]: "II_AP is RA3AP"
  by (rule Healthy_intro, rule RA3AP_II_AP)

subsubsection \<open>AP\<close>

(* Paper Definition 46: AP = RA3AP \<circ> RA2 \<circ> A \<circ> H1 \<circ> CSPA2. *)
definition AP ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
[pred]: "AP = RA3AP \<circ> RA2 \<circ> A \<circ> H1 \<circ> CSPA2"

end
