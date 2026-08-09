section \<open>Non-Divergent Angelic Processes\<close>

theory utp_ap_nd
  imports utp_ap_ops
begin

(* Paper Definition 49 / Thesis Definition 130: the angelic choice with
   the most nondeterministic non-divergent process. *)
definition NDAP :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design" where
[pred]: "NDAP P = Choice\<^sub>A\<^sub>P \<squnion>\<^sub>A\<^sub>P P"

lemma NDAP_conj: "NDAP P = (Choice\<^sub>A\<^sub>P \<and> P)"
  by (simp add: NDAP_def AP_angelic_choice)

lemma NDAP_idem: "NDAP (NDAP P) = NDAP P"
  by (simp add: NDAP_def inf.left_idem)

lemma NDAP_Idempotent [closure]: "Idempotent NDAP"
  by (simp add: Idempotent_def NDAP_idem)

lemma NDAP_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> NDAP P \<sqsubseteq> NDAP Q"
  unfolding NDAP_def AP_angelic_choice
  by (intro pred_ba.inf_mono; simp)

lemma NDAP_Monotonic [closure]: "Monotonic NDAP"
  by (rule MonotonicI, rule NDAP_mono)

(* Thesis Theorem T.6.4.2: angelic processes are closed under NDAP. *)
lemma NDAP_AP_closure [closure]:
  assumes "P is AP"
  shows "NDAP P is AP"
  unfolding NDAP_def
  by (rule AP_angelic_closure[OF Choice_AP_is_AP assms])

lemma NDAP_Choice: "NDAP Choice\<^sub>A\<^sub>P = Choice\<^sub>A\<^sub>P"
  by (simp add: NDAP_def)

(* Conjoining a design with a true precondition weakens the other
   precondition away. *)
lemma design_true_conj:
  "((true \<turnstile> Q) \<and> ((\<not> F) \<turnstile> T)) =
   (true \<turnstile> (Q \<and> (F \<or> T)))"
  by pred_auto

(* The ok'-false projection of an angelic process is subsumed by its
   ok'-true one: both are vacuous when it has not started, and the
   failure guard G makes the difference vacuous otherwise. *)
lemma impl_absorb:
  "((ok\<^sup>< \<longrightarrow> G) \<or>
    ((ok\<^sup>< \<and> \<not> G) \<longrightarrow> H)) =
   ((ok\<^sup>< \<and> \<not> G) \<longrightarrow> H)"
  by pred_auto

(* Paper Theorem 38: the NDAP image has a true precondition and keeps
   the postcondition of P. *)
theorem NDAP_design_form:
  assumes "P is AP"
  shows "NDAP P =
    (true \<turnstile>
     (RA3AP \<circ> RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
proof -
  let ?A = "PBMH_ades ((P \<^sub>wf)\<^sup>f)"
  let ?B = "PBMH_ades ((P \<^sub>wf)\<^sup>t)"

  (* The two projections of P \<^sub>wf share the failure guard G, so the
     ok'-false one is absorbed by the ok'-true one. *)
  obtain G H
    where proj: "(P \<^sub>wf)\<^sup>f = (ok\<^sup>< \<longrightarrow> G)"
      "(P \<^sub>wf)\<^sup>t = ((ok\<^sup>< \<and> \<not> G) \<longrightarrow> H)"
    using AP_wait_false_ok_false[of P] AP_wait_false_ok_true[of P]
    by (simp only: Healthy_if[OF assms])
  have absorb: "(?A \<or> ?B) = ?B"
    by (simp only: PBMH_ades_disj[symmetric] proj impl_absorb)

  have "NDAP P = (Choice\<^sub>A\<^sub>P \<and> AP P)"
    by (simp only: NDAP_conj Healthy_if[OF assms])
  also have "... =
      RA3AP ((true \<turnstile> RA1 true) \<and>
             ((\<not> RA2 ?A) \<turnstile> RA2 (RA1 ?B)))"
    by (simp only: Choice_AP_RA3AP AP_RA3AP_design RA3AP_conj[symmetric])
  also have "... = RA3AP (true \<turnstile> RA2 (RA1 ?B))"
    by (simp only: design_true_conj RA2_RA1_disj_absorb[OF absorb])
  finally show ?thesis
    by (simp only: RA3AP_true_design comp_apply)
qed

(* Thesis Theorem T.6.2.10: Theorem 38 with the RA3AP conditional on the
   postcondition expanded. *)
lemma NDAP_wait_cond_form:
  assumes "P is AP"
  shows "NDAP P =
    (true \<turnstile>
     (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t)))))"
  by (simp only: NDAP_design_form[OF assms] comp_apply
      RA3AP_true_design[symmetric] RA3AP_design expr_if_idem)

subsection \<open>Isomorphism with Non-Divergent Reactive Angelic Designs\<close>

(* A non-divergent angelic process is a fixed point of the round trip
   through the theory of reactive angelic designs.  The NDAP normal
   form has precondition true, so H1_RA1_design applies directly and
   RA1 is reabsorbed by the postcondition; none of the precondition
   weakening behind the paper's Theorem 42 refinement arises. *)
lemma H1_RA1_NDAP:
  assumes "P is AP"
  shows "H1 (RA1 (NDAP P)) = NDAP P"
proof -
  let ?T = "RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t)))"
  have "H1 (RA1 (NDAP P)) =
      H1 (RA1 (true \<turnstile>
        (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> ?T)))"
    by (simp only: NDAP_wait_cond_form[OF assms])
  also have "... =
      (true \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> ?T))"
    by (simp only: H1_RA1_design RA1_wait_cond RA1_state_choice
        RA1_RA2_commute' RA1_idem)
  finally show ?thesis
    by (simp only: NDAP_wait_cond_form[OF assms])
qed

(* Paper Theorem 43 / Thesis Theorem T.6.3.5: on the non-divergent
   subsets, the theories of angelic processes and of reactive angelic
   designs are isomorphic. *)
theorem H1_RA1_NDAP_AP:
  "(H1 \<circ> RA1 \<circ> NDAP \<circ> AP) P = (NDAP \<circ> AP) P"
  by (simp only: comp_apply H1_RA1_NDAP[OF AP_healthy])

(* The other half of the correspondence: RA1 maps the non-divergent
   angelic processes onto the non-divergent reactive angelic designs.
   Both NDAP and NDRAD are conjunctions with the respective Choice, and
   RA1 distributes over conjunction. *)
lemma RA1_NDAP_NDRAD: "RA1 (NDAP (AP P)) = NDRAD (RAD P)"
proof -
  have "RA1 (NDAP (AP P)) = (Choice\<^sub>R\<^sub>A\<^sub>D \<and> RAD P)"
    by (simp only: NDAP_conj RA1_conj RA1_Choice_AP RA1_AP_RAD)
  also have "... = (RAD P \<and> Choice\<^sub>R\<^sub>A\<^sub>D)"
    by (simp only: conj_pred_def inf_commute)
  finally show ?thesis
    by (simp only: NDRAD_def RAD_angelic_choice)
qed

end
