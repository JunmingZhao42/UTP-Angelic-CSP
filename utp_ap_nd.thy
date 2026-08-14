section \<open>Non-Divergent Angelic Processes\<close>

theory utp_ap_nd
  imports utp_ap_ops
begin

subsection \<open>NDAP\<close>

(* Paper Definition 49 / Thesis Definition 130. *)
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

lemma NDAP_AP_closure [closure]:
  assumes "P is AP"
  shows "NDAP P is AP"
  unfolding NDAP_def
  by (rule AP_angelic_closure[OF Choice_AP_is_AP assms])

lemma NDAP_Choice: "NDAP Choice\<^sub>A\<^sub>P = Choice\<^sub>A\<^sub>P"
  by (simp add: NDAP_def)

subsection \<open>Normal Form\<close>

lemma impl_absorb:
  "((ok\<^sup>< \<longrightarrow> G) \<or>
    ((ok\<^sup>< \<and> \<not> G) \<longrightarrow> H)) =
   ((ok\<^sup>< \<and> \<not> G) \<longrightarrow> H)"
  by pred_auto

(* Paper Theorem 38. *)
theorem NDAP_design_form:
  assumes "P is AP"
  shows "NDAP P = (true \<turnstile> (RA3AP \<circ> RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t))"
proof -
  let ?A = "PBMH_ades ((P \<^sub>f)\<^sup>f)" and ?B = "PBMH_ades ((P \<^sub>f)\<^sup>t)"

  (* The two projections of P \<^sub>f share the failure guard G, so the
     ok'-false one is absorbed by the ok'-true one. *)
  obtain G H
    where proj: "(P \<^sub>f)\<^sup>f = (ok\<^sup>< \<longrightarrow> G)"
      "(P \<^sub>f)\<^sup>t = ((ok\<^sup>< \<and> \<not> G) \<longrightarrow> H)"
    using AP_wait_false_ok_false[of P] AP_wait_false_ok_true[of P]
    by (simp only: Healthy_if[OF assms])
  have absorb: "(?A \<or> ?B) = ?B"
    by (simp only: PBMH_ades_disj[symmetric] proj impl_absorb)

  have "NDAP P = (Choice\<^sub>A\<^sub>P \<and> AP P)"
    by (simp only: NDAP_conj Healthy_if[OF assms])
  also have "... = RA3AP
      (true \<turnstile> (RA2 \<circ> RA1) ?B)"
    by (simp only: Choice_AP_RA3AP AP_RA3AP_design
        RA3AP_conj[symmetric] comp_apply design_true_conj
        RA2_RA1_disj_absorb[OF absorb])
  finally show ?thesis
    by (simp only: RA3AP_true_design comp_apply)
qed

lemma NDAP_is_H3:
  assumes "P is AP"
  shows "NDAP P is H3"
  by (simp only: NDAP_design_form[OF assms];
      rule design_condition_is_H3; unrest)

(* Thesis Theorem T.6.2.10: Theorem 38 with RA3AP expanded. *)
lemma NDAP_wait_cond_form:
  assumes "P is AP"
  shows "NDAP P =
    (true \<turnstile>
     (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)))"
  by (simp only: NDAP_design_form[OF assms] comp_apply
      RA3AP_true_design[symmetric] RA3AP_design expr_if_idem)

(* Theorem 38 as an AP image: the NDAP counterpart of
   H1_NDRAD_AP_true_design. *)
lemma NDAP_AP_true_design:
  assumes "P is AP"
  shows "NDAP P = AP (true \<turnstile> (P \<^sub>f)\<^sup>t)"
  by (simp only: NDAP_design_form[OF assms]
      AP_true_design[OF AP_wf_ok_true_facts[OF assms]]
      comp_apply AP_wf_ok_true_facts(2)[OF assms]
      RA3AP_design_post RA1_RA2_commute')

(* True-precondition angelic processes are non-divergent: the RA1-true
   postcondition of Choice_AP is absorbed. *)
lemma NDAP_AP_true_design_fixed:
  assumes "(X \<^sub>f) = X" "X is PBMH_ades"
    and "X\<lbrakk>True/ok\<^sup>>\<rbrakk> = X"
  shows "NDAP (AP (true \<turnstile> X)) = AP (true \<turnstile> X)"
proof -
  have ap_form: "AP (true \<turnstile> X) =
      RA3AP (true \<turnstile> RA1 (RA2 X))"
    by (simp only: AP_true_design[OF assms(1)
          Healthy_if[OF assms(2)] assms(3)]
        RA3AP_design_post[symmetric] RA3AP_true_design[symmetric])
  have "NDAP (AP (true \<turnstile> X)) =
      RA3AP ((true \<turnstile> RA1 true) \<and>
             (true \<turnstile> RA1 (RA2 X)))"
    by (simp only: NDAP_conj Choice_AP_RA3AP ap_form
        RA3AP_conj[symmetric])
  also have "... =
      RA3AP (true \<turnstile> (RA1 true \<and> RA1 (RA2 X)))"
    by (simp only: design_true_conj')
  also have "... = RA3AP (true \<turnstile> RA1 (RA2 X))"
    by (simp only: RA1_conj[symmetric] pred_ba.inf_top_left)
  also have "... = AP (true \<turnstile> X)"
    by (rule ap_form[symmetric])
  finally show ?thesis .
qed

subsection \<open>Closure under Choice\<close>

(* Paper Theorems 44 and 47 belong to the choice sections 7.3.1--7.3.2
   of the paper; they live here because they need NDAP. *)

(* Paper Theorem 44 / Thesis Theorem T.6.4.2.  By associativity only
   the first assumption is needed. *)
theorem NDAP_angelic_closure:
  assumes "P is NDAP" "Q is NDAP"
  shows "NDAP (P \<squnion>\<^sub>A\<^sub>P Q) = P \<squnion>\<^sub>A\<^sub>P Q"
  apply (rule_tac s="NDAP P \<squnion>\<^sub>A\<^sub>P Q" in trans)
  apply (simp only: NDAP_def inf_assoc)
  by (simp only: Healthy_if[OF assms(1)])

(* Paper Theorem 47 / Thesis Theorem T.6.4.6. *)
theorem NDAP_demonic_closure:
  assumes "P is NDAP" "Q is NDAP"
  shows "NDAP (P \<sqinter>\<^sub>A\<^sub>P Q) = P \<sqinter>\<^sub>A\<^sub>P Q"
proof -
  have "NDAP (P \<sqinter>\<^sub>A\<^sub>P Q) = (NDAP P \<sqinter>\<^sub>A\<^sub>P NDAP Q)"
    by (simp only: NDAP_def inf_sup_distrib1)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])
qed

subsection \<open>Closure under Sequential Composition\<close>

(* Paper Theorem 63 / Thesis Theorem T.6.4.22. *)
theorem NDAP_seq_closure:
  assumes "P is AP" "Q is AP" "P is NDAP" "Q is NDAP"
  shows "NDAP (P ;;\<^sub>D\<^sub>A Q) = (P ;;\<^sub>D\<^sub>A Q)"
proof -
  let ?Pt = "(P \<^sub>f)\<^sup>t" and ?Qt = "(Q \<^sub>f)\<^sup>t"
  let ?post = "(RA1 ?Pt ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ?Qt)))"
  note Pt_facts = AP_wf_ok_true_facts[OF assms(1)]
  note Qt_facts = AP_wf_ok_true_facts[OF assms(2)]
  have post_wf: "(?post \<^sub>f) = ?post"
    by (simp only: rad_wait_false_aseq_ades
        rad_wait_false_RA1_commute Pt_facts(1))
  have post_PBMH: "?post is PBMH_ades"
    by (intro aseq_ades_PBMH_ades_closure
        RA1_PBMH_ades_closure rad_wait_cond_PBMH_ades_closure
        ades_state_choice_is_PBMH_ades RA2_PBMH_ades_closure
        AP_wf_ok_true_PBMH_ades[OF assms(1)]
        AP_wf_ok_true_PBMH_ades[OF assms(2)])
  have post_unrest: "$ok\<^sup>> \<sharp> ?post"
    by (simp add: unrest)
  have post_ok: "?post\<lbrakk>True/ok\<^sup>>\<rbrakk> = ?post"
    using post_unrest by (simp add: unrest usubst)
  have P_form: "P = AP (true \<turnstile> ?Pt)"
    using NDAP_AP_true_design[OF assms(1)]
    by (simp only: Healthy_if[OF assms(3)])
  have Q_form: "Q = AP (true \<turnstile> ?Qt)"
    using NDAP_AP_true_design[OF assms(2)]
    by (simp only: Healthy_if[OF assms(4)])
  have seq_form: "(P ;;\<^sub>D\<^sub>A Q) = AP (true \<turnstile> ?post)"
    using AP_true_design_seq[OF Pt_facts Qt_facts]
    by (simp only: P_form[symmetric] Q_form[symmetric])
  show ?thesis
    by (simp only: seq_form
        NDAP_AP_true_design_fixed[OF post_wf post_PBMH post_ok])
qed

subsection \<open>Isomorphism with Non-Divergent Reactive Angelic Designs\<close>

(* Paper Theorem 43 / Thesis Theorem T.6.3.5.  With a true
   precondition the Theorem 42 weakening never arises. *)
theorem H1_RA1_NDAP_AP:
  "(H1 \<circ> RA1 \<circ> NDAP \<circ> AP) P = (NDAP \<circ> AP) P"
  by (simp only: comp_apply NDAP_wait_cond_form[OF AP_healthy]
      H1_RA1_design RA1_wait_cond RA1_state_choice RA1_RA2_commute'
      RA1_idem)

(* Not in the paper: RA1 maps the non-divergent AP image onto the
   non-divergent RAD image.  The commutativity step is kept separate:
   with the NDAP/NDRAD unfoldings in the same simp set, inf_commute
   does not terminate. *)
lemma RA1_NDAP_NDRAD:
  "(RA1 \<circ> NDAP \<circ> AP) P = (NDRAD \<circ> RAD) P"
proof -
  have "(RA1 \<circ> NDAP \<circ> AP) P = (Choice\<^sub>R\<^sub>A\<^sub>D \<and> RAD P)"
    by (simp only: comp_apply NDAP_conj RA1_conj RA1_Choice_AP
        RA1_AP_RAD[simplified comp_apply])
  also have "... = (RAD P \<and> Choice\<^sub>R\<^sub>A\<^sub>D)"
    by (simp only: conj_pred_def inf_commute)
  finally show ?thesis
    by (simp only: comp_apply NDRAD_def RAD_angelic_choice)
qed

end
