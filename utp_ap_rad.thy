section \<open>Angelic Processes and Reactive Angelic Designs\<close>

theory utp_ap_rad
  imports utp_ap_healthy
begin

subsection \<open>From Reactive Angelic Designs to Angelic Processes\<close>

(* Paper Theorem 39 / Thesis Theorem T.6.3.1: H1 turns a reactive
   angelic design into an angelic process whose precondition, in
   addition, requires the failures to be RA1-healthy. *)
theorem H1_RAD_design:
  "H1 (RAD P) =
   ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (\<not> (RA1 \<circ> RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f))) \<turnstile>
    (RA3AP \<circ> RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
proof -
  let ?F = "PBMH_ades ((P \<^sub>wf)\<^sup>f)"
  let ?T = "PBMH_ades ((P \<^sub>wf)\<^sup>t)"

  have "H1 (RAD P) =
      H1 (RA1 (RA3 (RA2 ((\<not> ?F) \<turnstile> (?T \<and> ac_non_empty)))))"
    by (simp only: RAD_design_form comp_apply A_design RA_as_RA1_RA3_RA2)
  also have "... =
      H1 (RA1 (RA3 ((\<not> RA2 ?F) \<turnstile> RA2 (RA1 ?T))))"
    by (simp only: RA2_design_distrib RA2_not RA2_ac_non_empty)
  also have "... =
      H1 (RA1 ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA2 ?F)) \<turnstile>
               (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                RA2 (RA1 ?T))))"
    by (simp only: RA1_RA3_design)
  also have "... =
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        (\<not> RA1 (RA2 ?F))) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        RA2 (RA1 ?T)))"
    by (simp only: H1_RA1_design_gen rad_wait_cond_not
        pred_ba.compl_top_eq pred_ba.compl_bot_eq pred_ba.double_compl
        RA1_wait_cond RA1_false RA1_state_choice RA1_RA2_commute'
        RA1_idem)
  finally show ?thesis
    by (simp only: comp_apply RA3AP_design_post)
qed

subsection \<open>From Angelic Processes to Reactive Angelic Designs\<close>

(* Paper Theorem 40 / Thesis Theorem T.6.3.2: RA1 maps an angelic
   process back to the reactive angelic design image. *)
theorem RA1_AP_design:
  "(RA1 \<circ> AP) P = (RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  let ?F = "PBMH_ades ((P \<^sub>wf)\<^sup>f)"
  let ?T = "PBMH_ades ((P \<^sub>wf)\<^sup>t)"

  have "(RA1 \<circ> AP) P =
      RA1 (RA3 ((\<not> RA2 ?F) \<turnstile> RA2 (RA1 ?T)))"
    by (simp only: comp_apply AP_RA3AP_design RA1_RA3AP_RA3)
  also have "... = RA ((\<not> ?F) \<turnstile> RA1 ?T)"
    by (simp only: RA_as_RA1_RA3_RA2 RA2_design_distrib RA2_not)
  also have "... = RA ((\<not> ?F) \<turnstile> ?T)"
    by (simp only: RA_alt_def RA1_design_post[symmetric])
  finally show ?thesis
    by (simp only: comp_apply RA_A'[OF rad_wait_false_design_is_H]
        PBMH_ades_neg_design)
qed

(* RA1 maps the angelic process image onto the reactive angelic design
   image of the same predicate. *)
lemma RA1_AP_RAD: "RA1 (AP P) = RAD P"
  by (simp only: RA1_AP_design[simplified comp_apply]
      RAD_design_form comp_apply)

subsection \<open>Non-Divergent Processes\<close>

(* Paper Lemma 10 / Thesis Lemma L.6.3.1: mapping a non-divergent
   reactive angelic design through H1 keeps the precondition true. *)
lemma H1_RA_A_true_design:
  "(H1 \<circ> RA \<circ> A) (true \<turnstile> (P \<^sub>wf)\<^sup>t) =
   (true \<turnstile> (RA3AP \<circ> RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
proof -
  let ?T = "(P \<^sub>wf)\<^sup>t"
  have H: "(true \<turnstile> ?T) is \<^bold>H"
    by (rule design_is_H1_H2; unrest)
  have push: "PBMH_ades (true \<turnstile> ?T) = (true \<turnstile> PBMH_ades ?T)"
    by (simp add: design_as_disj PBMH_ades_disj PBMH_ades_conj_ok)
  have "(H1 \<circ> RA \<circ> A) (true \<turnstile> ?T) =
      H1 (RA (true \<turnstile> PBMH_ades ?T))"
    by (simp only: comp_apply RA_A'[OF H] push)
  also have "... =
      (true \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        RA2 (RA1 (PBMH_ades ?T))))"
    by (simp only: RA_true_design H1_RA1_design RA1_wait_cond
        RA1_state_choice RA1_RA2_commute')
  finally show ?thesis
    by (simp only: comp_apply RA3AP_design_post)
qed

(* The same for an explicitly NDRAD-healthy process. *)
lemma H1_NDRAD:
  assumes "P is RAD"
  shows "H1 (NDRAD P) =
    (true \<turnstile>
     (RA3AP \<circ> RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
  by (simp only: NDRAD_design_form[OF assms] comp_apply
      H1_RA_A_true_design[simplified comp_apply])

subsection \<open>Isomorphism and Galois Connection\<close>

(* Theorem 39 in RA3AP normal form: H1 maps a reactive angelic design
   to the angelic process whose precondition, in addition, requires the
   failures to be RA1-healthy.  Thesis Lemma L.H.2.4 states the same
   fact as AP applied to a design rather than as an RA3AP image. *)
lemma H1_RAD_RA3AP:
  "H1 (RAD P) =
   RA3AP ((\<not> RA1 (RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f)))) \<turnstile>
          RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t))))"
  by (simp only: H1_RAD_design comp_apply RA3AP_design RA3AP_design_post)

(* Paper Theorem 41 / Thesis Theorem T.6.3.3: mapping a reactive angelic
   design into the theory of angelic processes and back is the
   identity. *)
theorem RA1_H1_RAD: "(RA1 \<circ> H1 \<circ> RAD) P = RAD P"
  by (simp only: comp_apply RAD_design_form A_design RA1_H1_RA_design)

(* Paper Theorem 42 / Thesis Theorem T.6.3.4: in the opposite direction
   only a refinement is obtained.  The mapped process
   (H1 \<circ> RA1 \<circ> AP) P refines AP P -- the paper's
   H1 \<circ> RA1 \<circ> AP (P) \<sqsupseteq> AP (P) -- because the round trip weakens
   the precondition by an RA1. *)
theorem H1_RA1_AP_refine: "AP P \<sqsubseteq> (H1 \<circ> RA1 \<circ> AP) P"
proof -
  let ?F = "RA2 (PBMH_ades ((P \<^sub>wf)\<^sup>f))"
  let ?T = "RA2 (RA1 (PBMH_ades ((P \<^sub>wf)\<^sup>t)))"
  have F_PBMH: "?F is PBMH_ades"
    by (rule RA2_PBMH_ades_closure, simp add: Healthy_def PBMH_ades_idem)
  have pre: "(\<not> RA1 ?F) \<sqsubseteq> (\<not> ?F)"
    by (rule not_refine, rule RA1_refine[OF F_PBMH])
  have eq: "(H1 \<circ> RA1 \<circ> AP) P = RA3AP ((\<not> RA1 ?F) \<turnstile> ?T)"
    by (simp only: comp_apply RA1_AP_RAD H1_RAD_RA3AP)
  have ref: "RA3AP ((\<not> ?F) \<turnstile> ?T) \<sqsubseteq> RA3AP ((\<not> RA1 ?F) \<turnstile> ?T)"
    by (rule RA3AP_mono, rule design_pre_weaken[OF pre])
  show ?thesis
    by (simp only: eq AP_RA3AP_design; rule ref)
qed

subsection \<open>Correspondence for True-Precondition Designs\<close>

(* Thesis Lemma L.H.2.2, for designs with a true precondition: H1 maps a
   reactive angelic design to the corresponding angelic process. *)
lemma H1_RA_true_design:
  assumes "(Post \<^sub>wf) = Post" "PBMH_ades Post = Post"
    and "Post\<lbrakk>True/ok\<^sup>>\<rbrakk> = Post"
  shows "H1 (RA (true \<turnstile> Post)) = AP (true \<turnstile> Post)"
  by (simp only: RA_true_design H1_RA1_design RA1_wait_cond
      RA1_state_choice AP_true_design[OF assms])

(* Thesis Theorem T.6.3.2, for designs with a true precondition: RA1
   maps back. *)
lemma RA1_AP_true_design:
  assumes "(Post \<^sub>wf) = Post" "PBMH_ades Post = Post"
    and "Post\<lbrakk>True/ok\<^sup>>\<rbrakk> = Post"
  shows "RA1 (AP (true \<turnstile> Post)) = RA (true \<turnstile> Post)"
proof -
  have "RA1 (AP (true \<turnstile> Post)) =
      RA1 (true \<turnstile>
           RA1 (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                RA2 Post))"
    by (simp only: AP_true_design[OF assms] RA1_wait_cond
        RA1_state_choice)
  then show ?thesis
    by (simp only: RA1_design_post[symmetric] RA_true_design)
qed

end
