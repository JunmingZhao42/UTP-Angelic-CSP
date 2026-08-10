section \<open>Angelic Processes and Reactive Angelic Designs\<close>

theory utp_ap_rad
  imports utp_ap_healthy
begin

subsection \<open>From Reactive Angelic Designs to Angelic Processes\<close>

(* Paper Theorem 39 / Thesis Theorem T.6.3.1. *)
theorem H1_RAD_design:
  "(H1 \<circ> RAD) P =
   ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (\<not> (RA1 \<circ> RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f))) \<turnstile>
    (RA3AP \<circ> RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
proof -
  let ?F = "PBMH_ades ((P \<^sub>wf)\<^sup>f)"
  let ?T = "PBMH_ades ((P \<^sub>wf)\<^sup>t)"

  have "(H1 \<circ> RAD) P =
      (H1 \<circ> RA1 \<circ> RA3 \<circ> RA2) ((\<not> ?F) \<turnstile> (?T \<and> ac_non_empty))"
    by (simp only: comp_apply RAD_design_form A_design
        RA_as_RA1_RA3_RA2)
  also have "... =
      (H1 \<circ> RA1 \<circ> RA3) ((\<not> RA2 ?F) \<turnstile> (RA2 \<circ> RA1) ?T)"
    by (simp only: comp_apply RA2_design_distrib RA2_not
        RA2_ac_non_empty)
  also have "... =
      (H1 \<circ> RA1) ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> RA2 ?F)) \<turnstile>
               (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                (RA2 \<circ> RA1) ?T))"
    by (simp only: comp_apply RA1_RA3_design)
  also have "... =
      ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        (\<not> (RA1 \<circ> RA2) ?F)) \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        (RA2 \<circ> RA1) ?T))"
    by (simp only: comp_apply H1_RA1_design_gen rad_wait_cond_not
        pred_ba.compl_top_eq pred_ba.compl_bot_eq pred_ba.double_compl
        RA1_wait_cond RA1_false RA1_state_choice RA1_RA2_commute'
        RA1_idem)
  finally show ?thesis
    by (simp only: comp_apply RA3AP_design_post)
qed

subsection \<open>From Angelic Processes to Reactive Angelic Designs\<close>

(* Paper Theorem 40 / Thesis Theorem T.6.3.2. *)
theorem RA1_AP_design:
  "(RA1 \<circ> AP) P = (RA \<circ> A) ((\<not> (P \<^sub>wf)\<^sup>f) \<turnstile> (P \<^sub>wf)\<^sup>t)"
proof -
  let ?F = "PBMH_ades ((P \<^sub>wf)\<^sup>f)"
  let ?T = "PBMH_ades ((P \<^sub>wf)\<^sup>t)"

  have "(RA1 \<circ> AP) P =
      (RA1 \<circ> RA3) ((\<not> RA2 ?F) \<turnstile> (RA2 \<circ> RA1) ?T)"
    by (simp only: comp_apply AP_RA3AP_design
        RA1_RA3AP_RA3[simplified comp_apply])
  also have "... = RA ((\<not> ?F) \<turnstile> RA1 ?T)"
    by (simp only: comp_apply RA_as_RA1_RA3_RA2 RA2_design_distrib
        RA2_not)
  also have "... = RA ((\<not> ?F) \<turnstile> ?T)"
    by (simp only: RA_alt_def RA1_design_post[symmetric])
  finally show ?thesis
    by (simp only: comp_apply RA_A'[OF rad_wait_false_design_is_H]
        PBMH_ades_neg_design)
qed

(* Theorem 40 packaged with RAD_design_form. *)
lemma RA1_AP_RAD: "(RA1 \<circ> AP) P = RAD P"
  by (simp only: RA1_AP_design[simplified comp_apply]
      RAD_design_form comp_apply)

subsection \<open>Non-Divergent Processes\<close>

(* Paper Lemma 10 / Thesis Lemma L.6.3.1. *)
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
      (H1 \<circ> RA) (true \<turnstile> PBMH_ades ?T)"
    by (simp only: comp_apply RA_A'[OF H] push)
  also have "... =
      (true \<turnstile>
       (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
        (RA2 \<circ> RA1 \<circ> PBMH_ades) ?T))"
    by (simp only: comp_apply RA_true_design H1_RA1_design RA1_wait_cond
        RA1_state_choice RA1_RA2_commute')
  finally show ?thesis
    by (simp only: comp_apply RA3AP_design_post)
qed

(* Lemma 10 for an explicitly NDRAD-healthy process. *)
lemma H1_NDRAD:
  assumes "P is RAD"
  shows "(H1 \<circ> NDRAD) P =
    (true \<turnstile>
     (RA3AP \<circ> RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t))"
  by (simp only: comp_apply NDRAD_design_form[OF assms]
      H1_RA_A_true_design[simplified comp_apply])

subsection \<open>Isomorphism and Galois Connection\<close>

(* Paper Theorem 41 / Thesis Theorem T.6.3.3.  H1_RA1_design_gen puts
   an extra RA1 on each component; RA1_design_post/_pre run backwards
   reabsorb it. *)
theorem RA1_H1_RAD: "(RA1 \<circ> H1 \<circ> RAD) P = RAD P"
  by (simp only: comp_apply RAD_design_form A_design RA_as_RA1_RA3_RA2
      RA2_design_distrib RA1_RA3_design H1_RA1_design_gen
      RA1_design_post[symmetric] RA1_design_pre[symmetric])

(* Paper Theorem 42 / Thesis Theorem T.6.3.4.  The round trip weakens
   the precondition by an RA1; eq below is thesis Lemma L.H.2.4. *)
theorem H1_RA1_AP_refine: "AP P \<sqsubseteq> (H1 \<circ> RA1 \<circ> AP) P"
proof -
  let ?F = "(RA2 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>f)"
  let ?T = "(RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>wf)\<^sup>t)"
  have F_PBMH: "?F is PBMH_ades"
    by (simp only: comp_apply, rule RA2_PBMH_ades_closure,
        simp add: Healthy_def PBMH_ades_idem)
  have eq: "(H1 \<circ> RA1 \<circ> AP) P = RA3AP ((\<not> RA1 ?F) \<turnstile> ?T)"
    by (simp only: comp_apply RA1_AP_RAD[simplified comp_apply]
        H1_RAD_design[simplified comp_apply] RA3AP_design
        RA3AP_design_post)
  show ?thesis
    unfolding eq AP_RA3AP_design
    by (rule RA3AP_mono[OF design_pre_weaken[OF
        not_refine[OF RA1_refine[OF F_PBMH]]]])
qed

subsection \<open>Correspondence for True-Precondition Designs\<close>

(* Thesis Lemma L.H.2.2. *)
lemma H1_RA_true_design:
  assumes "(Post \<^sub>wf) = Post" "PBMH_ades Post = Post"
    and "Post\<lbrakk>True/ok\<^sup>>\<rbrakk> = Post"
  shows "H1 (RA (true \<turnstile> Post)) = AP (true \<turnstile> Post)"
  by (simp only: RA_true_design H1_RA1_design RA1_wait_cond
      RA1_state_choice AP_true_design[OF assms])

(* Thesis Theorem T.6.3.2 for true-precondition designs. *)
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
