section \<open>Angelic Process Examples\<close>

text \<open>
  The worked examples of the paper's Section 7, collected apart from
  the healthiness, correspondence, and operator theories.
\<close>

theory utp_ap_examples
  imports utp_ap_rad
begin

(* Paper Example 22: Theorem 39 applied to Chaos_RAD = RAD true. *)
lemma H1_Chaos_RAD_example:
  "H1 (Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) =
   ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
     (($rad_wait_lens\<^sup><)\<^sub>e \<and> ades_state_choice))"
  by (simp only: Chaos_RAD_RAD H1_RAD_design[simplified comp_apply]
      rad_wait_false_true subst_pred(1) PBMH_ades_true RA2_true
      RA2_RA1_true RA3AP_design_post;
      pred_auto add: rad_trace_extensions_def)

(* Paper Example 23. *)
lemma H1_Skip_RAD_example:
  "H1 (Skip\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design) =
   (true \<turnstile> RA3AP skip_post)"
  by (simp only: Skip_RAD_def comp_apply
      H1_RA_A_true_design[where P=skip_post,
        simplified rad_wait_false_skip_post skip_post_ok_out_subst comp_apply]
      skip_post_PBMH RA1_skip_post RA2_skip_post)

(* Paper Example 24 *)
lemma RA1_H1_Chaos_RAD_example:
  "RA1 ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
      (($rad_wait_lens\<^sup><)\<^sub>e \<and> ades_state_choice)) =
   (Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t::trace, 'e) reactive_angelic_design)"
  by (simp only: H1_Chaos_RAD_example[symmetric] Chaos_RAD_RAD
      RA1_H1_RAD[simplified comp_apply])

(* Paper Example 25: H1 after mapping the bottom AP through RA1. *)
lemma H1_RA1_bottom_AP_example:
  "(H1 \<circ> RA1) (\<^bold>\<bottom>\<^sub>A\<^sub>P ::
      ('t::trace, 'e) reactive_angelic_design) =
   ((($rad_wait_lens\<^sup><)\<^sub>e \<or> (\<not> RA1 true)) \<turnstile>
    (($rad_wait_lens\<^sup><)\<^sub>e \<and> ades_state_choice))"
  by (simp only: comp_apply RA1_AP_RAD[simplified comp_apply]
      bottom_RAD_is_Chaos H1_Chaos_RAD_example)

end
