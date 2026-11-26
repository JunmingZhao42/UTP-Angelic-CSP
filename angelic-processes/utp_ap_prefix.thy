section \<open>Angelic Process Prefixing\<close>

theory utp_ap_prefix
  imports utp_ap_seq
begin

subsection \<open>Prefixing\<close>

(* TODO: Generalise prefixing to arbitrary trace algebras equipped with an
   event-to-trace embedding; the current list instance maps a to [a]. *)

(* Paper Definition 57 / Thesis Definition 138. *)
definition PrefixSkip_AP :: "'e \<Rightarrow> ('e list, 'e) angelic_process" where
[pred]: "PrefixSkip_AP a = AP (true \<turnstile> prefix_post a)"

lemma PrefixSkip_AP_is_AP [closure]: "PrefixSkip_AP a is AP"
  by (simp add: PrefixSkip_AP_def AP_healthy)

lemmas PrefixSkip_AP_facts =
  rad_wait_false_prefix_post prefix_post_PBMH prefix_post_ok_out_subst

lemma PrefixSkip_AP_design:
  "PrefixSkip_AP a =
   (true \<turnstile>
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 (prefix_post a)))"
  by (simp only: PrefixSkip_AP_def
      AP_true_design[OF PrefixSkip_AP_facts] RA2_prefix_post)

(* Paper Lemma 12 / Thesis Lemma L.6.4.4. *)
lemma H1_PrefixSkip_RAD:
  "H1 (PrefixSkip_RAD a) = PrefixSkip_AP a"
  by (simp only: PrefixSkip_RAD_RA PrefixSkip_AP_def
      H1_RA_true_design[OF PrefixSkip_AP_facts])

(* Paper Lemma 13 / Thesis Lemma L.6.4.5. *)
lemma RA1_PrefixSkip_AP:
  "RA1 (PrefixSkip_AP a) = PrefixSkip_RAD a"
  by (simp only: PrefixSkip_AP_def PrefixSkip_RAD_RA
      RA1_AP_true_design[OF PrefixSkip_AP_facts])

(* Thesis Section 6.4.8: the compound process a \<rightarrow>\<^sub>A\<^sub>P P
   abbreviates (a \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) ;;\<^sub>A\<^sub>D P; its
   general normal form is stated below. *)
definition Prefix_AP ::
  "'e \<Rightarrow> ('e list, 'e) angelic_process \<Rightarrow>
   ('e list, 'e) angelic_process"
  (infixr "\<rightarrow>\<^sub>A\<^sub>P" 80) where
[pred]: "Prefix_AP a P = (PrefixSkip_AP a ;;\<^sub>A\<^sub>D P)"

lemma Prefix_AP_closure [closure]:
  assumes "P is AP"
  shows "(a \<rightarrow>\<^sub>A\<^sub>P P) is AP"
  unfolding Prefix_AP_def
  by (rule AP_seq_closure[OF PrefixSkip_AP_is_AP assms])

(* Compound prefixing of Skip is the primitive prefix. *)
lemma Prefix_Skip_AP:
  "(a \<rightarrow>\<^sub>A\<^sub>P Skip\<^sub>A\<^sub>P) = PrefixSkip_AP a"
  unfolding Prefix_AP_def PrefixSkip_AP_def Skip_AP_def
  apply (subst AP_true_design_seq[OF PrefixSkip_AP_facts Skip_AP_facts])
  by (simp only: prefix_continuation_skip)

(* Thesis Theorem T.6.4.23. *)
lemma Prefix_AP_design:
  assumes "P is AP"
  shows "(a \<rightarrow>\<^sub>A\<^sub>P P) =
    AP ((\<not> prefix_handover a ((RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f))) \<turnstile>
      prefix_continuation a ((RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t)))"
proof -
  let ?D = "true \<turnstile> prefix_post a"
  let ?DF = "PBMH_ades ((?D \<^sub>f)\<^sup>f)"
  let ?DT = "(RA1 \<circ> PBMH_ades) ((?D \<^sub>f)\<^sup>t)"
  let ?F = "PBMH_ades ((P \<^sub>f)\<^sup>f)"
  let ?T = "RA1 (PBMH_ades ((P \<^sub>f)\<^sup>t))"
  let ?pre = "((\<not> (?DF ;;\<^sub>A\<^sub>R true)) \<and>
    (\<not> (?DT ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?F))))"
  let ?post = "?DT ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 ((\<not> ?F) \<longrightarrow> ?T))"
  let ?pre' = "\<not> (RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    ((\<not> rad_wait_lens\<^sup><) \<and> RA2 ?F))"
  let ?post' = "RA1 (prefix_post a) ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 ((\<not> ?F) \<longrightarrow> ?T))"
  note D_push = true_design_components_ok_in_subst[OF PrefixSkip_AP_facts]
  have design_eq: "(?pre \<turnstile> ?post) = (?pre' \<turnstile> ?post')"
    by (rule design_ok_in_cong)
      (simp_all only: subst_pred aseq_ades_ok_in_subst
        rad_wait_cond_ok_in_subst D_push
        aseq_ades_false_left pred_ba.compl_bot_eq pred_ba.inf_top_left)
  have "(a \<rightarrow>\<^sub>A\<^sub>P P) = (AP ?D ;;\<^sub>A\<^sub>D AP P)"
    by (simp only: Prefix_AP_def PrefixSkip_AP_def Healthy_if[OF assms])
  also have "... = AP (?pre \<turnstile> ?post)"
    by (simp only: AP_seq_design_PBMH comp_apply)
  also have "... = AP (?pre' \<turnstile> ?post')"
    by (simp only: design_eq)
  also have "... = AP
      ((\<not> prefix_handover a (RA2 ?F)) \<turnstile>
       prefix_continuation a (RA2 ?T))"
    by (simp only: impl_neg_disj pred_ba.double_compl RA2_disj
        prefix_handover_aseq prefix_continuation_aseq prefix_design_failure_absorb)
  finally show ?thesis
    by (simp only: comp_apply)
qed

end
