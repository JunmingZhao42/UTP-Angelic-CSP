section \<open>Reactive Angelic Design Sequential Composition\<close>

text \<open>
  Sequential composition laws, CSP correspondence, and the paper Theorem 30
  normal form (thesis T.5.4.21, via T.G.8.5 and T.G.8.6).
\<close>

theory utp_rad_seq
  imports utp_rad_ops
begin

subsection \<open>Basic laws and CSP correspondence\<close>

(* Thesis Theorem T.4.5.15. *)
lemma RAD_seq_demonic_distrib:
  "(P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) ;;\<^sub>R\<^sub>A\<^sub>D R = (P ;;\<^sub>R\<^sub>A\<^sub>D R) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (Q ;;\<^sub>R\<^sub>A\<^sub>D R)"
  by (rule angelic_design_seq_demonic)

(* The observation repackaging distributes over sequential composition. *)
lemma csp2rad_rel_seq_distrib:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
  shows "csp2rad_rel (P ;; Q) = (csp2rad_rel P ;; csp2rad_rel Q)"
proof (rule ext)
  fix w :: "('t::trace, 'e) rad_state des_vars_scheme \<times>
    ('t, 'e) rad_state des_vars_scheme"
  obtain x y where [simp]: "w = (x, y)" by (cases w) auto
  have L: "csp2rad_rel (P ;; Q) w \<longleftrightarrow>
      (\<exists>m. P (rad2csp_obs x, m) \<and> Q (m, rad2csp_obs y))"
    by (simp add: csp2rad_rel_def; pred_auto)
  have R: "(csp2rad_rel P ;; csp2rad_rel Q) w \<longleftrightarrow>
      (\<exists>m. P (rad2csp_obs x, rad2csp_obs m) \<and>
        Q (rad2csp_obs m, rad2csp_obs y))"
    by (simp add: csp2rad_rel_def; pred_auto)
  show "csp2rad_rel (P ;; Q) w = (csp2rad_rel P ;; csp2rad_rel Q) w"
  proof (simp only: L R, rule iffI)
    assume "\<exists>m. P (rad2csp_obs x, m) \<and> Q (m, rad2csp_obs y)"
    then obtain m where "P (rad2csp_obs x, m)" and
        "Q (m, rad2csp_obs y)"
      by blast
    then show "\<exists>m. P (rad2csp_obs x, rad2csp_obs m) \<and>
        Q (rad2csp_obs m, rad2csp_obs y)"
      by (intro exI[where x="csp2rad_obs m"]) simp
  next
    assume "\<exists>m. P (rad2csp_obs x, rad2csp_obs m) \<and>
        Q (rad2csp_obs m, rad2csp_obs y)"
    then show "\<exists>m. P (rad2csp_obs x, m) \<and> Q (m, rad2csp_obs y)"
      by blast
  qed
qed

(* Thesis Theorem T.G.7.11, lifted to the reactive angelic mapping. *)
lemma rad_p2ac_seq:
  "rad_p2ac (P ;; Q) = (rad_p2ac P ;;\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q)"
  by (simp only: rad_p2ac_def comp_apply csp2rad_rel_seq_distrib
      p2ac_seq)

(* Thesis Theorem T.5.4.24: the correspondence of sequential composition with CSP. *)
lemma RAD_seq_CSP_inverse:
  "rad_ac2p (rad_p2ac P ;;\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q) = P ;; Q"
  by (simp only: rad_p2ac_seq[symmetric] rad_ac2p_p2ac_inverse')

subsection \<open>Sequential composition of RA1 designs\<close>

(* Thesis Theorem T.G.8.6: normal form for the composition of RA1
   designs. *)
lemma RA1_design_seq:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    and "(\<not> P) is PBMH_ades" "Q is PBMH_ades"
  shows "(RA1 (P \<turnstile> Q) ;;\<^sub>D\<^sub>A RA1 (R \<turnstile> S)) =
    RA1 (((\<not> (RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
          (\<not> (RA1 Q ;;\<^sub>A\<^sub>D RA1 (\<not> R)))) \<turnstile>
         (RA1 Q ;;\<^sub>A\<^sub>D RA1 (R \<longrightarrow> S)))"
proof -
  let ?B = "RA1 ((\<not> R) \<or> (S \<and> ok\<^sup>>))"
  have disj_collapse:
    "((X' \<or> Y' \<or> Z) \<or> (X \<or> Y)) = (X \<or> Y \<or> Z)"
    if "X \<sqsubseteq> X'" "Y \<sqsubseteq> Y'"
    for X X' Y Y' Z :: "('t::trace, 'e) reactive_angelic_design"
    using that
    by (simp add: pred_refine_iff fun_eq_iff; pred_auto)
  have B_refine: "RA1 true \<sqsubseteq> ?B"
    by (rule RA1_mono; pred_auto)
  have absorb_not_ok:
      "RA1 (\<not> ok\<^sup><) \<sqsubseteq> (RA1 (\<not> ok\<^sup><) ;;\<^sub>A\<^sub>D ?B)"
    using aseq_ades_mono_right
      [where P="RA1 (\<not> ok\<^sup><)" and Q="RA1 true" and R="?B",
       OF _ B_refine]
    by (simp add: Healthy_def' RA1_not_ok_aseq_absorb)
  have absorb_not_P:
      "(RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true) \<sqsubseteq>
       (RA1 (\<not> P) ;;\<^sub>A\<^sub>D ?B)"
    by (rule aseq_ades_mono_right
        [OF RA1_PBMH_ades_closure[OF assms(5)] B_refine])
  have B_split: "(RA1 Q ;;\<^sub>A\<^sub>D ?B) =
    ((RA1 Q ;;\<^sub>A\<^sub>D RA1 (\<not> R)) \<or>
     ((RA1 Q ;;\<^sub>A\<^sub>D RA1 (R \<longrightarrow> S)) \<and> ok\<^sup>>))"
    by (simp only: RA1_disj RA1_conj_ok
        aseq_ades_ok_out_split[OF RA1_PBMH_ades_closure[OF assms(6)]]
        RA1_disj[symmetric] impl_neg_disj[of R S, symmetric])
  show ?thesis
    apply (simp only: angelic_design_seq_ok_cases
        RA1_ok_out_subst RA1_ok_in_subst
        design_ok_out_true_subst[OF assms(1) assms(2)]
        design_ok_out_false_subst[OF assms(1)]
        design_ok_in_true_subst[OF assms(3) assms(4)]
        design_ok_in_false_subst)
    apply (simp only:
        RA1_disj[of "\<not> ok\<^sup><" "(\<not> P) \<or> Q"]
        RA1_disj[of "\<not> P" Q]
        RA1_disj[of "\<not> ok\<^sup><" "\<not> P"]
        aseq_ades_disj_distrib)
    apply (simp only: disj_collapse[OF absorb_not_ok absorb_not_P]
        RA1_not_ok_aseq_absorb)
    apply (simp only: B_split)
    apply (simp only: design_as_disj pred_ba.compl_inf
        pred_ba.double_compl RA1_disj RA1_conj_ok
        RA1_aseq_absorb pred_ba.sup.assoc)
    done
qed

subsection \<open>Wait-conditional composition\<close>

lemma rad_wait_cond_left_absorb:
  fixes A :: "'s pred"
  shows "expr_if (expr_if A b B) b C = expr_if A b C"
  by (simp add: expr_if_def fun_eq_iff)

lemma aseq_ades_wait_cond_distrib:
  "((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) ;;\<^sub>A\<^sub>D R) =
   ((P ;;\<^sub>A\<^sub>D R) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    (Q ;;\<^sub>A\<^sub>D R))"
  by (simp add: aseq_ades_def expr_if_def fun_eq_iff; pred_auto)

subsection \<open>Sequential composition of RA designs\<close>

text \<open>
  Thesis Theorem T.G.8.5 assumes PBMH healthiness for all four design
  components.  The proof below uses upward closure only for the first
  design's failure and postcondition predicates, \<open>\<not> P\<close> and
  \<open>Q\<close>; the mechanised statement therefore records these weaker
  sufficient assumptions.
\<close>

(* Thesis Theorem T.G.8.5: 
  normal form for the composition of RA designs. *)
lemma RA_design_seq:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
    "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    and "(\<not> P) is PBMH_ades" "Q is PBMH_ades"
  shows "(RA (P \<turnstile> Q) ;;\<^sub>D\<^sub>A RA (R \<turnstile> S)) =
    RA (((\<not> (RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
         (\<not> (RA1 Q ;;\<^sub>A\<^sub>D
             ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 (\<not> R)))))) \<turnstile>
        (RA1 Q ;;\<^sub>A\<^sub>D
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          RA2 (RA1 (R \<longrightarrow> S)))))"
proof -
  let ?P' = "true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 P"
  let ?Q' = "ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 Q"
  let ?R' = "true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 R"
  let ?S' = "ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 S"
  have not_true: "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) = false"
    by pred_auto
  have not_false: "(\<not> (false :: ('t::trace, 'e) reactive_angelic_design)) = true"
    by pred_auto
  have P_RA1_design_form: "RA (P \<turnstile> Q) = RA1 (?P' \<turnstile> ?Q')"
    by (simp only: RA_as_RA1_RA3_RA2 RA2_design_distrib
        RA1_RA3_design)
  have Q_RA1_design_form: "RA (R \<turnstile> S) = RA1 (?R' \<turnstile> ?S')"
    by (simp only: RA_as_RA1_RA3_RA2 RA2_design_distrib
        RA1_RA3_design)
  have component_unrests:
      "$ok\<^sup>> \<sharp> ?P'" "$ok\<^sup>> \<sharp> ?Q'"
      "$ok\<^sup>< \<sharp> ?R'" "$ok\<^sup>< \<sharp> ?S'"
    by (simp_all add: unrest assms)
  have P_pre_failure_form: "(\<not> ?P') =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (\<not> P))"
    by (simp only: rad_wait_cond_not not_true RA2_not[symmetric])
  have Q_pre_failure_form: "(\<not> ?R') =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (\<not> R))"
    by (simp only: rad_wait_cond_not not_true RA2_not[symmetric])
  have P_pre_failure_PBMH: "(\<not> ?P') is PBMH_ades"
    unfolding P_pre_failure_form
    by (rule rad_wait_cond_PBMH_ades_closure[OF false_PBMH_ades
        RA2_PBMH_ades_closure[OF assms(5)]])
  have P_post_wait_PBMH: "?Q' is PBMH_ades"
    by (rule rad_wait_cond_PBMH_ades_closure[OF ades_state_choice_is_PBMH_ades
        RA2_PBMH_ades_closure[OF assms(6)]])
  have rad_wait_cond_conj: "\<And>A B C D b.
    ((expr_if (A :: ('t::trace, 'e) reactive_angelic_design) b B) \<and>
     (expr_if C b D)) = expr_if (A \<and> C) b (B \<and> D)"
    by (simp add: expr_if_def fun_eq_iff; pred_auto)
  have pred_conj_true:
    "((true :: ('t::trace, 'e) reactive_angelic_design) \<and> true) = true"
    by pred_auto
  have P_failure_RA1_form: "RA1 (\<not> ?P') =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 (RA2 (\<not> P)))"
    by (simp only: P_pre_failure_form RA1_wait_cond RA1_false)
  have Q_failure_RA1_form: "RA1 (\<not> ?R') =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 (RA2 (\<not> R)))"
    by (simp only: Q_pre_failure_form RA1_wait_cond RA1_false)
  have P_post_RA1_form: "RA1 ?Q' =
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 (RA2 Q))"
    by (simp only: RA1_wait_cond RA1_state_choice)
  have Q_body_RA1_form: "RA1 (?R' \<longrightarrow> ?S') =
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA1 (RA2 (R \<longrightarrow> S)))"
    by (simp only: rad_wait_cond_impl pred_impl_laws(1)
        RA2_impl[symmetric] RA1_wait_cond RA1_state_choice)
  have P_failure_comp_form: "(RA1 (\<not> ?P') ;;\<^sub>A\<^sub>D RA1 true) =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (RA1 (RA2 (\<not> P)) ;;\<^sub>A\<^sub>D RA1 true))"
    by (simp only: P_failure_RA1_form aseq_ades_wait_cond_distrib
        aseq_ades_false_left)
  have handover_failure_comp_form: "(RA1 ?Q' ;;\<^sub>A\<^sub>D RA1 (\<not> ?R')) =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
      (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA1 (RA2 (\<not> R)))))"
    by (simp only: P_post_RA1_form Q_failure_RA1_form
        aseq_ades_wait_cond_distrib
        aseq_ades_state_choice_left rad_wait_cond_left_absorb)
  have continuation_comp_form: "(RA1 ?Q' ;;\<^sub>A\<^sub>D RA1 (?R' \<longrightarrow> ?S')) =
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA1 (RA2 (R \<longrightarrow> S)))))"
    by (simp only: P_post_RA1_form Q_body_RA1_form
        aseq_ades_wait_cond_distrib
        aseq_ades_state_choice_left rad_wait_cond_left_absorb)
  have P_failure_RA2_transport: "RA2 (RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true) =
    (RA1 (RA2 (\<not> P)) ;;\<^sub>A\<^sub>D RA1 true)"
    by (rule RA2_RA1_aseq_distrib
        [where P="\<not> P" and Q=true,
         simplified RA1_RA2_commute'[symmetric] RA2_true])
  have handover_failure_RA2_transport: "RA2 (RA1 Q ;;\<^sub>A\<^sub>D
      (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA2 (RA1 (\<not> R)))) =
    (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
     (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 (RA2 (\<not> R))))"
    by (rule RA2_RA1_aseq_distrib
        [where P=Q and
          Q="false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> R)",
         simplified RA1_wait_cond RA1_false RA2_wait_cond RA2_false])
  have continuation_RA2_transport: "RA2 (RA1 Q ;;\<^sub>A\<^sub>D
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA2 (RA1 (R \<longrightarrow> S)))) =
    (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
     (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA1 (RA2 (R \<longrightarrow> S))))"
    by (rule RA2_RA1_aseq_distrib
        [where P=Q and
          Q="ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
             (R \<longrightarrow> S)",
         simplified RA1_wait_cond RA1_state_choice
           RA2_wait_cond RA2_state_choice])
  have "(RA (P \<turnstile> Q) ;;\<^sub>D\<^sub>A RA (R \<turnstile> S)) =
    RA1 ((\<not> (RA1 (\<not> ?P') ;;\<^sub>A\<^sub>D RA1 true) \<and>
          \<not> (RA1 ?Q' ;;\<^sub>A\<^sub>D RA1 (\<not> ?R'))) \<turnstile>
         (RA1 ?Q' ;;\<^sub>A\<^sub>D RA1 (?R' \<longrightarrow> ?S')))"
    unfolding P_RA1_design_form Q_RA1_design_form
    by (rule RA1_design_seq[OF component_unrests P_pre_failure_PBMH
          P_post_wait_PBMH])
  also have "... =
    RA1 (((\<not> (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
              (RA1 (RA2 (\<not> P)) ;;\<^sub>A\<^sub>D RA1 true))) \<and>
          (\<not> (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
              (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
               (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                RA1 (RA2 (\<not> R))))))) \<turnstile>
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
           (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
            RA1 (RA2 (R \<longrightarrow> S))))))"
    by (simp only: P_failure_comp_form handover_failure_comp_form
        continuation_comp_form)
  also have "... =
    RA1 ((true \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          ((\<not> (RA1 (RA2 (\<not> P)) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
           (\<not> (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
               (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                RA1 (RA2 (\<not> R))))))) \<turnstile>
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
           (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
            RA1 (RA2 (R \<longrightarrow> S))))))"
    by (simp only: rad_wait_cond_not not_false
        rad_wait_cond_conj pred_conj_true)
  also have "... =
    RA1 (RA3 ((((\<not> (RA1 (RA2 (\<not> P)) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
           (\<not> (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
               (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                RA1 (RA2 (\<not> R))))))) \<turnstile>
         (RA1 (RA2 Q) ;;\<^sub>A\<^sub>D
           (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
            RA1 (RA2 (R \<longrightarrow> S))))))"
    by (simp only: RA1_RA3_design)
  also have "... =
    RA1 (RA3 (((\<not> RA2 (RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
               (\<not> RA2 (RA1 Q ;;\<^sub>A\<^sub>D
                  (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                   RA2 (RA1 (\<not> R)))))) \<turnstile>
              RA2 (RA1 Q ;;\<^sub>A\<^sub>D
                (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                 RA2 (RA1 (R \<longrightarrow> S))))))"
    by (simp only: P_failure_RA2_transport
        handover_failure_RA2_transport continuation_RA2_transport)
  also have "... =
    RA1 (RA3 (RA2 (((\<not> (RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
               (\<not> (RA1 Q ;;\<^sub>A\<^sub>D
                  (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                   RA2 (RA1 (\<not> R)))))) \<turnstile>
              (RA1 Q ;;\<^sub>A\<^sub>D
                (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
                 RA2 (RA1 (R \<longrightarrow> S)))))))"
    by (simp only: RA2_design_distrib RA2_conj RA2_not)
  also have "... =
    RA (((\<not> (RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
         (\<not> (RA1 Q ;;\<^sub>A\<^sub>D
             (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
              RA2 (RA1 (\<not> R)))))) \<turnstile>
        (RA1 Q ;;\<^sub>A\<^sub>D
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          RA2 (RA1 (R \<longrightarrow> S)))))"
    by (simp only: RA_as_RA1_RA3_RA2)
  also have "... =
    RA (((\<not> (RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
         (\<not> (RA1 Q ;;\<^sub>A\<^sub>D
             ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 (\<not> R)))))) \<turnstile>
        (RA1 Q ;;\<^sub>A\<^sub>D
         (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
          RA2 (RA1 (R \<longrightarrow> S)))))"
    by (simp only: rad_wait_cond_false)
  finally show ?thesis .
qed

subsection \<open>Sequential composition of reactive angelic designs\<close>

text \<open>
  Notation in the statement below follows the mechanisation layers:
  \<open>;;\<^sub>A\<^sub>D\<close> is the full-design-alphabet lifting of the paper's
  angelic relation composition, \<open>ades_state_choice\<close> is the predicate
  \<open>s \<in> ac'\<close>, and \<open>$rad_wait_lens\<^sup><\<close> is the initial
  \<open>s.wait\<close> observation.  The expressions \<open>(P \<^sub>wf)\<^sup>f\<close>
  and \<open>(P \<^sub>wf)\<^sup>t\<close> are the wait-false predicate with final
  \<open>ok\<close> respectively fixed to false and true.
\<close>

(* Paper Theorem 30: Design form for the sequential composition of reactive angelic designs. *)
theorem RAD_seq_design:
  assumes "P is RAD" "Q is RAD"
  shows "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) =
    \<comment> \<open> \<not> (RA1 (P_f^f) ;; RA1(true)): P's precondition must hold \<close>
    (RA \<circ> A) (((\<not> (RA1 ((P \<^sub>wf)\<^sup>f) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
    \<comment> \<open> \<not> (RA1(P_f^t) ;; \<not>wait \<and> RA2 \<circ> RA1 (Q_f^f)): If P terminates and post condition hold then Q's precondition must hold\<close>
    (\<not> (RA1 ((P \<^sub>wf)\<^sup>t) ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ((Q \<^sub>wf)\<^sup>f)))))) \<turnstile>
    \<comment> \<open>If P waits then s\<in>ac', else RA2 \<circ> RA1 (Q_pre => Q_post)\<close>
    (RA1 ((P \<^sub>wf)\<^sup>t) ;;\<^sub>A\<^sub>D (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (RA1 ((\<not> (Q \<^sub>wf)\<^sup>f) \<longrightarrow> (Q \<^sub>wf)\<^sup>t)))))"
proof -
  let ?Af = "(P \<^sub>wf)\<^sup>f" and ?At = "(P \<^sub>wf)\<^sup>t"
  let ?Bf = "(Q \<^sub>wf)\<^sup>f" and ?Bt = "(Q \<^sub>wf)\<^sup>t"
  let ?Bf' = "(Q \<^sub>wf)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?Bt' = "(Q \<^sub>wf)\<^sup>t\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?preT = "((\<not> (RA1 ?Af ;;\<^sub>A\<^sub>D RA1 true)) \<and>
    (\<not> (RA1 ?At ;;\<^sub>A\<^sub>D
        ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Bf)))))"
  let ?postT = "(RA1 ?At ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ((\<not> ?Bf) \<longrightarrow> ?Bt))))"
  let ?pre' = "((\<not> (RA1 ?Af ;;\<^sub>A\<^sub>D RA1 true)) \<and>
    (\<not> (RA1 ?At ;;\<^sub>A\<^sub>D
        ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Bf')))))"
  let ?post' = "(RA1 ?At ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ((\<not> ?Bf') \<longrightarrow> ?Bt'))))"
  have Q_ok_normalised:
    "RA ((\<not> ?Bf) \<turnstile> ?Bt) = RA ((\<not> ?Bf') \<turnstile> ?Bt')"
    by (simp only: design_subst_ok[of "\<not> ?Bf" ?Bt, symmetric])
      (simp add: usubst)
  have component_unrests:
    "$ok\<^sup>> \<sharp> (\<not> ?Af)" "$ok\<^sup>> \<sharp> ?At"
    "$ok\<^sup>< \<sharp> (\<not> ?Bf')" "$ok\<^sup>< \<sharp> ?Bt'"
    by (simp_all add: unrest)
  have P_failure_PBMH: "(\<not> (\<not> ?Af)) is PBMH_ades"
    by (simp only: pred_ba.double_compl
        RAD_wf_ok_false_PBMH[OF assms(1)])
  have seq_RA_normal_form: "(RA ((\<not> ?Af) \<turnstile> ?At) ;;\<^sub>D\<^sub>A
      RA ((\<not> ?Bf') \<turnstile> ?Bt')) =
    RA (?pre' \<turnstile> ?post')"
    by (simp only: RA_design_seq[OF component_unrests P_failure_PBMH
          RAD_wf_ok_true_PBMH[OF assms(1)]] pred_ba.double_compl)
  have push: "?preT\<lbrakk>True/ok\<^sup><\<rbrakk> = ?pre'\<lbrakk>True/ok\<^sup><\<rbrakk>"
    "?postT\<lbrakk>True/ok\<^sup><\<rbrakk> = ?post'\<lbrakk>True/ok\<^sup><\<rbrakk>"
    by (simp_all add: usubst RA1_ok_in_subst RA2_ok_in_subst
        aseq_ades_ok_in_subst rad_wait_cond_ok_in_subst)
  have design_ok_desubstitute:
    "(?pre' \<turnstile> ?post') = (?preT \<turnstile> ?postT)"
    using arg_cong2[where f=design, OF push]
    by (simp only: design_subst_ok)
  have seq_pre_as_neg_failure: "?preT =
    (\<not> ((RA1 ?Af ;;\<^sub>A\<^sub>D RA1 true) \<or>
        (RA1 ?At ;;\<^sub>A\<^sub>D
         ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Bf)))))"
    by pred_auto
  have seq_design_PBMH: "(?preT \<turnstile> ?postT) is PBMH_ades"
    unfolding seq_pre_as_neg_failure
    unfolding rad_wait_cond_false[symmetric] impl_neg_disj
      pred_ba.double_compl
    by (intro PBMH_ades_design_closure PBMH_ades_disj_closure
        aseq_ades_PBMH_ades_closure RA1_PBMH_ades_closure
        RA2_PBMH_ades_closure rad_wait_cond_PBMH_ades_closure
        false_PBMH_ades true_PBMH_ades ades_state_choice_is_PBMH_ades
        RAD_wf_ok_false_PBMH RAD_wf_ok_true_PBMH assms)
  have seq_design_H: "(?preT \<turnstile> ?postT) is \<^bold>H"
    by (rule design_is_H1_H2; simp add: unrest)
  have "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) =
    (RA ((\<not> ?Af) \<turnstile> ?At) ;;\<^sub>D\<^sub>A RA ((\<not> ?Bf') \<turnstile> ?Bt'))"
    by (simp only: RAD_RA_design_form[OF assms(1), symmetric]
        RAD_RA_design_form[OF assms(2), symmetric]
        Q_ok_normalised[symmetric])
  also have "... = (RA \<circ> A) (?preT \<turnstile> ?postT)"
    by (simp only: seq_RA_normal_form design_ok_desubstitute
        RA_A_absorb[OF seq_design_PBMH seq_design_H, symmetric])
  finally show ?thesis .
qed

lemma RAD_seq_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) is RAD"
  apply (simp only: RAD_seq_design[OF assms])
  apply (rule RAD_design_closure)
   apply (rule design_is_H1_H2; simp add: unrest)
  apply (simp add: rad_wait_false_distrib)
  done

lemma Prefix_RAD_closure [closure]:
  assumes "P is RAD"
  shows "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P) is RAD"
  unfolding Prefix_RAD_def
  by (rule RAD_seq_closure[OF PrefixSkip_RAD_is_RAD assms])

subsection \<open>Prefixing laws\<close>

(* An RA1-guarded left operand vanishes on the empty continuation. *)
lemma RA1_aseq_false: "(RA1 P ;;\<^sub>A\<^sub>D false) = false"
  by (simp add: RA1_def aseq_ades_def fun_eq_iff Let_def; pred_auto)

(* A nonempty choice set is subsumed by an inhabited choice over it. *)
lemma bex_nonempty_absorb:
  "((\<exists> y \<in> X. P y) \<and> \<not> X = {}) = (\<exists> y \<in> X. P y)"
  by auto

lemma trace_le_append [simp]: "(xs :: 'e list) \<le> xs @ ys"
  by (simp add: plus_list_def[symmetric])

(* The continuation of prefixing into Skip leaves the prefix
   postcondition unchanged: Skip is a right unit of the primitive. *)
lemma prefix_continuation_skip:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 skip_post))) = prefix_post a"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_skip_post)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def skip_post_def ades_singleton_choice_def
      ades_state_choice_def expr_if_def rad_trace_extensions_def
      fun_eq_iff Let_def lens_defs rad_state.wait_def astate.s_def
      des_vars.more\<^sub>L_def bex_nonempty_absorb)
  apply clarify
  subgoal for x0 y0
    apply (rule iffI)
     apply fastforce
    apply (elim bexE conjE)
    subgoal for y
      by (cases "rad_state.wait\<^sub>v y";
          rule_tac x=y in bexI; fastforce)
    done
  done

(* Thesis Theorem T.5.4.29 instantiated to Skip: the compound
   a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D coincides with the
   primitive of Definition 43. *)
lemma Prefix_Skip_RAD_RA:
  "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) = RA (true \<turnstile> prefix_post a)"
proof -
  have component_unrests:
      "$ok\<^sup>> \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> (true :: ('t::trace, 'e) reactive_angelic_design)"
      "$ok\<^sup>< \<sharp> skip_post"
    by (simp_all add: unrest)
  have not_true_PBMH:
      "(\<not> (true :: ('t::trace, 'e) reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have prefix_PBMH: "prefix_post a is PBMH_ades"
    by (simp add: Healthy_def')
  have skip_absorb:
      "(RA \<circ> A) (true \<turnstile> skip_post) = RA (true \<turnstile> skip_post)"
    by (rule RA_A_absorb_design_true; simp add: Healthy_def' unrest)
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D Skip\<^sub>R\<^sub>A\<^sub>D) =
      (RA (true \<turnstile> prefix_post a) ;;\<^sub>D\<^sub>A
       RA (true \<turnstile> skip_post))"
    by (simp only: Prefix_RAD_def PrefixSkip_RAD_RA Skip_RAD_def
        skip_absorb)
  also have "... = RA (true \<turnstile> prefix_post a)"
    using RA_design_seq[
      where P=true and Q="prefix_post a" and R=true and S=skip_post,
      OF component_unrests not_true_PBMH prefix_PBMH]
    by (simp only: pred_ba.compl_top_eq pred_ba.compl_bot_eq
        RA1_false RA2_false aseq_ades_false_left
        pred_ba.inf_bot_right RA1_aseq_false pred_ba.inf_idem
        pred_impl_laws prefix_continuation_skip)
  finally show ?thesis .
qed


end
