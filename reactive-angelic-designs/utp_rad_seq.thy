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
proof -
  have handover:
    "P (x, m) \<Longrightarrow> Q (m, y) \<Longrightarrow>
     \<exists>n. P (x, rad2csp_obs n) \<and> Q (rad2csp_obs n, y)"
    for x m y
    by (intro exI[where x="csp2rad_obs m"]) simp
  show ?thesis
    by (auto simp add: csp2rad_rel_def seq_def fun_eq_iff
        intro: handover split: prod.splits)
qed

(* Thesis Theorem T.G.7.11, lifted to the reactive angelic mapping. *)
lemma rad_p2ac_seq:
  "rad_p2ac (P ;; Q) = (rad_p2ac P ;;\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q)"
  by (simp only: rad_p2ac_def comp_apply csp2rad_rel_seq_distrib
      p2ac_seq)

(* Thesis Theorem T.5.4.22. *)
lemma RAD_seq_CSP_refine:
  assumes "P is RAD" "Q is RAD"
  shows "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) \<sqsubseteq>
    rad_p2ac (rad_ac2p P ;; rad_ac2p Q)"
  unfolding rad_p2ac_seq
  by (rule angelic_design_seq_mono[OF RAD_is_PBMH_ades[OF assms(1)]];
      rule rad_p2ac_ac2p_refine'[OF RAD_is_PBMH_ades]) (fact assms)+

(* Thesis Theorem T.5.4.23. *)
lemma RAD_seq_CSP_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "rad_p2ac (rad_ac2p P ;; rad_ac2p Q) =
    (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
  by (simp only: rad_p2ac_seq rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

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
        design_ok_false)
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
    by (simp only: rad_wait_cond_not pred_ba.compl_top_eq RA2_not[symmetric])
  have Q_pre_failure_form: "(\<not> ?R') =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (\<not> R))"
    by (simp only: rad_wait_cond_not pred_ba.compl_top_eq RA2_not[symmetric])
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
  let ?failure = "RA1 (\<not> P) ;;\<^sub>A\<^sub>D RA1 true"
  let ?handover = "RA1 Q ;;\<^sub>A\<^sub>D
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (RA1 (\<not> R)))"
  let ?continuation = "RA1 Q ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 (R \<longrightarrow> S)))"
  have "(RA (P \<turnstile> Q) ;;\<^sub>D\<^sub>A RA (R \<turnstile> S)) =
    RA1 ((\<not> (RA1 (\<not> ?P') ;;\<^sub>A\<^sub>D RA1 true) \<and>
          \<not> (RA1 ?Q' ;;\<^sub>A\<^sub>D RA1 (\<not> ?R'))) \<turnstile>
         (RA1 ?Q' ;;\<^sub>A\<^sub>D RA1 (?R' \<longrightarrow> ?S')))"
    unfolding P_RA1_design_form Q_RA1_design_form
    by (rule RA1_design_seq[OF component_unrests P_pre_failure_PBMH
          P_post_wait_PBMH])
  also have "... = RA1 (RA3 (RA2
      (((\<not> ?failure) \<and> (\<not> ?handover)) \<turnstile> ?continuation)))"
    apply (simp only: RA2_design_distrib RA2_conj RA2_not RA1_RA3_design)
    apply (simp only: P_failure_comp_form handover_failure_comp_form
        continuation_comp_form P_failure_RA2_transport
        handover_failure_RA2_transport continuation_RA2_transport)
    by (simp only: rad_wait_cond_not pred_ba.compl_bot_eq
        rad_wait_cond_conj pred_ba.inf_idem)
  also have "... = RA (((\<not> ?failure) \<and> (\<not> ?handover))
      \<turnstile> ?continuation)"
    by (simp only: RA_as_RA1_RA3_RA2)
  finally show ?thesis
    by (simp only: rad_wait_cond_false)
qed

subsection \<open>Sequential composition of reactive angelic designs\<close>

text \<open>
  Notation in the statement below follows the mechanisation layers:
  \<open>;;\<^sub>A\<^sub>D\<close> is the full-design-alphabet lifting of the paper's
  angelic relation composition, \<open>ades_state_choice\<close> is the predicate
  \<open>s \<in> ac'\<close>, and \<open>$rad_wait_lens\<^sup><\<close> is the initial
  \<open>s.wait\<close> observation.  The expressions \<open>(P \<^sub>f)\<^sup>f\<close>
  and \<open>(P \<^sub>f)\<^sup>t\<close> are the wait-false predicate with final
  \<open>ok\<close> respectively fixed to false and true.
\<close>

(* Paper Theorem 30: Design form for the sequential composition of reactive angelic designs. *)
theorem RAD_seq_design:
  assumes "P is RAD" "Q is RAD"
  shows "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) =
    \<comment> \<open> \<not> (RA1 (P_f^f) ;; RA1(true)): P's precondition must hold \<close>
    (RA \<circ> A) (((\<not> (RA1 ((P \<^sub>f)\<^sup>f) ;;\<^sub>A\<^sub>D RA1 true)) \<and>
    \<comment> \<open> \<not> (RA1(P_f^t) ;; \<not>wait \<and> RA2 \<circ> RA1 (Q_f^f)): If P terminates and post condition hold then Q's precondition must hold\<close>
    (\<not> (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>D ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ((Q \<^sub>f)\<^sup>f)))))) \<turnstile>
    \<comment> \<open>If P waits then s\<in>ac', else RA2 \<circ> RA1 (Q_pre => Q_post)\<close>
    (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>D (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (RA1 ((\<not> (Q \<^sub>f)\<^sup>f) \<longrightarrow> (Q \<^sub>f)\<^sup>t)))))"
proof -
  let ?Af = "(P \<^sub>f)\<^sup>f" and ?At = "(P \<^sub>f)\<^sup>t"
  let ?Bf = "(Q \<^sub>f)\<^sup>f" and ?Bt = "(Q \<^sub>f)\<^sup>t"
  let ?Bf' = "(Q \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk>"
    and ?Bt' = "(Q \<^sub>f)\<^sup>t\<lbrakk>True/ok\<^sup><\<rbrakk>"
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

(* Thesis Theorem T.5.4.25. *)
lemma RAD_seq_A2_closure [closure]:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) is A2"
  by (rule angelic_design_seq_A2_closure[OF assms(3,4)])

lemma Prefix_RAD_closure [closure]:
  assumes "P is RAD"
  shows "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P) is RAD"
  unfolding Prefix_RAD_def
  by (rule RAD_seq_closure[OF PrefixSkip_RAD_is_RAD assms])

lemma Prefix_RAD_A2_closure [closure]:
  assumes "P is A2"
  shows "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P) is A2"
  unfolding Prefix_RAD_def
  by (rule angelic_design_seq_A2_closure[OF PrefixSkip_RAD_is_A2 assms])

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

(* General prefixing: the handover state follows the event, while the
   continuation also includes observations that still offer it. *)
lemma RA1_prefix_post:
  "RA1 (prefix_post a) = prefix_post a"
  by (simp add: RA1_def prefix_post_def ades_singleton_choice_def
      expr_if_def rad_state.wait_def rad_trace_extensions_def
      fun_eq_iff Let_def bex_nonempty_absorb;
      auto intro: trace_le_append)

(* The state reached after performing the prefix event. *)
definition prefix_handover ::
  "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
   ('e list, 'e) reactive_angelic_design" where
[pred]: "prefix_handover a P = (\<lambda> (s0, ac').
  \<exists> y. \<not> rad_state.wait\<^sub>v y \<and>
    rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<and>
    P (des_vars.more_update (astate.s\<^sub>v_update (\<lambda>_. y)) s0, ac'))"

(* The prefix is either still offering the event or has handed over. *)
definition prefix_continuation ::
  "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
   ('e list, 'e) reactive_angelic_design" where
[pred]: "prefix_continuation a P = (\<lambda> (s0, ac').
  \<exists> y. if rad_state.wait\<^sub>v y
    then y \<in> achoices.ac\<^sub>v (des_vars.more ac') \<and>
      rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
      a \<notin> rad_state.ref\<^sub>v y
    else rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<and>
      P (des_vars.more_update (astate.s\<^sub>v_update (\<lambda>_. y)) s0, ac'))"

lemma prefix_handover_aseq:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    ((\<not> rad_wait_lens\<^sup><) \<and> P)) = prefix_handover a P"
  by (simp only: RA1_prefix_post;
      simp add: aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def prefix_handover_def fun_eq_iff
      lens_defs rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def
      SEXP_def subst_app_def subst_ext_def conj_pred_def not_pred_def;
      auto simp add: if_bool_eq_disj split: prod.splits)

lemma prefix_continuation_aseq:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> P)) =
   prefix_continuation a P"
  by (simp only: RA1_prefix_post;
      simp add: aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def prefix_continuation_def
      ades_state_choice_def fun_eq_iff lens_defs rad_state.wait_def
      astate.s_def des_vars.more\<^sub>L_def
      SEXP_def subst_app_def subst_ext_def;
      auto simp add: if_bool_eq_disj split: prod.splits)

lemma prefix_design_failure_absorb:
  "((\<not> prefix_handover a F) \<turnstile> prefix_continuation a (F \<or> T)) =
   ((\<not> prefix_handover a F) \<turnstile> prefix_continuation a T)"
  by (simp add: prefix_handover_def prefix_continuation_def
      design_def fun_eq_iff conj_pred_def disj_pred_def not_pred_def impl_pred_def
      SEXP_def subst_app_def subst_ext_def lens_defs;
      auto simp add: if_bool_eq_disj split: prod.splits)

lemma Prefix_RA_design:
  assumes "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(PrefixSkip_RAD a ;;\<^sub>D\<^sub>A RA (R \<turnstile> S)) =
    RA ((\<not> prefix_handover a (RA2 (RA1 (\<not> R)))) \<turnstile>
      prefix_continuation a (RA2 (RA1 S)))"
proof -
  have components:
      "$ok\<^sup>> \<sharp> (true :: ('e list, 'e) reactive_angelic_design)"
      "$ok\<^sup>> \<sharp> prefix_post a"
      "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    by (simp_all add: unrest assms)
  have failure_PBMH:
      "(\<not> (true :: ('e list, 'e) reactive_angelic_design)) is PBMH_ades"
    by (simp only: pred_ba.compl_top_eq false_PBMH_ades)
  have prefix_PBMH: "prefix_post a is PBMH_ades"
    by (simp only: Healthy_def' prefix_post_PBMH)
  show ?thesis
    using RA_design_seq[where P=true and Q="prefix_post a" and R=R and S=S,
      OF components failure_PBMH prefix_PBMH]
    by (simp only: PrefixSkip_RAD_RA pred_ba.compl_top_eq RA1_false
        aseq_ades_false_left pred_ba.compl_bot_eq pred_ba.inf_top_left
        impl_neg_disj RA1_disj RA2_disj
        prefix_handover_aseq prefix_continuation_aseq prefix_design_failure_absorb)
qed

(* Thesis Theorem T.5.4.29. *)
lemma Prefix_RAD_design:
  assumes "P is RAD"
  shows "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P) =
    (RA \<circ> A)
      ((\<not> prefix_handover a ((RA2 \<circ> RA1) ((P \<^sub>f)\<^sup>f))) \<turnstile>
       prefix_continuation a ((RA2 \<circ> RA1) ((P \<^sub>f)\<^sup>t)))"
proof -
  let ?F = "(P \<^sub>f)\<^sup>f" and ?T = "(P \<^sub>f)\<^sup>t"
  let ?F' = "?F\<lbrakk>True/ok\<^sup><\<rbrakk>" and ?T' = "?T\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?D = "(\<not> prefix_handover a (RA2 (RA1 ?F))) \<turnstile>
    prefix_continuation a (RA2 (RA1 ?T))"
  let ?D' = "(\<not> prefix_handover a (RA2 (RA1 ?F'))) \<turnstile>
    prefix_continuation a (RA2 (RA1 ?T'))"
  have P_form: "P = RA ((\<not> ?F') \<turnstile> ?T')"
    using RAD_RA_design_form[OF assms]
    by (simp only: design_subst_ok[of "\<not> ?F" ?T, symmetric])
      (simp add: usubst)
  have components: "$ok\<^sup>< \<sharp> (\<not> ?F')" "$ok\<^sup>< \<sharp> ?T'"
    by (simp_all add: unrest)
  have desubst: "?D' = ?D"
    apply (rule design_ok_in_cong)
    by (simp_all add: usubst prefix_handover_aseq[symmetric]
        prefix_continuation_aseq[symmetric] RA1_ok_in_subst RA2_ok_in_subst
        aseq_ades_ok_in_subst rad_wait_cond_ok_in_subst)
  have failure_PBMH: "prefix_handover a (RA2 (RA1 ?F)) is PBMH_ades"
    unfolding prefix_handover_aseq[symmetric] rad_wait_cond_false[symmetric]
    by (intro aseq_ades_PBMH_ades_closure RA1_PBMH_ades_closure
        rad_wait_cond_PBMH_ades_closure false_PBMH_ades
        RA2_PBMH_ades_closure RAD_wf_ok_false_PBMH[OF assms];
        simp add: Healthy_def')
  have post_PBMH: "prefix_continuation a (RA2 (RA1 ?T)) is PBMH_ades"
    unfolding prefix_continuation_aseq[symmetric]
    by (intro aseq_ades_PBMH_ades_closure RA1_PBMH_ades_closure
        rad_wait_cond_PBMH_ades_closure ades_state_choice_is_PBMH_ades
        RA2_PBMH_ades_closure RAD_wf_ok_true_PBMH[OF assms];
        simp add: Healthy_def')
  have prefix_unrest: "$ok\<^sup>> \<sharp> RA1 (prefix_post a)"
    by unrest
  have continuation_unrest: "$ok\<^sup>> \<sharp>
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (RA1 ?T))"
    by unrest
  have unrests:
      "$ok\<^sup>> \<sharp> (\<not> prefix_handover a (RA2 (RA1 ?F)))"
      "$ok\<^sup>> \<sharp> prefix_continuation a (RA2 (RA1 ?T))"
    apply (simp only: prefix_handover_aseq[symmetric]; simp add: unrest)
    using aseq_ades_unrest_ok_out[OF prefix_unrest continuation_unrest]
    by (simp only: prefix_continuation_aseq)
  have absorb: "(RA \<circ> A) ?D = RA ?D"
    apply (rule RA_A_absorb_design)
       apply (simp only: pred_ba.double_compl failure_PBMH)
      apply (rule post_PBMH)
     apply (rule unrests(1))
    by (rule unrests(2))
  have "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D P) =
      (PrefixSkip_RAD a ;;\<^sub>D\<^sub>A RA ((\<not> ?F') \<turnstile> ?T'))"
    by (simp only: Prefix_RAD_def P_form[symmetric])
  also have "... = RA ?D'"
    by (simp only: Prefix_RA_design[OF components] pred_ba.double_compl)
  also have "... = (RA \<circ> A) ?D"
    by (simp only: desubst absorb)
  finally show ?thesis
    by (simp only: comp_apply)
qed

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


subsection \<open>Prefix observations and continuations\<close>

(* The failure observation of a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D
   Chaos\<^sub>R\<^sub>A\<^sub>D: the event has occurred. *)
definition prefix_diverge_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design"
where
[pred]: "prefix_diverge_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) @ [a] \<le>
    rad_state.tr\<^sub>v y)"

(* The event is offered and has not yet occurred. *)
definition prefix_offer_post :: "'e \<Rightarrow> ('e list, 'e) reactive_angelic_design"
where
[pred]: "prefix_offer_post a = (\<lambda> (s0, ac').
  \<exists> y \<in> achoices.ac\<^sub>v (des_vars.more ac').
    rad_state.wait\<^sub>v y \<and>
    rad_state.tr\<^sub>v y =
      rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more s0)) \<and>
    a \<notin> rad_state.ref\<^sub>v y)"

lemma prefix_diverge_post_p2ac:
  "prefix_diverge_post a = p2ac \<lceil>(\<lambda> (s, y).
    rad_state.tr\<^sub>v s @ [a] \<le> rad_state.tr\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: prefix_diverge_post_def p2ac_def fun_eq_iff
      subst_app_def subst_ext_def SEXP_def lens_defs
      des_vars.more\<^sub>L_def; pred_auto; blast)

lemma prefix_offer_post_p2ac:
  "prefix_offer_post a = p2ac \<lceil>(\<lambda> (s, y).
    rad_state.wait\<^sub>v y \<and> rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v s \<and>
    a \<notin> rad_state.ref\<^sub>v y)\<rceil>\<^sub>D"
  by (simp add: prefix_offer_post_def p2ac_def fun_eq_iff
      subst_app_def subst_ext_def SEXP_def lens_defs
      des_vars.more\<^sub>L_def; pred_auto; blast)

lemma prefix_diverge_post_PBMH [simp]:
  "PBMH_ades (prefix_diverge_post a) = prefix_diverge_post a"
  by (simp only: prefix_diverge_post_p2ac PBMH_ades_p2ac)

lemma prefix_offer_post_PBMH [simp]:
  "PBMH_ades (prefix_offer_post a) = prefix_offer_post a"
  by (simp only: prefix_offer_post_p2ac PBMH_ades_p2ac)

lemma prefix_diverge_post_unrest_ok [unrest]:
  "$ok\<^sup>> \<sharp> prefix_diverge_post a"
  apply (simp add: unrest_lens prefix_diverge_post_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma prefix_offer_post_unrest_ok [unrest]:
  "$ok\<^sup>> \<sharp> prefix_offer_post a"
  apply (simp add: unrest_lens prefix_offer_post_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

(* Handing the prefix over to an arbitrary continuation records
   exactly that the event has occurred. *)
lemma prefix_handover_diverge:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 true))) =
   prefix_diverge_post a"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def
      rad_state.wait_def
      prefix_diverge_post_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_state.wait_def astate.s_def
      des_vars.more\<^sub>L_def true_pred_def conj_pred_def
      not_pred_def SEXP_def subst_ext_def
      subst_app_def ex_in_conv[symmetric])
  apply clarify
  subgoal for x0 y0
    apply (rule iffI)
     apply (fastforce intro: order_trans)
    apply (elim bexE)
    subgoal for y
      apply (rule conjI)
       apply (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
           (rad_state.tr\<^sub>v_update
             (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
             y)" in bexI; fastforce)
      by (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
          (rad_state.tr\<^sub>v_update
            (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
            y)" in exI; fastforce)
    done
  done

(* The continuation of the prefix into Chaos: either the event is
   still offered, or it has occurred and anything may follow. *)
lemma prefix_continuation_chaos:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA2 (RA1 true))) =
   (prefix_offer_post a \<or> prefix_diverge_post a)"
  apply (simp only: RA1_RA2_commute'[symmetric] RA2_true)
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      ades_singleton_choice_def prefix_offer_post_def prefix_diverge_post_def
      ades_state_choice_def expr_if_def rad_trace_extensions_def
      fun_eq_iff Let_def lens_defs rad_state.wait_def astate.s_def
      des_vars.more\<^sub>L_def true_pred_def disj_pred_def
      conj_pred_def not_pred_def SEXP_def
      subst_ext_def subst_app_def ex_in_conv[symmetric])
  apply clarify
  subgoal for x0 y0
    apply (rule iffI)
     apply (fastforce intro: order_trans)
    apply (elim disjE bexE)
     subgoal for y
       apply (rule conjI)
        apply (rule_tac x=y in bexI; fastforce)
       by (rule_tac x=y in exI; fastforce)
    subgoal for y
      apply (rule conjI)
       apply (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
           (rad_state.tr\<^sub>v_update
             (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
             y)" in bexI; fastforce)
      by (rule_tac x="rad_state.wait\<^sub>v_update (\<lambda>_. False)
          (rad_state.tr\<^sub>v_update
            (\<lambda>_. rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more x0)) @ [a])
            y)" in exI; fastforce)
    done
  done

(* Trace normalisation fixes the failure observation of the prefixed
   Chaos: both sides state that the event has occurred. *)
lemma RA2_prefix_diverge_post:
  "RA2 (prefix_diverge_post a) = prefix_diverge_post a"
proof -
  have append_le:
    "xs \<le> ys \<Longrightarrow> zs \<le> ys - xs \<Longrightarrow>
     xs @ zs \<le> ys" for xs ys zs :: "'e list"
  proof -
    assume xy: "xs \<le> ys" and zd: "zs \<le> ys - xs"
    have "xs + zs \<le> xs + (ys - xs)"
      by (rule add_left_mono[OF zd])
    also have "... = ys"
      by (rule diff_add_cancel_left'[OF xy])
    finally show "xs @ zs \<le> ys"
      by (simp only: plus_list_def)
  qed
  have diff_le:
    "xs @ zs \<le> ys \<Longrightarrow> zs \<le> ys - xs"
    for xs ys zs :: "'e list"
  proof -
    assume xyz: "xs @ zs \<le> ys"
    have xy: "xs \<le> ys"
      by (rule list_append_prefixD[OF xyz])
    have "xs + zs \<le> xs + (ys - xs)"
      using xyz diff_add_cancel_left'[OF xy]
      by (simp only: plus_list_def)
    then show "zs \<le> ys - xs"
      by (rule add_le_imp_le_left)
  qed
  show ?thesis
    apply (simp add: RA2_def prefix_diverge_post_def
        rad_normalise_choices_def rad_trace_difference_def
        rad_zero_trace_def fun_eq_iff Let_def)
    apply pred_auto
    subgoal for ok tr ref wait more morea okv ac moreb refv waitv trv
      by (frule (1) append_le,
          rule_tac x="\<lparr>rad_state.tr\<^sub>v = trv, ref\<^sub>v = refv,
            wait\<^sub>v = waitv\<rparr>" in bexI; simp)
    subgoal for trv acv trv2 refv waitv
      by (frule list_append_prefixD, frule diff_le,
          rule_tac x="trv2 - trv" in exI, rule conjI,
          rule_tac x=refv in exI, rule_tac x=waitv in exI,
          rule_tac x=trv2 in exI; simp)
    done
qed

lemma RA2_prefix_offer_post:
  "RA2 (prefix_offer_post a) = prefix_offer_post a"
proof -
  \<comment> \<open>List instance of \<open>minus_zero_eq\<close>, shaped for the trace
      difference the normalisation exposes.\<close>
  have nil: "xs \<le> ys \<Longrightarrow> ys - xs = [] \<Longrightarrow> ys = xs"
      for xs ys :: "'e list"
    using minus_zero_eq by (auto simp add: zero_list_def)
  show ?thesis
  apply (simp add: RA2_def prefix_offer_post_def
      rad_normalise_choices_def rad_trace_difference_def
      rad_zero_trace_def fun_eq_iff Let_def)
  apply pred_auto
  subgoal for ok tr ref wait more morea okv ac moreb refv waitv trv
    by (drule sym, frule (1) nil,
        rule_tac x="\<lparr>rad_state.tr\<^sub>v = trv, ref\<^sub>v = refv,
          wait\<^sub>v = True\<rparr>" in bexI; simp)
  subgoal for tr ac ref wait
    by (rule_tac x=ref in exI, rule_tac x=True in exI, rule conjI,
        rule_tac x=tr in exI,
        simp_all add: diff_cancel zero_list_def)
  done
qed

(* Handing the prefix over to any non-waiting continuation is always
   possible: performing the event reaches a non-waiting state. *)
lemma prefix_handover_nonwait:
  "(RA1 (prefix_post a) ;;\<^sub>A\<^sub>D (\<not> rad_wait_lens\<^sup><)) = true"
  apply (simp add: RA1_def aseq_ades_def prefix_post_def
      ades_singleton_choice_def expr_if_def
      rad_state.wait_def rad_trace_extensions_def fun_eq_iff
      Let_def lens_defs rad_state.wait_def astate.s_def
      des_vars.more\<^sub>L_def true_pred_def conj_pred_def
      not_pred_def SEXP_def subst_ext_def
      subst_app_def ex_in_conv[symmetric])
  apply (rule allI, rule conjI)
  subgoal for aa
    by (rule_tac x="\<lparr>rad_state.tr\<^sub>v =
        rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more aa)) @ [a],
        ref\<^sub>v = {}, wait\<^sub>v = False\<rparr>" in bexI;
        simp add: trace_le_append)
  subgoal for aa
    by (rule_tac x="\<lparr>rad_state.tr\<^sub>v =
        rad_state.tr\<^sub>v (astate.s\<^sub>v (des_vars.more aa)) @ [a],
        ref\<^sub>v = {}, wait\<^sub>v = False\<rparr>" in exI;
        simp add: trace_le_append)
  done

end
