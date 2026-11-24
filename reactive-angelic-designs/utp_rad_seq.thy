section \<open>Reactive Angelic Design Sequential Composition\<close>

text \<open>
  Sequential composition laws, CSP correspondence, and the paper Theorem 30
  normal form (thesis T.5.4.21, via T.G.8.5 and T.G.8.6).
\<close>

theory utp_rad_seq
  imports utp_rad_prefix
begin

subsection \<open>Healthiness and angelic composition\<close>

(* Thesis Lemma L.G.1.29: an aborted first process followed by anything
   yields the aborted behaviour. *)
lemma RA1_not_ok_aseq_absorb:
  "(RA1 (\<not> ok\<^sup><) ;;\<^sub>A\<^sub>R RA1 true) = RA1 (\<not> ok\<^sup><)"
  apply (simp add: RA1_def aseq_ades_def fun_eq_iff Let_def)
  apply pred_auto
   apply (blast dest: rad_trace_extensions_trans)
  apply (blast intro: rad_trace_extensions_refl)
  done

(* Thesis Lemma L.G.1.16: composition preserves RA1 healthiness. *)
lemma RA1_aseq_absorb:
  "RA1 (RA1 P ;;\<^sub>A\<^sub>R RA1 Q) = (RA1 P ;;\<^sub>A\<^sub>R RA1 Q)"
  apply (simp add: RA1_def aseq_ades_def fun_eq_iff Let_def)
  apply (simp add: rad_trace_extensions_Int_Collect
      rad_trace_extensions_inter_absorb cong: conj_cong)
  apply (auto dest: rad_trace_extensions_trans)
  done

lemma rad_trace_append_assoc:
  "(\<lambda>x. t + (u + x)) = ((+) (t + u))" for t :: "'t::trace"
  by (auto simp add: fun_eq_iff add.assoc)

(* Thesis Theorem T.G.2.4: RA2 distributes through full-alphabet angelic
   composition when the right operand is already RA2-normalised. *)
lemma RA2_aseq_distrib:
  "RA2 (P ;;\<^sub>A\<^sub>R RA2 Q) = (RA2 P ;;\<^sub>A\<^sub>R RA2 Q)"
  by (simp add: RA2_def aseq_ades_def Let_def fun_eq_iff comp_def
      rad_normalise_choices_as_prepend[unfolded rad_trace_prepend_def] rad_zero_trace_def
      rad_trace_append_assoc)

(* A reusable form of the RA2 transport used by reactive sequential
   composition: commute RA1 and RA2 on both operands in one step. *)
lemma RA2_RA1_aseq_distrib:
  "RA2 (RA1 P ;;\<^sub>A\<^sub>R RA2 (RA1 Q)) =
   (RA1 (RA2 P) ;;\<^sub>A\<^sub>R RA1 (RA2 Q))"
proof -
  have "RA2 (RA1 P ;;\<^sub>A\<^sub>R RA2 (RA1 Q)) =
      (RA2 (RA1 P) ;;\<^sub>A\<^sub>R RA2 (RA1 Q))"
    by (rule RA2_aseq_distrib)
  also have "... =
      (RA1 (RA2 P) ;;\<^sub>A\<^sub>R RA1 (RA2 Q))"
    by (simp only: RA1_RA2_commute'[symmetric])
  finally show ?thesis .
qed

lemma RA2_aseq_fixed:
  assumes "RA2 Y = Y"
  shows "RA2 (X ;;\<^sub>A\<^sub>R Y) = (RA2 X ;;\<^sub>A\<^sub>R Y)"
proof -
  have "RA2 (X ;;\<^sub>A\<^sub>R Y) = RA2 (X ;;\<^sub>A\<^sub>R RA2 Y)"
    by (simp only: assms)
  also have "... = (RA2 X ;;\<^sub>A\<^sub>R RA2 Y)"
    by (rule RA2_aseq_distrib)
  also have "... = (RA2 X ;;\<^sub>A\<^sub>R Y)"
    by (simp only: assms)
  finally show ?thesis .
qed

subsection \<open>Basic laws and CSP correspondence\<close>

(* Thesis Theorem T.4.5.15. *)
lemma RAD_seq_demonic_distrib:
  "(P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) ;;\<^sub>R\<^sub>A\<^sub>D R = (P ;;\<^sub>R\<^sub>A\<^sub>D R) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (Q ;;\<^sub>R\<^sub>A\<^sub>D R)"
  by (rule angelic_design_seq_demonic)

lemma rad_p2ac_seq:
  "p2ac (P ;; Q) = (p2ac P ;;\<^sub>R\<^sub>A\<^sub>D p2ac Q)"
  by (simp only: comp_apply
      p2ac_seq)

(* Thesis Theorem T.5.4.22. *)
lemma RAD_seq_CSP_refine:
  assumes "P is RAD" "Q is RAD"
  shows "(P ;;\<^sub>R\<^sub>A\<^sub>D Q) \<sqsubseteq>
    p2ac (ac2p P ;; ac2p Q)"
  unfolding rad_p2ac_seq
  by (rule angelic_design_seq_mono[OF RAD_is_PBMH_ades[OF assms(1)]];
      rule rad_p2ac_ac2p_refine'[OF RAD_is_PBMH_ades]) (fact assms)+

(* Thesis Theorem T.5.4.23. *)
lemma RAD_seq_CSP_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "p2ac (ac2p P ;; ac2p Q) =
    (P ;;\<^sub>R\<^sub>A\<^sub>D Q)"
  by (simp only: rad_p2ac_seq rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

(* Thesis Theorem T.5.4.24: the correspondence of sequential composition with CSP. *)
lemma RAD_seq_CSP_inverse:
  "ac2p (p2ac P ;;\<^sub>R\<^sub>A\<^sub>D p2ac Q) = P ;; Q"
  by (simp only: rad_p2ac_seq[symmetric] rad_ac2p_p2ac_inverse')

subsection \<open>Sequential composition of RA1 designs\<close>

(* Thesis Theorem T.G.8.6: normal form for the composition of RA1
   designs. *)
lemma RA1_design_seq:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q" "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
    and "(\<not> P) is PBMH_ades" "Q is PBMH_ades"
  shows "(RA1 (P \<turnstile> Q) ;;\<^sub>A\<^sub>D RA1 (R \<turnstile> S)) =
    RA1 (((\<not> (RA1 (\<not> P) ;;\<^sub>A\<^sub>R RA1 true)) \<and>
          (\<not> (RA1 Q ;;\<^sub>A\<^sub>R RA1 (\<not> R)))) \<turnstile>
         (RA1 Q ;;\<^sub>A\<^sub>R RA1 (R \<longrightarrow> S)))"
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
      "RA1 (\<not> ok\<^sup><) \<sqsubseteq> (RA1 (\<not> ok\<^sup><) ;;\<^sub>A\<^sub>R ?B)"
    using aseq_ades_mono_right
      [where P="RA1 (\<not> ok\<^sup><)" and Q="RA1 true" and R="?B",
       OF _ B_refine]
    by (simp add: Healthy_def' RA1_not_ok_aseq_absorb)
  have absorb_not_P:
      "(RA1 (\<not> P) ;;\<^sub>A\<^sub>R RA1 true) \<sqsubseteq>
       (RA1 (\<not> P) ;;\<^sub>A\<^sub>R ?B)"
    by (rule aseq_ades_mono_right
        [OF RA1_PBMH_ades_closure[OF assms(5)] B_refine])
  have B_split: "(RA1 Q ;;\<^sub>A\<^sub>R ?B) =
    ((RA1 Q ;;\<^sub>A\<^sub>R RA1 (\<not> R)) \<or>
     ((RA1 Q ;;\<^sub>A\<^sub>R RA1 (R \<longrightarrow> S)) \<and> ok\<^sup>>))"
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
  "((P \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> Q) ;;\<^sub>A\<^sub>R R) =
   ((P ;;\<^sub>A\<^sub>R R) \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
    (Q ;;\<^sub>A\<^sub>R R))"
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
  shows "(RA (P \<turnstile> Q) ;;\<^sub>A\<^sub>D RA (R \<turnstile> S)) =
    RA (((\<not> (RA1 (\<not> P) ;;\<^sub>A\<^sub>R RA1 true)) \<and>
         (\<not> (RA1 Q ;;\<^sub>A\<^sub>R
             ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 (\<not> R)))))) \<turnstile>
        (RA1 Q ;;\<^sub>A\<^sub>R
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
  have P_failure_comp_form: "(RA1 (\<not> ?P') ;;\<^sub>A\<^sub>R RA1 true) =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (RA1 (RA2 (\<not> P)) ;;\<^sub>A\<^sub>R RA1 true))"
    by (simp only: P_failure_RA1_form aseq_ades_wait_cond_distrib
        aseq_ades_false_left)
  have handover_failure_comp_form: "(RA1 ?Q' ;;\<^sub>A\<^sub>R RA1 (\<not> ?R')) =
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (RA1 (RA2 Q) ;;\<^sub>A\<^sub>R
      (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA1 (RA2 (\<not> R)))))"
    by (simp only: P_post_RA1_form Q_failure_RA1_form
        aseq_ades_wait_cond_distrib
        aseq_ades_state_choice_left rad_wait_cond_left_absorb)
  have continuation_comp_form: "(RA1 ?Q' ;;\<^sub>A\<^sub>R RA1 (?R' \<longrightarrow> ?S')) =
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     (RA1 (RA2 Q) ;;\<^sub>A\<^sub>R
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA1 (RA2 (R \<longrightarrow> S)))))"
    by (simp only: P_post_RA1_form Q_body_RA1_form
        aseq_ades_wait_cond_distrib
        aseq_ades_state_choice_left rad_wait_cond_left_absorb)
  have P_failure_RA2_transport: "RA2 (RA1 (\<not> P) ;;\<^sub>A\<^sub>R RA1 true) =
    (RA1 (RA2 (\<not> P)) ;;\<^sub>A\<^sub>R RA1 true)"
    by (rule RA2_RA1_aseq_distrib
        [where P="\<not> P" and Q=true,
         simplified RA1_RA2_commute'[symmetric] RA2_true])
  have handover_failure_RA2_transport: "RA2 (RA1 Q ;;\<^sub>A\<^sub>R
      (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA2 (RA1 (\<not> R)))) =
    (RA1 (RA2 Q) ;;\<^sub>A\<^sub>R
     (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA1 (RA2 (\<not> R))))"
    by (rule RA2_RA1_aseq_distrib
        [where P=Q and
          Q="false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> (\<not> R)",
         simplified RA1_wait_cond RA1_false RA2_wait_cond RA2_false])
  have continuation_RA2_transport: "RA2 (RA1 Q ;;\<^sub>A\<^sub>R
      (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
       RA2 (RA1 (R \<longrightarrow> S)))) =
    (RA1 (RA2 Q) ;;\<^sub>A\<^sub>R
     (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
      RA1 (RA2 (R \<longrightarrow> S))))"
    by (rule RA2_RA1_aseq_distrib
        [where P=Q and
          Q="ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
             (R \<longrightarrow> S)",
         simplified RA1_wait_cond RA1_state_choice
           RA2_wait_cond RA2_state_choice])
  let ?failure = "RA1 (\<not> P) ;;\<^sub>A\<^sub>R RA1 true"
  let ?handover = "RA1 Q ;;\<^sub>A\<^sub>R
    (false \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (RA1 (\<not> R)))"
  let ?continuation = "RA1 Q ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 (R \<longrightarrow> S)))"
  have "(RA (P \<turnstile> Q) ;;\<^sub>A\<^sub>D RA (R \<turnstile> S)) =
    RA1 ((\<not> (RA1 (\<not> ?P') ;;\<^sub>A\<^sub>R RA1 true) \<and>
          \<not> (RA1 ?Q' ;;\<^sub>A\<^sub>R RA1 (\<not> ?R'))) \<turnstile>
         (RA1 ?Q' ;;\<^sub>A\<^sub>R RA1 (?R' \<longrightarrow> ?S')))"
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
  \<open>;;\<^sub>A\<^sub>R\<close> is the full-design-alphabet lifting of the paper's
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
    (RA \<circ> A) (((\<not> (RA1 ((P \<^sub>f)\<^sup>f) ;;\<^sub>A\<^sub>R RA1 true)) \<and>
    \<comment> \<open> \<not> (RA1(P_f^t) ;; \<not>wait \<and> RA2 \<circ> RA1 (Q_f^f)): If P terminates and post condition hold then Q's precondition must hold\<close>
    (\<not> (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>R ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ((Q \<^sub>f)\<^sup>f)))))) \<turnstile>
    \<comment> \<open>If P waits then s\<in>ac', else RA2 \<circ> RA1 (Q_pre => Q_post)\<close>
    (RA1 ((P \<^sub>f)\<^sup>t) ;;\<^sub>A\<^sub>R (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright> RA2 (RA1 ((\<not> (Q \<^sub>f)\<^sup>f) \<longrightarrow> (Q \<^sub>f)\<^sup>t)))))"
proof -
  let ?Af = "(P \<^sub>f)\<^sup>f" and ?At = "(P \<^sub>f)\<^sup>t"
  let ?Bf = "(Q \<^sub>f)\<^sup>f" and ?Bt = "(Q \<^sub>f)\<^sup>t"
  let ?Bf' = "(Q \<^sub>f)\<^sup>f\<lbrakk>True/ok\<^sup><\<rbrakk>"
    and ?Bt' = "(Q \<^sub>f)\<^sup>t\<lbrakk>True/ok\<^sup><\<rbrakk>"
  let ?preT = "((\<not> (RA1 ?Af ;;\<^sub>A\<^sub>R RA1 true)) \<and>
    (\<not> (RA1 ?At ;;\<^sub>A\<^sub>R
        ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Bf)))))"
  let ?postT = "(RA1 ?At ;;\<^sub>A\<^sub>R
    (ades_state_choice \<triangleleft> $rad_wait_lens\<^sup>< \<triangleright>
     RA2 (RA1 ((\<not> ?Bf) \<longrightarrow> ?Bt))))"
  let ?pre' = "((\<not> (RA1 ?Af ;;\<^sub>A\<^sub>R RA1 true)) \<and>
    (\<not> (RA1 ?At ;;\<^sub>A\<^sub>R
        ((\<not> rad_wait_lens\<^sup><) \<and> RA2 (RA1 ?Bf')))))"
  let ?post' = "(RA1 ?At ;;\<^sub>A\<^sub>R
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
  have seq_RA_normal_form: "(RA ((\<not> ?Af) \<turnstile> ?At) ;;\<^sub>A\<^sub>D
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
    (\<not> ((RA1 ?Af ;;\<^sub>A\<^sub>R RA1 true) \<or>
        (RA1 ?At ;;\<^sub>A\<^sub>R
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
    (RA ((\<not> ?Af) \<turnstile> ?At) ;;\<^sub>A\<^sub>D RA ((\<not> ?Bf') \<turnstile> ?Bt'))"
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

end
