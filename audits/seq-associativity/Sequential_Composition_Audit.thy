theory Sequential_Composition_Audit
  imports "UTP-Angelic-CSP.Angelic_CSP"
begin

text \<open>
  Standalone audit of paper Definitions 18--19 (thesis Definitions 95--96).
  The production operators and healthiness conditions are imported unchanged.
  Evaluation records retain both outer ok observations explicitly.
\<close>

definition ades_eval :: "'s angelic_design \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> 's set \<Rightarrow> bool" where
"ades_eval P i state0 out_ok C = P
  (\<lparr>ok\<^sub>v = i, \<dots> = \<lparr>s\<^sub>v = state0, \<dots> = ()\<rparr>\<rparr>,
   \<lparr>ok\<^sub>v = out_ok, \<dots> = \<lparr>ac\<^sub>v = C, \<dots> = ()\<rparr>\<rparr>)"

lemma ades_eval_ext:
  assumes "\<And>i state0 out_ok C. ades_eval P i state0 out_ok C = ades_eval Q i state0 out_ok C"
  shows "P = Q"
  by (rule ext; case_tac x; rename_tac a b; case_tac a; case_tac b;
      rename_tac i am out_ok bm; case_tac am; case_tac bm; simp add: assms[unfolded ades_eval_def])

lemma ades_eval_seq:
  "ades_eval (P ;;\<^sub>D\<^sub>A Q) i state0 out_ok C =
    (\<exists>b. ades_eval P i state0 b {t. ades_eval Q b t out_ok C})"
  by (simp add: ades_eval_def angelic_design_seq_def)

lemma ades_eval_A2:
  "ades_eval (A2 P) i state0 out_ok C = (ades_eval P i state0 out_ok {} \<or> (\<exists>t\<in>C. ades_eval P i state0 out_ok {t}))"
  by (simp add: ades_eval_def A2_def)

lemma ades_eval_A2_union:
  assumes "P is A2"
  shows "ades_eval P i state0 out_ok (X \<union> Y) = (ades_eval P i state0 out_ok X \<or> ades_eval P i state0 out_ok Y)"
proof -
  have "\<And>C. ades_eval P i state0 out_ok C = (ades_eval P i state0 out_ok {} \<or> (\<exists>t\<in>C. ades_eval P i state0 out_ok {t}))"
    by (rule ades_eval_A2[of P i state0 out_ok, unfolded Healthy_if[OF assms]])
  from this[of "X \<union> Y"] this[of X] this[of Y] show ?thesis by blast
qed

lemma seq_assoc_first_A2:
  assumes "P is A2"
  shows "((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) = (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
proof (rule ades_eval_ext)
  fix i state0 out_ok C
  show "ades_eval ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) i state0 out_ok C =
    ades_eval (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R)) i state0 out_ok C"
    by (simp only: ades_eval_seq ex_bool_eq Collect_disj_eq ades_eval_A2_union[OF assms]; blast)
qed

text \<open>A two-state counterexample within the A-healthy carrier.\<close>

definition audit_both :: "bool angelic_design" where
"audit_both = (true \<turnstile>\<^sub>r
  (\<guillemotleft>False\<guillemotright> \<in> $ac\<^sup>> \<and> \<guillemotleft>True\<guillemotright> \<in> $ac\<^sup>>)\<^sub>e)"

definition audit_split :: "bool angelic_design" where
"audit_split = (($s\<^sup>< \<or> \<guillemotleft>False\<guillemotright> \<notin> $ac\<^sup>>)\<^sub>e \<turnstile>\<^sub>r
  ($s\<^sup>< \<and> \<guillemotleft>True\<guillemotright> \<in> $ac\<^sup>>)\<^sub>e)"

lemma ades_eval_both:
  "ades_eval audit_both i state0 out_ok C = (\<not> i \<or> (out_ok \<and> False \<in> C \<and> True \<in> C))"
  by (simp add: ades_eval_def audit_both_def; pred_auto)

lemma ades_eval_split:
  "ades_eval audit_split i state0 out_ok C = (\<not> i \<or> (\<not> state0 \<and> False \<in> C) \<or> (out_ok \<and> state0 \<and> True \<in> C))"
  by (simp add: ades_eval_def audit_split_def; pred_auto)

lemma ades_eval_skip:
  "ades_eval Skip_AD i state0 out_ok C = (\<not> i \<or> (out_ok \<and> state0 \<in> C))"
  by (simp add: ades_eval_def Skip_AD_def arel_to_ades_def; pred_auto)

lemma both_A: "audit_both is A"
  by (rule Healthy_intro; simp add: audit_both_def A_design_form; pred_auto; blast)

lemma split_A: "audit_split is A"
  by (rule Healthy_intro; simp add: audit_split_def A_design_form; pred_auto; blast)

lemma split_A2: "audit_split is A2"
  apply (rule Healthy_intro, rule ades_eval_ext)
  by (simp only: ades_eval_A2 ades_eval_split; blast)

lemma witness_left:
  "\<not> ades_eval ((audit_both ;;\<^sub>D\<^sub>A audit_split) ;;\<^sub>D\<^sub>A Skip_AD) True True True {True}"
  by (simp add: ades_eval_seq ades_eval_both ades_eval_split ades_eval_skip ex_bool_eq)

lemma witness_right:
  "ades_eval (audit_both ;;\<^sub>D\<^sub>A (audit_split ;;\<^sub>D\<^sub>A Skip_AD)) True True True {True}"
  by (simp add: ades_eval_seq ades_eval_both ades_eval_split ades_eval_skip ex_bool_eq)

lemma A_seq_not_associative:
  "\<exists>P Q R :: bool angelic_design.
     (P is A) \<and> (Q is A) \<and> (R is A) \<and>
     ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) \<noteq> (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
proof -
  have ne: "((audit_both ;;\<^sub>D\<^sub>A audit_split) ;;\<^sub>D\<^sub>A Skip_AD) \<noteq>
      (audit_both ;;\<^sub>D\<^sub>A (audit_split ;;\<^sub>D\<^sub>A Skip_AD))"
    using witness_left witness_right by auto
  show ?thesis
    by (intro exI[where x=audit_both] exI[where x=audit_split] exI[where x=Skip_AD];
        simp add: both_A split_A Skip_AD_is_A ne)
qed

lemma ades_eval_upward:
  assumes "P is PBMH_ades" "ades_eval P i state0 out_ok X" "X \<subseteq> Y"
  shows "ades_eval P i state0 out_ok Y"
  using PBMH_ades_upward[OF assms(1) assms(2)[unfolded ades_eval_def]]
    assms(3)
  unfolding ades_eval_def by simp

lemma seq_assoc_imp:
  assumes "P is PBMH_ades"
    "ades_eval ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) i state0 out_ok C"
  shows "ades_eval (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R)) i state0 out_ok C"
proof -
  obtain b c where old: "ades_eval P i state0 b
      {t. ades_eval Q b t c {u. ades_eval R c u out_ok C}}"
    using assms(2) by (auto simp only: ades_eval_seq)
  have subset: "{t. ades_eval Q b t c {u. ades_eval R c u out_ok C}} \<subseteq>
      {t. \<exists>c. ades_eval Q b t c {u. ades_eval R c u out_ok C}}"
    by blast
  show ?thesis
    unfolding ades_eval_seq using ades_eval_upward[OF assms(1) old subset] by blast
qed

lemma seq_assoc_refine:
  assumes "P is PBMH_ades"
  shows "(P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R)) \<sqsubseteq>
    ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R)"
  unfolding pred_refine_iff
  apply (intro allI impI)
  subgoal for w
    by (cases w; rename_tac a b; case_tac a; case_tac b;
        rename_tac i am out_ok bm; case_tac am; case_tac bm;
        simp add: seq_assoc_imp[OF assms, unfolded ades_eval_def])
  done

lemma normal_false_true:
  assumes "Q is \<^bold>N" "ades_eval Q i state0 False X"
  shows "ades_eval Q i state0 True Y"
proof -
  have dom: "ades_eval (p \<turnstile>\<^sub>n S) i state0 False X \<Longrightarrow>
      ades_eval (p \<turnstile>\<^sub>n S) i state0 True Y" for p S
    by (simp add: ades_eval_def; pred_auto)
  show ?thesis
    by (rule dom[where p="(pre\<^sub>D Q)\<^sub><" and S="post\<^sub>D Q",
          unfolded ndesign_form[OF assms(1)]], rule assms(2))
qed

lemma seq_assoc_middle_normal:
  assumes "P is PBMH_ades" "Q is \<^bold>N"
  shows "((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) = (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
proof (rule ades_eval_ext, rule iffI)
  fix i state0 out_ok C
  assume "ades_eval ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) i state0 out_ok C"
  then show "ades_eval (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R)) i state0 out_ok C"
    by (rule seq_assoc_imp[OF assms(1)])
next
  fix i state0 out_ok C
  assume right: "ades_eval (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R)) i state0 out_ok C"
  have collapse:
    "{t. \<exists>c. ades_eval Q b t c {u. ades_eval R c u out_ok C}} =
     {t. ades_eval Q b t True {u. ades_eval R True u out_ok C}}" for b
    using normal_false_true[OF assms(2)]
    by (auto simp: ex_bool_eq)
  show "ades_eval ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) i state0 out_ok C"
    using right unfolding ades_eval_seq collapse by blast
qed

text \<open>
  Reactive counterexamples use only existing Stop, prefixing and Chaos operators.
  The final choice contains an initial waiting observation refusing the event
  and a non-waiting observation after that event.
\<close>

lemma eval_Stop_AP:
  "ades_eval Stop_AP i x out_ok C =
    (\<not> i \<or> (out_ok \<and>
      (if rad_state.wait\<^sub>v x then x \<in> C
       else \<exists>y\<in>C. rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v x \<and> rad_state.wait\<^sub>v y)))"
  apply (simp only: Stop_AP_design ades_eval_def)
  apply (pred_auto add: rad_trace_extensions_def Let_def rad_state.wait_def disjoint_iff)
  apply fastforce
  done

lemma eval_PrefixSkip_AP:
  "ades_eval (PrefixSkip_AP a) i x out_ok C =
    (\<not> i \<or> (out_ok \<and>
      (if rad_state.wait\<^sub>v x then x \<in> C else
       \<exists>y\<in>C. if rad_state.wait\<^sub>v y
         then rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v x \<and> a \<notin> rad_state.ref\<^sub>v y
         else rad_state.tr\<^sub>v y = rad_state.tr\<^sub>v x @ [a])))"
  apply (simp only: PrefixSkip_AP_design ades_eval_def)
  apply (pred_auto add: rad_trace_extensions_def Let_def rad_state.wait_def disjoint_iff)
  subgoal for ref wait
    apply (rule exI[where x="rad_state.tr\<^sub>v x @ [a]"])
    apply simp
    apply (rule exI[where x=ref], rule exI[where x=False])
    by assumption
  subgoal for ref wait
    apply (rule exI[where x="rad_state.tr\<^sub>v x"])
    apply simp
    apply (rule exI[where x=ref], rule exI[where x=True])
    by assumption
  done

lemma eval_ChaosCSP_AP:
  "ades_eval ChaosCSP_AP i x out_ok C =
    (\<not> i \<or>
      (if rad_state.wait\<^sub>v x then out_ok \<and> x \<in> C
       else \<exists>y\<in>C. rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v y))"
  by (simp only: ChaosCSP_AP_design ades_eval_def;
      pred_auto add: rad_trace_extensions_def; blast)

lemma eval_RA1:
  "ades_eval (RA1 P) i x out_ok C =
    (ades_eval P i x out_ok (rad_trace_extensions x \<inter> C) \<and>
      rad_trace_extensions x \<inter> C \<noteq> {})"
  by (simp add: ades_eval_def RA1_def Let_def)

lemma eval_angelic:
  "ades_eval (P \<and> Q) i x out_ok C =
    (ades_eval P i x out_ok C \<and> ades_eval Q i x out_ok C)"
  by (simp add: ades_eval_def conj_pred_def)

type_synonym audit_state = "(unit list, unit) rad_state"

definition start :: audit_state where
"start = \<lparr>tr\<^sub>v = [], ref\<^sub>v = {}, wait\<^sub>v = False, \<dots> = ()\<rparr>"

definition waiting :: audit_state where
"waiting = \<lparr>tr\<^sub>v = [], ref\<^sub>v = {()}, wait\<^sub>v = True, \<dots> = ()\<rparr>"

definition finished :: audit_state where
"finished = \<lparr>tr\<^sub>v = [()], ref\<^sub>v = {}, wait\<^sub>v = False, \<dots> = ()\<rparr>"

definition stop_prefix_AP :: "(unit list, unit) reactive_angelic_design" where
"stop_prefix_AP = (Stop_AP \<and> PrefixSkip_AP ())"

lemma stop_prefix_AP_healthy: "stop_prefix_AP is AP"
  unfolding stop_prefix_AP_def
  by (rule AP_angelic_closure[OF Stop_AP_is_AP PrefixSkip_AP_is_AP,
        unfolded AP_angelic_choice])

lemma AP_witness_left:
  "\<not> ades_eval ((stop_prefix_AP ;;\<^sub>D\<^sub>A ChaosCSP_AP) ;;\<^sub>D\<^sub>A Stop_AP)
     True start True {waiting, finished}"
  unfolding stop_prefix_AP_def
  apply (simp only: ades_eval_seq eval_angelic eval_Stop_AP eval_PrefixSkip_AP eval_ChaosCSP_AP ex_bool_eq)
  apply (simp add: start_def waiting_def finished_def)
  apply auto
  done

lemma AP_witness_right:
  "ades_eval (stop_prefix_AP ;;\<^sub>D\<^sub>A (ChaosCSP_AP ;;\<^sub>D\<^sub>A Stop_AP))
     True start True {waiting, finished}"
proof -
  let ?C = "{waiting, finished}"
  let ?S = "{t. ades_eval (ChaosCSP_AP ;;\<^sub>D\<^sub>A Stop_AP) True t True ?C}"
  have wait: "waiting \<in> ?S"
    by (simp add: ades_eval_seq eval_ChaosCSP_AP eval_Stop_AP waiting_def finished_def ex_bool_eq)
  have finish: "finished \<in> ?S"
    apply (simp only: mem_Collect_eq ades_eval_seq)
    apply (rule exI[where x=False])
    apply (simp add: eval_ChaosCSP_AP eval_Stop_AP finished_def)
    by (rule exI[where x=finished]; simp add: finished_def)
  have fork: "ades_eval stop_prefix_AP True start True ?S"
    unfolding stop_prefix_AP_def
    apply (simp only: eval_angelic eval_Stop_AP eval_PrefixSkip_AP)
    apply (simp add: start_def)
    apply (intro conjI)
     apply (rule exI[where x=waiting]; simp add: waiting_def wait[unfolded mem_Collect_eq waiting_def])
    apply (rule exI[where x=finished]; simp add: finished_def finish[unfolded mem_Collect_eq finished_def])
    done
  show ?thesis using fork[unfolded ades_eval_seq] unfolding ades_eval_seq by blast
qed

lemma AP_seq_not_associative:
  "((stop_prefix_AP ;;\<^sub>D\<^sub>A ChaosCSP_AP) ;;\<^sub>D\<^sub>A Stop_AP) \<noteq>
    (stop_prefix_AP ;;\<^sub>D\<^sub>A (ChaosCSP_AP ;;\<^sub>D\<^sub>A Stop_AP))"
  using AP_witness_left AP_witness_right by auto

lemma eval_Stop_RAD:
  "ades_eval Stop_RAD i x out_ok C =
    (if i then ades_eval Stop_AP True x out_ok C
     else \<exists>y\<in>C. rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v y)"
  apply (simp only: RA1_Stop_AP[symmetric] eval_RA1 eval_Stop_AP)
  apply (auto simp: rad_trace_extensions_def disjoint_iff split: if_splits)
  subgoal for y by (rule exI[where x=y]; simp)
  done

lemma eval_PrefixSkip_RAD:
  "ades_eval (PrefixSkip_RAD a) i x out_ok C =
    (if i then ades_eval (PrefixSkip_AP a) True x out_ok C
     else \<exists>y\<in>C. rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v y)"
  apply (simp only: RA1_PrefixSkip_AP[symmetric] eval_RA1 eval_PrefixSkip_AP)
  apply (auto simp: rad_trace_extensions_def disjoint_iff split: if_splits)
  subgoal for y by (rule exI[where x=y]; simp)
  subgoal for y by (rule exI[where x=y]; simp)
  done

lemma eval_Chaos_RAD:
  "ades_eval Chaos_RAD i x out_ok C =
    (if i then ades_eval ChaosCSP_AP True x out_ok C
     else \<exists>y\<in>C. rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v y)"
  by (simp only: RA1_ChaosCSP_AP[symmetric] eval_RA1 eval_ChaosCSP_AP;
      auto simp: rad_trace_extensions_def disjoint_iff split: if_splits)

definition stop_prefix_RAD :: "(unit list, unit) reactive_angelic_design" where
"stop_prefix_RAD = (Stop_RAD \<and> PrefixSkip_RAD ())"

lemma stop_prefix_RAD_healthy: "stop_prefix_RAD is RAD"
  unfolding stop_prefix_RAD_def
  by (rule RAD_angelic_closure[OF Stop_RAD_is_RAD PrefixSkip_RAD_is_RAD,
        unfolded RAD_angelic_choice])

lemma RAD_witness_left:
  "\<not> ades_eval ((stop_prefix_RAD ;;\<^sub>D\<^sub>A Chaos_RAD) ;;\<^sub>D\<^sub>A Stop_RAD)
     True start True {waiting, finished}"
  unfolding stop_prefix_RAD_def
  apply (simp only: ades_eval_seq eval_angelic eval_Stop_RAD eval_PrefixSkip_RAD
      eval_Chaos_RAD eval_Stop_AP eval_PrefixSkip_AP eval_ChaosCSP_AP ex_bool_eq)
  apply (simp add: start_def waiting_def finished_def)
  apply auto
  done

lemma RAD_witness_right:
  "ades_eval (stop_prefix_RAD ;;\<^sub>D\<^sub>A (Chaos_RAD ;;\<^sub>D\<^sub>A Stop_RAD))
     True start True {waiting, finished}"
proof -
  let ?C = "{waiting, finished}"
  let ?S = "{t. ades_eval (Chaos_RAD ;;\<^sub>D\<^sub>A Stop_RAD) True t True ?C}"
  have wait: "waiting \<in> ?S"
    apply (simp only: mem_Collect_eq ades_eval_seq)
    apply (rule exI[where x=True])
    by (simp add: eval_Chaos_RAD eval_ChaosCSP_AP eval_Stop_RAD eval_Stop_AP waiting_def)
  have finish: "finished \<in> ?S"
    apply (simp only: mem_Collect_eq ades_eval_seq)
    apply (rule exI[where x=False])
    apply (simp add: eval_Chaos_RAD eval_ChaosCSP_AP eval_Stop_RAD finished_def)
    by (rule exI[where x=finished]; simp add: finished_def)
  have fork: "ades_eval stop_prefix_RAD True start True ?S"
    unfolding stop_prefix_RAD_def
    apply (simp only: eval_angelic eval_Stop_RAD eval_PrefixSkip_RAD eval_Stop_AP eval_PrefixSkip_AP)
    apply (simp add: start_def)
    apply (intro conjI)
     apply (rule exI[where x=waiting]; simp add: waiting_def wait[unfolded mem_Collect_eq waiting_def])
    apply (rule exI[where x=finished]; simp add: finished_def finish[unfolded mem_Collect_eq finished_def])
    done
  show ?thesis using fork[unfolded ades_eval_seq] unfolding ades_eval_seq by blast
qed

lemma RAD_seq_not_associative:
  "((stop_prefix_RAD ;;\<^sub>D\<^sub>A Chaos_RAD) ;;\<^sub>D\<^sub>A Stop_RAD) \<noteq>
    (stop_prefix_RAD ;;\<^sub>D\<^sub>A (Chaos_RAD ;;\<^sub>D\<^sub>A Stop_RAD))"
  using RAD_witness_left RAD_witness_right by auto

lemma eval_aseq_ades:
  "ades_eval (P ;;\<^sub>A\<^sub>D Q) i x out_ok C =
    ades_eval P i x out_ok {y. ades_eval Q i y out_ok C}"
  by (simp add: ades_eval_def aseq_ades_def)

text \<open>The auxiliary full-alphabet operator has no hidden intermediate ok.\<close>

lemma full_alphabet_aseq_assoc:
  "((P ;;\<^sub>A\<^sub>D Q) ;;\<^sub>A\<^sub>D R) = (P ;;\<^sub>A\<^sub>D (Q ;;\<^sub>A\<^sub>D R))"
  by (rule ades_eval_ext; simp only: eval_aseq_ades)

lemma AP_seq_assoc_middle_NDAP:
  assumes "P is AP" "Q is AP" "Q is NDAP"
  shows "((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) = (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
proof -
  have H1: "H1 Q = Q"
    by (rule Healthy_if[OF H_implies_H1[OF AP_is_H[OF assms(2)]]])
  have H3: "H3 Q = Q"
    using Healthy_if[OF NDAP_is_H3[OF assms(2)]]
    by (simp only: Healthy_if[OF assms(3)])
  have normal: "Q is \<^bold>N"
    by (simp only: Healthy_def' H3 H1)
  show ?thesis
    by (rule seq_assoc_middle_normal[OF AP_is_PBMH_ades[OF assms(1)] normal])
qed

text \<open>
  Non-divergent RAD associativity transfers from AP through the existing
  H1/RA1 isomorphism and the qualified sequential correspondence.
\<close>

lemma H1_NDRAD_is_NDAP:
  assumes "P is RAD" "P is NDRAD"
  shows "H1 P is NDAP"
  apply (simp only: H1_NDRAD_AP_true_design[OF assms] Healthy_def')
  apply (rule NDAP_AP_true_design_fixed)
    apply (rule RAD_wf_ok_true_facts(1)[OF assms(1)])
   apply (rule RAD_wf_ok_true_PBMH[OF assms(1)])
  by (rule RAD_wf_ok_true_facts(3)[OF assms(1)])

lemma H1_NDRAD_seq:
  assumes "P is RAD" "Q is RAD" "P is NDRAD" "Q is NDRAD"
  shows "H1 (P ;;\<^sub>D\<^sub>A Q) = (H1 P ;;\<^sub>D\<^sub>A H1 Q)"
proof -
  have ap: "(H1 P ;;\<^sub>D\<^sub>A H1 Q) is AP"
    by (rule AP_seq_closure; rule H1_RAD_AP_closure; rule assms)
  have nd: "NDAP (H1 P ;;\<^sub>D\<^sub>A H1 Q) = (H1 P ;;\<^sub>D\<^sub>A H1 Q)"
    by (rule NDAP_seq_closure[OF
          H1_RAD_AP_closure[OF assms(1)] H1_RAD_AP_closure[OF assms(2)]
          H1_NDRAD_is_NDAP[OF assms(1,3)] H1_NDRAD_is_NDAP[OF assms(2,4)]])
  have iso: "H1 (RA1 (H1 P ;;\<^sub>D\<^sub>A H1 Q)) = (H1 P ;;\<^sub>D\<^sub>A H1 Q)"
    using H1_RA1_NDAP_AP[of "H1 P ;;\<^sub>D\<^sub>A H1 Q"]
    by (simp only: comp_apply Healthy_if[OF ap] nd)
  show ?thesis
    by (simp only: RA1_H1_seq[OF assms, symmetric] iso)
qed

lemma NDRAD_seq_assoc:
  assumes "P is RAD" "Q is RAD" "R is RAD"
    "P is NDRAD" "Q is NDRAD" "R is NDRAD"
  shows "((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) = (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
proof -
  note pq = RAD_seq_closure[OF assms(1,2)]
  note qr = RAD_seq_closure[OF assms(2,3)]
  note pqnd = NDRAD_seq_closure[OF assms(1,2,4,5)]
  note qrnd = NDRAD_seq_closure[OF assms(2,3,5,6)]
  have ap_assoc:
    "((H1 P ;;\<^sub>D\<^sub>A H1 Q) ;;\<^sub>D\<^sub>A H1 R) =
      (H1 P ;;\<^sub>D\<^sub>A (H1 Q ;;\<^sub>D\<^sub>A H1 R))"
    by (rule AP_seq_assoc_middle_NDAP[OF
          H1_RAD_AP_closure[OF assms(1)] H1_RAD_AP_closure[OF assms(2)]
          H1_NDRAD_is_NDAP[OF assms(2,5)]])
  have mapped:
    "H1 ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) = H1 (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
    by (simp only: H1_NDRAD_seq[OF pq assms(3) pqnd assms(6)]
        H1_NDRAD_seq[OF assms(1) qr assms(4) qrnd]
        H1_NDRAD_seq[OF assms(1,2,4,5)] H1_NDRAD_seq[OF assms(2,3,5,6)]
        ap_assoc)
  show ?thesis
    using arg_cong[where f=RA1, OF mapped]
    by (simp only:
        RA1_H1_RAD_healthy[OF RAD_seq_closure[OF pq assms(3)], simplified comp_apply]
        RA1_H1_RAD_healthy[OF RAD_seq_closure[OF assms(1) qr], simplified comp_apply])
qed

lemma AP_carrier_not_associative:
  "\<exists>P Q R :: (unit list, unit) reactive_angelic_design.
    (P is AP) \<and> (Q is AP) \<and> (R is AP) \<and>
    ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) \<noteq> (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
  by (intro exI[where x=stop_prefix_AP] exI[where x=ChaosCSP_AP] exI[where x=Stop_AP];
      simp add: stop_prefix_AP_healthy ChaosCSP_AP_is_AP Stop_AP_is_AP AP_seq_not_associative)

lemma RAD_carrier_not_associative:
  "\<exists>P Q R :: (unit list, unit) reactive_angelic_design.
    (P is RAD) \<and> (Q is RAD) \<and> (R is RAD) \<and>
    ((P ;;\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R) \<noteq> (P ;;\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R))"
  by (intro exI[where x=stop_prefix_RAD] exI[where x=Chaos_RAD] exI[where x=Stop_RAD];
      simp add: stop_prefix_RAD_healthy Chaos_RAD_is_RAD Stop_RAD_is_RAD RAD_seq_not_associative)

end

