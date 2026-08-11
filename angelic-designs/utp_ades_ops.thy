section \<open>Angelic Design Operators\<close>

theory utp_ades_ops
  imports utp_ades_core
begin

subsection \<open>Assignment\<close>

(* Thesis Definition 94. The assigned state is one available angelic choice. *)
definition assign_arel :: 
  "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "assign_arel x e = (\<lambda> (s0, ac').
  put\<^bsub>x\<^esub> (astate.s\<^sub>v s0) (e (astate.s\<^sub>v s0))
    \<in> achoices.ac\<^sub>v ac')"

definition assigns_ades :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's angelic_design" where
[pred]: "assigns_ades x e = arel_to_ades (assign_arel x e)"

syntax
  "_assignment_ades" :: "svid \<Rightarrow> logic \<Rightarrow> logic"  (infixr ":=\<^sub>D\<^sub>A" 62)

translations
  "_assignment_ades x e" == "CONST assigns_ades x (e)\<^sub>e"
  "_assignment_ades (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_assignment_ades (x +\<^sub>L y) e"

subsection \<open>Demonic Choice\<close>

abbreviation dchoice_ades :: "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design" (infixl "\<sqinter>\<^sub>D\<^sub>A" 65)
where "P \<sqinter>\<^sub>D\<^sub>A Q \<equiv> P \<sqinter> Q"

lemma angelic_rel_demonic:
  fixes P Q :: "('s, '\<alpha>, '\<beta>) angelic_rel_ext"
  shows "P \<sqinter> Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

lemma angelic_design_demonic: "P \<sqinter>\<^sub>D\<^sub>A Q = (P \<or> Q)"
  by (simp add: disj_pred_def)

subsection \<open>Angelic Choice\<close>

abbreviation achoice_ades :: "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design" (infixl "\<squnion>\<^sub>D\<^sub>A" 70)
where "P \<squnion>\<^sub>D\<^sub>A Q \<equiv> P \<squnion> Q"

lemma angelic_rel_angelic:
  fixes P Q :: "('s, '\<alpha>, '\<beta>) angelic_rel_ext"
  shows "P \<squnion> Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

lemma angelic_design_angelic:
  "P \<squnion>\<^sub>D\<^sub>A Q = (P \<and> Q)"
  by (simp add: conj_pred_def)

(* Thesis Theorem T.4.5.18 *)
lemma angelic_design_angelic_top:
  fixes P :: "'s angelic_design"
  assumes "P is \<^bold>H"
  shows "P \<squnion>\<^sub>D\<^sub>A \<top>\<^sub>D = \<top>\<^sub>D"
proof -
  have H1H2_eq: "H1 (H2 P) = P"
    using assms by (simp only: Healthy_def')
  have P_le_top: "P \<sqsubseteq> \<top>\<^sub>D"
    using H1_below_top[of "H2 P"] H1H2_eq by simp
  show ?thesis
    using P_le_top
    by (simp only: ref_lattice.le_iff_sup)
qed

subsection \<open>Angelic Relation Sequential Composition\<close>

(* Paper Definition 19. *)
definition aseq ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext" (infixl ";;\<^sub>A" 75)
where
(* P(s0, ac'[ac := {s1 | Q(s0[s := s1], ac')}]) *)
[pred]: "P ;;\<^sub>A Q = (\<lambda> (s0, ac').
  P (s0, achoices.ac\<^sub>v_update
    (\<lambda>_. {s1. Q (astate.s\<^sub>v_update (\<lambda>_. s1) s0, ac')}) ac'))"

lemma aseq_true_left [simp]: "true ;;\<^sub>A P = true"
  by (pred_auto)

lemma aseq_false_left [simp]: "false ;;\<^sub>A P = false"
  by (pred_auto)

(* (s \<in> ac') ;; P = P *)
lemma aseq_state_choice_left [simp]:
  "(($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e ;;\<^sub>A P) = P"
  by (pred_auto)

lemma aseq_true_right_unrest [simp]:
  assumes "$ac\<^sup>> \<sharp> P"
  shows "P ;;\<^sub>A true = P"
  using assms by (pred_auto assms: assms)

lemma aseq_mono_left:
  "P \<sqsubseteq> Q \<Longrightarrow> (P ;;\<^sub>A R) \<sqsubseteq> (Q ;;\<^sub>A R)"
  by (auto simp add: aseq_def pred_refine_iff split: prod.splits)

(* Left distribution over disjunction; the right argument occurs inside the
   angelic-choice set, so the symmetric law does not hold in general. *)
lemma aseq_disj_distrib:
  "((P \<or> Q) ;;\<^sub>A R) = ((P ;;\<^sub>A R) \<or> (Q ;;\<^sub>A R))"
  by (simp add: aseq_def fun_eq_iff; pred_auto)

lemma aseq_assoc:
  "((P ;;\<^sub>A Q) ;;\<^sub>A R) = (P ;;\<^sub>A (Q ;;\<^sub>A R))"
  by (simp add: aseq_def fun_eq_iff)

subsection \<open>Full-alphabet Angelic Sequential Composition\<close>

text \<open>
  The operator below lifts angelic relation composition to the complete
  design alphabet.  It threads the state and angelic-choice components while
  leaving the two \<open>ok\<close> observations unchanged.
\<close>

definition aseq_ades ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  (infixl ";;\<^sub>A\<^sub>D" 75)
where [pred]: "P ;;\<^sub>A\<^sub>D Q = (\<lambda> (s0, ac').
  P (s0, des_vars.more_update
    (achoices.ac\<^sub>v_update (\<lambda>_.
      {s1. Q (des_vars.more_update
        (astate.s\<^sub>v_update (\<lambda>_. s1)) s0, ac')})) ac'))"

(* Embedding angelic relations as designs preserves sequential composition. *)
lemma arel_to_ades_aseq:
  "arel_to_ades (P ;;\<^sub>A Q) =
   (arel_to_ades P ;;\<^sub>A\<^sub>D arel_to_ades Q)"
  by (simp add: arel_to_ades_def rdesign_def design_def
      aseq_def aseq_ades_def fun_eq_iff; pred_auto)

lemma aseq_ades_true_left [simp]: "true ;;\<^sub>A\<^sub>D P = true"
  by pred_auto

lemma aseq_ades_false_left [simp]: "false ;;\<^sub>A\<^sub>D P = false"
  by pred_auto

lemma not_ok_aseq_ades_true:
  "((\<not> ok\<^sup><) ;;\<^sub>A\<^sub>D true) = (\<not> ok\<^sup><)"
  by (simp add: aseq_ades_def fun_eq_iff; pred_auto)

lemma aseq_ades_disj_distrib:
  "((P \<or> Q) ;;\<^sub>A\<^sub>D R) = ((P ;;\<^sub>A\<^sub>D R) \<or> (Q ;;\<^sub>A\<^sub>D R))"
  by pred_auto

lemma aseq_ades_mono_left:
  "P \<sqsubseteq> Q \<Longrightarrow> (P ;;\<^sub>A\<^sub>D R) \<sqsubseteq> (Q ;;\<^sub>A\<^sub>D R)"
  by (auto simp add: aseq_ades_def pred_refine_iff split: prod.splits)

(* s \<in> ac' *)
definition ades_state_choice :: "'s angelic_design" where
[pred]: "ades_state_choice = (\<lambda> (s0, ac').
  astate.s\<^sub>v (des_vars.more s0) \<in> achoices.ac\<^sub>v (des_vars.more ac'))"

abbreviation ades_s_lens where
"ades_s_lens \<equiv> astate.s ;\<^sub>L des_vars.more\<^sub>L"

abbreviation ades_ac_lens where
"ades_ac_lens \<equiv> achoices.ac ;\<^sub>L des_vars.more\<^sub>L"

lemma ades_state_choice_expr:
  "ades_state_choice = ($ades_s_lens\<^sup>< \<in> $ades_ac_lens\<^sup>>)\<^sub>e"
  by pred_auto

lemma aseq_ades_state_choice_left [simp]:
  "(ades_state_choice ;;\<^sub>A\<^sub>D P) = P"
  by pred_auto

(* The two fields of the design observation can be updated independently. *)
lemma des_more_ok_update_commute:
  "des_vars.more_update f (ok\<^sub>v_update g r) =
   ok\<^sub>v_update g (des_vars.more_update f r)"
  by (cases r) simp

lemma aseq_ades_unrest_ok_out [unrest]:
  "\<lbrakk> $ok\<^sup>> \<sharp> P; $ok\<^sup>> \<sharp> Q \<rbrakk> \<Longrightarrow>
   $ok\<^sup>> \<sharp> (P ;;\<^sub>A\<^sub>D Q)"
  apply (simp add: unrest_lens aseq_ades_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs des_more_ok_update_commute)
  done

lemma aseq_ades_unrest_ok_in [unrest]:
  "\<lbrakk> $ok\<^sup>< \<sharp> P; $ok\<^sup>< \<sharp> Q \<rbrakk> \<Longrightarrow>
   $ok\<^sup>< \<sharp> (P ;;\<^sub>A\<^sub>D Q)"
  apply (simp add: unrest_lens aseq_ades_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  apply (simp add: des_more_ok_update_commute)
  done

lemma ades_state_choice_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> (ades_state_choice :: 's angelic_design)"
  apply (simp add: unrest_lens ades_state_choice_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma ades_state_choice_unrest_ok_in [unrest]:
  "$ok\<^sup>< \<sharp> (ades_state_choice :: 's angelic_design)"
  apply (simp add: unrest_lens ades_state_choice_def)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma pred_true_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> (true :: 's angelic_design)"
  by (simp add: unrest_lens; pred_auto)

lemma pred_true_unrest_ok_in [unrest]:
  "$ok\<^sup>< \<sharp> (true :: 's angelic_design)"
  by (simp add: unrest_lens; pred_auto)

subsection \<open>Angelic Design Sequential Composition\<close>

(* Paper Definition 18: compose angelic designs through a hidden intermediate ok value. *)
definition angelic_design_seq ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design" (infixl ";;\<^sub>D\<^sub>A" 75)
where
[pred]: "angelic_design_seq P Q = (\<lambda> (s0, ac'). \<exists> ok0.
  P (s0, ok\<^sub>v_update (\<lambda>_. ok0)
    (des_vars.more_update (achoices.ac\<^sub>v_update (\<lambda>_.
        {s1. Q (ok\<^sub>v_update (\<lambda>_. ok0)
          (des_vars.more_update (astate.s\<^sub>v_update (\<lambda>_. s1)) s0), ac')})) ac')))"

(* Splitting the hidden intermediate observation into its two Boolean cases
   connects the design operator above to full-alphabet angelic composition. *)
lemma angelic_design_seq_ok_cases:
  "P ;;\<^sub>D\<^sub>A Q =
   ((P\<lbrakk>True/ok\<^sup>>\<rbrakk> ;;\<^sub>A\<^sub>D Q\<lbrakk>True/ok\<^sup><\<rbrakk>) \<or>
    (P\<lbrakk>False/ok\<^sup>>\<rbrakk> ;;\<^sub>A\<^sub>D Q\<lbrakk>False/ok\<^sup><\<rbrakk>))"
  by (simp add: angelic_design_seq_def aseq_ades_def fun_eq_iff
      ex_bool_eq subst_app_def subst_upd_def subst_id_def SEXP_def
      lens_defs des_vars.ok_def; pred_auto)

subsubsection \<open>Design-observation substitution laws\<close>

lemma design_ok_out_true_subst:
  assumes "$ok\<^sup>> \<sharp> P" "$ok\<^sup>> \<sharp> Q"
  shows "(P \<turnstile> Q)\<lbrakk>True/ok\<^sup>>\<rbrakk> = ((\<not> ok\<^sup><) \<or> (\<not> P) \<or> Q)"
  using assms
  by (simp add: design_def usubst usubst_eval; pred_auto)

lemma design_ok_out_false_subst:
  assumes "$ok\<^sup>> \<sharp> P"
  shows "(P \<turnstile> Q)\<lbrakk>False/ok\<^sup>>\<rbrakk> = ((\<not> ok\<^sup><) \<or> (\<not> P))"
  using assms
  by (simp add: design_def usubst usubst_eval; pred_auto)

lemma design_ok_in_true_subst:
  assumes "$ok\<^sup>< \<sharp> R" "$ok\<^sup>< \<sharp> S"
  shows "(R \<turnstile> S)\<lbrakk>True/ok\<^sup><\<rbrakk> = ((\<not> R) \<or> (S \<and> ok\<^sup>>))"
  using assms
  by (simp add: design_def usubst usubst_eval; pred_auto)

lemma design_ok_in_false_subst:
  "(R \<turnstile> S)\<lbrakk>False/ok\<^sup><\<rbrakk> = true"
  by (simp add: design_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs des_vars.ok_def;
      pred_auto)

lemma aseq_ades_ok_in_subst:
  "(P ;;\<^sub>A\<^sub>D Q)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> =
   (P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> ;;\<^sub>A\<^sub>D Q\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  by (simp add: aseq_ades_def fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs des_vars.ok_def
      des_more_ok_update_commute; pred_auto)

lemma ok_false_subst_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> ((P :: 's angelic_design)\<^sup>f)"
  apply (simp add: unrest_lens)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs des_more_ok_update_commute)
  done

lemma ok_true_subst_unrest_ok_out [unrest]:
  "$ok\<^sup>> \<sharp> ((P :: 's angelic_design)\<^sup>t)"
  apply (simp add: unrest_lens)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs des_more_ok_update_commute)
  done

lemma ok_in_subst_unrest_ok_in [unrest]:
  "$ok\<^sup>< \<sharp>
   ((P :: 's angelic_design)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)"
  apply (simp add: unrest_lens)
  apply (simp add: subst_app_def subst_upd_def subst_id_def
      SEXP_def lens_defs alpha_defs)
  done

lemma state_choice_ok_in_subst [usubst]:
  "ades_state_choice\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> = ades_state_choice"
  by (simp add: ades_state_choice_def fun_eq_iff subst_app_def
      subst_upd_def subst_id_def SEXP_def lens_defs; pred_auto)

lemma pred_true_ok_in_subst [usubst]:
  "(true :: 's angelic_design)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk> = true"
  by (simp add: fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

lemma subst_ok_in_absorb [simp]:
  "((P :: 's angelic_design)\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>)
      \<lbrakk>\<guillemotleft>c\<guillemotright>/ok\<^sup><\<rbrakk> =
   P\<lbrakk>\<guillemotleft>b\<guillemotright>/ok\<^sup><\<rbrakk>"
  by (simp add: fun_eq_iff subst_app_def subst_upd_def
      subst_id_def SEXP_def lens_defs; pred_auto)

(* Thesis Theorem T.4.5.1: pre/postcondition form. *)
definition angelic_design_seq_simplified ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
where [pred]: "angelic_design_seq_simplified P Q =
  ((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true) \<and> \<not> (post\<^sub>D P ;;\<^sub>A (\<not> pre\<^sub>D Q)))
   \<turnstile>\<^sub>r (post\<^sub>D P ;;\<^sub>A (pre\<^sub>D Q \<longrightarrow> post\<^sub>D Q)))"

(* Thesis Theorem T.4.5.15 *)
lemma angelic_design_seq_demonic:
  "(P \<sqinter>\<^sub>D\<^sub>A Q) ;;\<^sub>D\<^sub>A R =
   (P ;;\<^sub>D\<^sub>A R) \<sqinter>\<^sub>D\<^sub>A (Q ;;\<^sub>D\<^sub>A R)"
  by (simp add: angelic_design_seq_def angelic_design_demonic, pred_auto)

lemma angelic_design_seq_simplified_alt:
  "angelic_design_seq_simplified (P \<turnstile>\<^sub>r Q) (R \<turnstile>\<^sub>r S) =
   ((\<not> ((\<not> P) ;;\<^sub>A true) \<and> \<not> ((P \<longrightarrow> Q) ;;\<^sub>A (\<not> R)))
    \<turnstile>\<^sub>r
    ((P \<longrightarrow> Q) ;;\<^sub>A (R \<longrightarrow> S)))"
  by (pred_auto)

(* Thesis Theorem T.4.5.1 *)
lemma angelic_design_seq_eq_simplified:
  fixes P Q R S :: "('s astate, 's achoices) urel"
  assumes "PBMH (\<not> P) = (\<not> P)"
    and "PBMH Q = Q"
  shows
  "angelic_design_seq (P \<turnstile>\<^sub>r Q) (R \<turnstile>\<^sub>r S) =
   angelic_design_seq_simplified (P \<turnstile>\<^sub>r Q) (R \<turnstile>\<^sub>r S)"
proof (rule ext)
  fix x :: "'s astate des_vars_ext \<times> 's achoices des_vars_ext"
  obtain s0 ac' where x_eq: "x = (s0, ac')"
    by (cases x)
  have ok_cases:
    "(\<exists> ok0. ok_in \<and> P0 {s. ok0 \<and> R0 s \<longrightarrow> ok_out \<and> S0 s} \<longrightarrow>
        ok0 \<and> Q0 {s. ok0 \<and> R0 s \<longrightarrow> ok_out \<and> S0 s}) =
     (ok_in \<and> P0 UNIV \<and> P0 {s. \<not> R0 s} \<and> \<not> Q0 {s. \<not> R0 s} \<longrightarrow>
        ok_out \<and> (P0 {s. R0 s \<longrightarrow> S0 s} \<longrightarrow> Q0 {s. R0 s \<longrightarrow> S0 s}))"
    if nP_up: "\<And> X Y. X \<subseteq> Y \<Longrightarrow> \<not> P0 X \<Longrightarrow> \<not> P0 Y"
      and Q_up: "\<And> X Y. X \<subseteq> Y \<Longrightarrow> Q0 X \<Longrightarrow> Q0 Y"
    for P0 Q0 R0 S0 ok_in ok_out
  proof -
    have subset: "{s. \<not> R0 s} \<subseteq> {s. R0 s \<longrightarrow> S0 s}"
      by blast
    have nP_mono:
      "\<not> P0 {s. \<not> R0 s} \<Longrightarrow> \<not> P0 {s. R0 s \<longrightarrow> S0 s}"
      using nP_up subset by blast
    have Q_mono:
      "Q0 {s. \<not> R0 s} \<Longrightarrow> Q0 {s. R0 s \<longrightarrow> S0 s}"
      using Q_up subset by blast
    show ?thesis
      using nP_mono Q_mono
      by (cases ok_in; cases ok_out; simp add: ex_bool_eq; blast)
  qed
  show "angelic_design_seq (P \<turnstile>\<^sub>r Q) (R \<turnstile>\<^sub>r S) x =
    angelic_design_seq_simplified (P \<turnstile>\<^sub>r Q) (R \<turnstile>\<^sub>r S) x"
    using assms
    unfolding x_eq
    apply (simp add: angelic_design_seq_def angelic_design_seq_simplified_def aseq_def)
    apply (simp add: rdesign_def design_def)
    apply (pred_simp)
    apply (subst ok_cases)
      apply (cases "des_vars.more s0"; cases "des_vars.more ac'"; clarsimp)
      apply blast
     apply (cases "des_vars.more s0"; cases "des_vars.more ac'"; clarsimp)
     apply blast
    apply simp
    done
qed

(* Thesis Theorem T.4.5.2: simplified form when the left precondition
   does not depend on the final angelic choices. *)
lemma angelic_design_seq_simplified2:
  assumes "$ac\<^sup>> \<sharp> P"
    and "PBMH (\<not> P) = (\<not> P)"
    and "PBMH Q = Q"
  shows "angelic_design_seq (P \<turnstile>\<^sub>r Q) (R \<turnstile>\<^sub>r S) =
  ((P \<and> \<not> ((P \<longrightarrow> Q) ;;\<^sub>A (\<not> R))) \<turnstile>\<^sub>r
   ((P \<longrightarrow> Q) ;;\<^sub>A (R \<longrightarrow> S)))"
  using assms
  apply (subst angelic_design_seq_eq_simplified)
    apply assumption
   apply assumption
  apply (subst angelic_design_seq_simplified_alt)
  apply (simp add: unrest)
  done

end
