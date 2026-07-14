section \<open>Angelic Design Operators\<close>

theory utp_ades_ops
  imports utp_ades_core
begin

subsection \<open>Assignment\<close>

(* Definition 94. The assigned state is one available angelic choice. *)
definition assign_arel :: 
  "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "assign_arel x e = (\<lambda> (s0, ac').
  put\<^bsub>x\<^esub> (get\<^bsub>s\<^esub> s0) (e (get\<^bsub>s\<^esub> s0)) \<in> get\<^bsub>ac\<^esub> ac')"

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

lemma angelic_design_demonic:
  "P \<sqinter>\<^sub>D\<^sub>A Q = (P \<or> Q)"
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

(* TODO: Thesis T.4.5.16: A-healthy designs are closed under \<squnion>\<^sub>D\<^sub>A. *)

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

(* Definition 19. *)
definition aseq ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext" (infixl ";;\<^sub>A" 75)
where
(* P(s0, ac'[ac := {s1 | Q(s0[s := s1], ac')}]) *)
[pred]: "P ;;\<^sub>A Q = (\<lambda> (s0, ac').
  P (s0, put\<^bsub>ac\<^esub> ac' {s1. Q (put\<^bsub>s\<^esub> s0 s1, ac')}))"

lemma aseq_true_left [simp]:
  "true ;;\<^sub>A P = true"
  by (pred_auto)

lemma aseq_false_left [simp]:
  "false ;;\<^sub>A P = false"
  by (pred_auto)

(* (s \<in> ac') ;; P = P *)
lemma aseq_state_choice_left [simp]:
  "(($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e ;;\<^sub>A P) = P"
  by (pred_auto)

lemma aseq_true_right_unrest [simp]:
  assumes "$ac\<^sup>> \<sharp> P"
  shows "P ;;\<^sub>A true = P"
  using assms by (pred_auto assms: assms)

subsection \<open>PBMH\<close>

(* ac \<subseteq> ac' \<and> v' = v. *)
definition pbmh_step :: "(('s, '\<alpha>) achoices_scheme, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "pbmh_step = (($ac\<^sup>< \<subseteq> $ac\<^sup>>) \<and> $\<^bold>v\<^sub>A\<^sup>> = $\<^bold>v\<^sub>A\<^sup><)\<^sub>e"

(* Definition 15. *)
definition PBMH :: "('\<beta>, ('s, '\<alpha>) achoices_scheme) urel \<Rightarrow> ('\<beta>, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "PBMH P = (P ;; pbmh_step)"

subsection \<open>Angelic Design Sequential Composition\<close>

(* Paper Definition 18: compose angelic designs through a hidden intermediate ok value. *)
definition angelic_design_seq ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design" (infixl ";;\<^sub>D\<^sub>A" 75)
where
[pred]: "angelic_design_seq P Q = (\<lambda> (s0, ac'). \<exists> ok0.
  P (s0, put\<^bsub>ok\<^esub> (put\<^bsub>\<^bold>v\<^sub>D\<^esub> ac' (put\<^bsub>ac\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> ac')
    {s1. Q (put\<^bsub>ok\<^esub> (put\<^bsub>\<^bold>v\<^sub>D\<^esub> s0 (put\<^bsub>s\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> s0) s1)) ok0, ac')})) ok0))"

(* Thesis Theorem T.4.5.1: pre/postcondition form. *)
definition angelic_design_seq_simplified ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
where [pred]: "angelic_design_seq_simplified P Q =
  ((\<not> ((\<not> pre\<^sub>D P) ;;\<^sub>A true) \<and> \<not> (post\<^sub>D P ;;\<^sub>A (\<not> pre\<^sub>D Q)))
   \<turnstile>\<^sub>r (post\<^sub>D P ;;\<^sub>A (pre\<^sub>D Q \<longrightarrow> post\<^sub>D Q)))"

abbreviation dseq_ades ::
  "'s angelic_design \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
where "dseq_ades \<equiv> angelic_design_seq"

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
