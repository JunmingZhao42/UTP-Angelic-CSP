section \<open>Angelic Design Healthiness Conditions\<close>
(* Sec. 5.1 Definition 17. *)

theory utp_ades_healthy
  imports utp_ades_ops
begin

subsection \<open>PBMH\<close>

(* ac \<subseteq> ac' \<and> v' = v. *)
definition pbmh_step :: "(('s, '\<alpha>) achoices_scheme, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "pbmh_step = (($ac\<^sup>< \<subseteq> $ac\<^sup>>) \<and> $\<^bold>v\<^sub>A\<^sup>> = $\<^bold>v\<^sub>A\<^sup><)\<^sub>e"

(* Definition 15. *)
definition PBMH :: "('\<beta>, ('s, '\<alpha>) achoices_scheme) urel \<Rightarrow> ('\<beta>, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "PBMH P = (P ;; pbmh_step)"

lemma pbmh_step_idem:
  "pbmh_step ;; pbmh_step = pbmh_step"
  by (pred_auto)

lemma PBMH_idem:
  "PBMH (PBMH P) = PBMH P"
  by (simp add: PBMH_def seqr_assoc pbmh_step_idem)

lemma PBMH_Idempotent [closure]:
  "Idempotent PBMH"
  by (simp add: Idempotent_def PBMH_idem)

lemma PBMH_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> PBMH P \<sqsubseteq> PBMH Q"
  by (simp add: PBMH_def, rule seqr_mono, simp_all)

lemma PBMH_Monotonic [closure]:
  "Monotonic PBMH"
  by (rule MonotonicI, rule PBMH_mono)

lemma PBMH_neg_guard:
  "Q \<sqsubseteq> P \<Longrightarrow> (\<not> PBMH (\<not> Q)) \<sqsubseteq> (\<not> PBMH (\<not> P))"
  by (pred_auto)

lemma PBMH_guarded_post:
  "PBMH (P \<and> Q) \<sqsubseteq> ((\<not> PBMH (\<not> P)) \<and> PBMH Q)"
  by (pred_auto)

(* Lemma 3. PBMH (ac' = \<emptyset>) = true *)
lemma PBMH_ac_empty [simp]:
  "PBMH (($ac\<^sup>> = \<guillemotleft>{}\<guillemotright>)\<^sub>e) = true"
  by (pred_auto)

(* Lemma 15. PBMH (ac' \<noteq> \<emptyset>) = (ac' \<noteq> \<emptyset>) *)
lemma PBMH_ac_non_empty [simp]:
  "PBMH (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e) =
   (($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e)"
  by (pred_auto)

lemma PBMH_disj:
  "PBMH (P \<or> Q) = (PBMH P \<or> PBMH Q)"
  by (simp add: PBMH_def seqr_or_distl)

(* Theorem 64. PBMH commutes with the H1 guard. *)
lemma PBMH_H1_commute:
  "PBMH (ok\<^sup>< \<longrightarrow> P) = (ok\<^sup>< \<longrightarrow> PBMH P)"
  by (pred_auto)

lemma H2_lift_desr:
  "H2 (\<lceil>P\<rceil>\<^sub>D) = \<lceil>P\<rceil>\<^sub>D"
  by (pred_auto)

(* Theorem 65. PBMH and H2 commute, lifted through the design shell. *)
lemma PBMH_H2_commute:
  "H2 (\<lceil>PBMH P\<rceil>\<^sub>D) =
   \<lceil>PBMH (\<lfloor>H2 (\<lceil>P\<rceil>\<^sub>D)\<rfloor>\<^sub>D)\<rceil>\<^sub>D"
  by (simp add: H2_lift_desr)

subsection \<open>A0\<close>

definition ac_non_empty :: "'s angelic_design" where
[pred]: "ac_non_empty = \<lceil>($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e\<rceil>\<^sub>D"

definition A0 :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A0 P = (P \<and> ((ok\<^sup>< \<and> \<not> P\<^sup>f) \<longrightarrow> (ok\<^sup>> \<longrightarrow> ac_non_empty)))"

lemma A0_idem:
  "A0 (A0 P) = A0 P"
  by (pred_auto)

lemma A0_Idempotent [closure]:
  "Idempotent A0"
  by (simp add: Idempotent_def A0_idem)

lemma A0_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A0 P \<sqsubseteq> A0 Q"
  by (pred_auto)

lemma A0_Monotonic [closure]:
  "Monotonic A0"
  by (rule MonotonicI, rule A0_mono) 

(* Theorem 3. *)
lemma "A0 ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t) = ((\<not> P\<^sup>f) \<turnstile> (P\<^sup>t \<and> ac_non_empty))"
  by pred_auto

subsection \<open>A1\<close>

definition A1 :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A1 P = ((\<not> PBMH (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r PBMH (post\<^sub>D P))"

(* Lemma 16. Putting a design in PBMH. *)
lemma PBMH_rdesign:
  "A1 (P \<turnstile>\<^sub>r Q) =
   ((\<not> PBMH (\<not> P)) \<turnstile>\<^sub>r PBMH Q)"
  by (simp add: A1_def PBMH_disj rdesign_refinement, pred_auto)

lemma A1_idem:
  "A1 (A1 P) = A1 P"
  by (pred_auto)

lemma A1_Idempotent [closure]:
  "Idempotent A1"
  by (simp add: Idempotent_def A1_idem)

lemma A1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A1 P \<sqsubseteq> A1 Q"
  apply (simp add: A1_def)
  apply (rule rdesign_refine_intro')
   apply (rule PBMH_neg_guard)
   apply (insert design_refine_thms(1)[of P Q])
   apply (pred_auto)
  apply (rule_tac y="PBMH (pre\<^sub>D P \<and> post\<^sub>D Q)" in pred_ba.order_trans)
   apply (rule PBMH_guarded_post)
  apply (rule PBMH_mono)
  apply (insert design_refine_thms(2)[of P Q])
  apply (pred_auto)
  done

lemma A1_Monotonic [closure]:
  "Monotonic A1"
  by (rule MonotonicI, rule A1_mono)

subsection \<open>A\<close>

definition A :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A P = A0 (A1 P)"

lemma A_comp: "A = A0 \<circ> A1"
  by (auto simp add: A_def)

lemma A_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A P \<sqsubseteq> A Q"
  by (simp add: A_def A0_mono A1_mono)

lemma A_Monotonic [closure]:
  "Monotonic A"
  by (rule MonotonicI, rule A_mono)

lemma A_design_form:
  "A P =
   ((\<not> PBMH (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r
     (PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
  by (pred_auto)

lemma A_idem:
  "A (A P) = A P"
  by (simp add: A_design_form PBMH_idem rdesign_refinement, pred_auto)

lemma A_Idempotent [closure]:
  "Idempotent A"
  by (simp add: Idempotent_def A_idem)

lemma A_H1_commute:
  "H1 (A P) = A (H1 P)"
  by (simp add: A_design_form H1_rdesign, pred_auto)

lemma A_H2_commute:
  "H2 (A P) = A (H2 P)"
  by (simp add: A_design_form H2_rdesign H2_split PBMH_disj rdesign_refinement, pred_auto)

lemma A_is_H1:
  "H1 (A P) = A P"
  by (simp add: A_design_form H1_rdesign)

lemma A_is_H2:
  "H2 (A P) = A P"
  by (simp add: A_design_form H2_rdesign)

lemma A_is_design [closure]:
  "A P is \<^bold>H"
  by (simp add: A_design_form closure)

lemma A_healthy_design_form:
  "P is A \<Longrightarrow>
   P =
   ((\<not> PBMH (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r
     (PBMH (post\<^sub>D P) \<and> ($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e))"
  by (metis A_design_form Healthy_if)

(* corollary *)
lemma A_healthy_complete_lattice:
  "complete_lattice (fpl \<P> (A :: 's angelic_design \<Rightarrow> 's angelic_design))"
proof -
  interpret weak_complete_lattice "fpl \<P> (A :: 's angelic_design \<Rightarrow> 's angelic_design)"
    by (rule Knaster_Tarski, auto simp add: A_Monotonic)
  show ?thesis
    by (unfold_locales, simp add: fps_def sup_exists,
        (blast intro: sup_exists inf_exists)+)
qed

subsection \<open>A2\<close>

(* {s} = ac' *)
definition singleton_ac ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext" where
[pred]: "singleton_ac = (\<lambda> (s0, ac').
  get\<^bsub>ac\<^esub> ac' = {get\<^bsub>s\<^esub> s0})"

(* Definition 20. *)
definition A2_rel ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_rel_ext" where [pred]:
  "A2_rel P = PBMH (P ;;\<^sub>A singleton_ac)"

(* Theorem 4: expanded form of @{const A2_rel}. *)
definition A2_rel_expanded ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext"
where
[pred]: "A2_rel_expanded P = (\<lambda> (s0, ac').
  P (s0, put\<^bsub>ac\<^esub> ac' {}) \<or>
  (\<exists> y \<in> get\<^bsub>ac\<^esub> ac'. P (s0, put\<^bsub>ac\<^esub> ac' {y})))"

lemma singleton_choice_set_cases:
  assumes "P {x. X = {x}}" "X \<subseteq> Y" "\<And> y. y \<in> Y \<Longrightarrow> \<not> P {y}"
  shows "P {}"
proof (cases "\<exists> y. X = {y}")
  case True
  then obtain y where "X = {y}"
    by auto
  with assms show ?thesis
    by auto
next
  case False
  then have "{x. X = {x}} = {}"
    by auto
  with assms show ?thesis
    by auto
qed

lemma singleton_choice_set_empty_intro:
  "P {} \<Longrightarrow> \<exists> X. P {x. X = {x}} \<and> X \<subseteq> Y"
  by (rule_tac x="{}" in exI, auto)

lemma singleton_choice_set_single_intro:
  "y \<in> Y \<Longrightarrow> P {y} \<Longrightarrow> \<exists> X. P {x. X = {x}} \<and> X \<subseteq> Y"
  by (rule_tac x="{y}" in exI, auto)

lemma A2_rel_eq_expanded:
  "A2_rel P = A2_rel_expanded P"
  apply (pred_auto)
    apply (rule singleton_choice_set_cases)
      apply assumption
     apply assumption
    apply blast
  apply (rule singleton_choice_set_empty_intro, assumption)
  apply (rule singleton_choice_set_single_intro, assumption+)
  done

lemma A2_rel_expanded_disj:
  "A2_rel_expanded (P \<or> Q) = (A2_rel_expanded P \<or> A2_rel_expanded Q)"
  by (simp add: A2_rel_expanded_def, pred_auto)

lemma A2_rel_expanded_idem:
  "A2_rel_expanded (A2_rel_expanded P) = A2_rel_expanded P"
  by (pred_auto)

lemma A2_rel_disj:
  "A2_rel (P \<or> Q) = (A2_rel P \<or> A2_rel Q)"
  by (simp add: A2_rel_eq_expanded A2_rel_expanded_disj)

lemma A2_rel_idem:
  "A2_rel (A2_rel P) = A2_rel P"
  by (simp add: A2_rel_eq_expanded A2_rel_expanded_idem)

lemma A2_rel_Idempotent [closure]:
  "Idempotent A2_rel"
  by (simp add: Idempotent_def A2_rel_idem)

lemma A2_rel_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A2_rel P \<sqsubseteq> A2_rel Q"
  by (simp add: A2_rel_eq_expanded, pred_auto; blast)

lemma A2_rel_Monotonic [closure]:
  "Monotonic A2_rel"
  by (rule MonotonicI, rule A2_rel_mono)

lemma A2_rel_neg_guard:
  "Q \<sqsubseteq> P \<Longrightarrow> (\<not> A2_rel (\<not> Q)) \<sqsubseteq> (\<not> A2_rel (\<not> P))"
  by (simp add: A2_rel_eq_expanded, pred_auto; blast)

lemma A2_rel_guarded_post:
  "A2_rel (P \<and> Q) \<sqsubseteq> ((\<not> A2_rel (\<not> P)) \<and> A2_rel Q)"
  by (simp add: A2_rel_eq_expanded, pred_auto)

(* lemma L.4.2.3 in thesis *)
definition A2 :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "A2 P = ((\<not> A2_rel (\<not> pre\<^sub>D P)) \<turnstile>\<^sub>r A2_rel (post\<^sub>D P))"

lemma A2_rdesign:
  "A2 (P \<turnstile>\<^sub>r Q) = ((\<not> A2_rel (\<not> P)) \<turnstile>\<^sub>r A2_rel Q)"
  by (simp add: A2_def A2_rel_disj rdesign_refinement, pred_auto)

lemma A2_arel_to_ades:
  "A2 (arel_to_ades P) = arel_to_ades (A2_rel P)"
  by (simp add: arel_to_ades_def A2_rdesign, pred_auto)

lemma A2_idem:
  "A2 (A2 P) = A2 P"
  by (simp add: A2_def A2_rel_eq_expanded A2_rel_expanded_disj
      A2_rel_expanded_idem rdesign_refinement, pred_auto)

lemma A2_Idempotent [closure]:
  "Idempotent A2"
  by (simp add: Idempotent_def A2_idem)

lemma A2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> A2 P \<sqsubseteq> A2 Q"
  apply (simp add: A2_def)
  apply (rule rdesign_refine_intro')
   apply (rule A2_rel_neg_guard)
   apply (insert design_refine_thms(1)[of P Q])
   apply (pred_auto)
  apply (rule_tac y="A2_rel (pre\<^sub>D P \<and> post\<^sub>D Q)" in pred_ba.order_trans)
   apply (rule A2_rel_guarded_post)
  apply (rule A2_rel_mono)
  apply (insert design_refine_thms(2)[of P Q])
  apply (pred_auto)
  done

lemma A2_Monotonic [closure]:
  "Monotonic A2"
  by (rule MonotonicI, rule A2_mono)

end
