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

definition ac_non_empty :: "'s ades" where
[pred]: "ac_non_empty = \<lceil>($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e\<rceil>\<^sub>D"

definition A0 :: "'s ades \<Rightarrow> 's ades" where
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

definition A1 :: "'s ades \<Rightarrow> 's ades" where
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

definition A :: "'s ades \<Rightarrow> 's ades" where
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
  "complete_lattice (fpl \<P> (A :: 's ades \<Rightarrow> 's ades))"
proof -
  interpret weak_complete_lattice "fpl \<P> (A :: 's ades \<Rightarrow> 's ades)"
    by (rule Knaster_Tarski, auto simp add: A_Monotonic)
  show ?thesis
    by (unfold_locales, simp add: fps_def sup_exists,
        (blast intro: sup_exists inf_exists)+)
qed

end
