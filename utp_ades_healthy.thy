section \<open>Angelic Design Healthiness Conditions\<close>
(* Sec. 5.1 Definition 17. *)

theory utp_ades_healthy
  imports utp_ades_core
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

subsection \<open>A0\<close>

term "$ac\<^sup>> :: 's set"  (* ac' *)
term "{} :: 's set"     (* \<emptyset> *)
term "($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e"  (* ac' \<noteq> \<emptyset> *)
term "\<lceil>($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e\<rceil>\<^sub>D :: 's ades"

definition ac_non_empty :: "'s ades" where
[pred]: "ac_non_empty = \<lceil>($ac\<^sup>> \<noteq> \<guillemotleft>{}\<guillemotright>)\<^sub>e\<rceil>\<^sub>D"

term " \<not> P\<^sup>f :: ('a des_vars_scheme, 'b des_vars_scheme) urel"

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

end
