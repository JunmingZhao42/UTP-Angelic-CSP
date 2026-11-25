theory Sync_F_Laws
  imports Sync_Algebra
begin

section \<open>Healthiness of F\<close>

text \<open>We want F to give RAD processes. F is a join of RAD processes, and each RAD
  condition says something about single observations that a conjunction keeps, so
  a nonempty join of RAD processes is RAD.\<close>

lemma pred_Inf_eval:
  fixes A :: "('a \<Rightarrow> bool) set" and x :: 'a
  shows "(\<Squnion> A) x \<longleftrightarrow> (\<forall>P\<in>A. P x)"
  unfolding Inf_fun_def by auto

lemma RA1_Inf_closed:
  fixes A :: "('t::trace, 'e) reactive_angelic_design set"
  assumes ne: "A \<noteq> {}" and h: "\<And>P. P \<in> A \<Longrightarrow> P is RA1"
  shows "\<Squnion> A is RA1"
  unfolding Healthy_def'
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  have e: "P (ades_obs ok0 s0 c X) \<longleftrightarrow>
      P (ades_obs ok0 s0 c (rad_trace_extensions s0 \<inter> X)) \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}"
    if "P \<in> A" for P
    by (rule RA1_obs[of P ok0 s0 c X, unfolded Healthy_if[OF h[OF that]]])
  show "RA1 (\<Squnion> A) (ades_obs ok0 s0 c X) = (\<Squnion> A) (ades_obs ok0 s0 c X)"
    unfolding RA1_obs pred_Inf_eval using ne e by blast
qed

lemma RA2_Inf_closed:
  fixes A :: "('t::trace, 'e) reactive_angelic_design set"
  assumes h: "\<And>P. P \<in> A \<Longrightarrow> P is RA2"
  shows "\<Squnion> A is RA2"
  unfolding Healthy_def'
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  have e: "P (ades_obs ok0 s0 c X) \<longleftrightarrow>
      P (ades_obs ok0 (rad_zero_trace s0) c (rad_normalise_choices s0 X))"
    if "P \<in> A" for P
    by (rule RA2_obs'[of P ok0 s0 c X, unfolded Healthy_if[OF h[OF that]]])
  show "RA2 (\<Squnion> A) (ades_obs ok0 s0 c X) = (\<Squnion> A) (ades_obs ok0 s0 c X)"
    unfolding RA2_obs' pred_Inf_eval using e by blast
qed

lemma RA3_obs:
  "RA3 P (ades_obs ok0 s0 c X) \<longleftrightarrow>
    (if rad_wait\<^sub>v s0 then II_Rac (ades_obs ok0 s0 c X) else P (ades_obs ok0 s0 c X))"
  by (simp add: RA3_eval)

(* at a waiting prior an RA3 process is II_Rac *)
lemma RA3_waiting:
  assumes "P is RA3" "rad_wait\<^sub>v s0"
  shows "P (ades_obs ok0 s0 c X) \<longleftrightarrow> II_Rac (ades_obs ok0 s0 c X)"
proof -
  have "RA3 P (ades_obs ok0 s0 c X) \<longleftrightarrow> II_Rac (ades_obs ok0 s0 c X)"
    using assms(2) by (simp only: RA3_obs if_True)
  then show ?thesis by (simp only: Healthy_if[OF assms(1)])
qed

lemma RA3_Inf_closed:
  fixes A :: "('t::trace, 'e) reactive_angelic_design set"
  assumes ne: "A \<noteq> {}" and h: "\<And>P. P \<in> A \<Longrightarrow> P is RA3"
  shows "\<Squnion> A is RA3"
  unfolding Healthy_def'
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  show "RA3 (\<Squnion> A) (ades_obs ok0 s0 c X) = (\<Squnion> A) (ades_obs ok0 s0 c X)"
  proof (cases "rad_wait\<^sub>v s0")
    case True
    have "P (ades_obs ok0 s0 c X) \<longleftrightarrow> II_Rac (ades_obs ok0 s0 c X)" if "P \<in> A" for P
      by (rule RA3_waiting[OF h[OF that] True])
    then show ?thesis
      unfolding RA3_obs pred_Inf_eval using ne True by auto
  next
    case False
    then show ?thesis by (simp only: RA3_obs if_False)
  qed
qed

lemma CSPA1_Inf_closed:
  fixes A :: "('t::trace, 'e) reactive_angelic_design set"
  assumes h: "\<And>P. P \<in> A \<Longrightarrow> P is CSPA1"
  shows "\<Squnion> A is CSPA1"
  unfolding Healthy_def'
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  have e: "P (ades_obs ok0 s0 c X)"
    if "P \<in> A" "\<not> ok0" "rad_trace_extensions s0 \<inter> X \<noteq> {}" for P
  proof -
    have "CSPA1 P (ades_obs ok0 s0 c X)" unfolding CSPA1_obs using that(2,3) by blast
    then show ?thesis by (simp only: Healthy_if[OF h[OF that(1)]])
  qed
  show "CSPA1 (\<Squnion> A) (ades_obs ok0 s0 c X) = (\<Squnion> A) (ades_obs ok0 s0 c X)"
    unfolding CSPA1_obs pred_Inf_eval using e by blast
qed

(* an H2 process that may diverge may also terminate *)
lemma H2_up:
  assumes "H2 P = P" "P (ades_obs ok0 s0 False X)"
  shows "P (ades_obs ok0 s0 True X)"
proof -
  have "H2 P (ades_obs ok0 s0 True X)" unfolding H2_obs using assms(2) by blast
  then show ?thesis by (simp only: assms(1))
qed

lemma CSPA2_H2: "P is CSPA2 \<Longrightarrow> H2 P = P"
  by (simp only: Healthy_def' CSPA2_def)

lemma CSPA2_Inf_closed:
  fixes A :: "('t::trace, 'e) reactive_angelic_design set"
  assumes h: "\<And>P. P \<in> A \<Longrightarrow> P is CSPA2"
  shows "\<Squnion> A is CSPA2"
  unfolding Healthy_def' CSPA2_def
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  have e: "P (ades_obs ok0 s0 True X)" if "P \<in> A" "P (ades_obs ok0 s0 False X)" for P
    by (rule H2_up[OF CSPA2_H2[OF h[OF that(1)]] that(2)])
  show "H2 (\<Squnion> A) (ades_obs ok0 s0 c X) = (\<Squnion> A) (ades_obs ok0 s0 c X)"
  proof (cases c)
    case True
    then have c: "c = True" by simp
    show ?thesis using e unfolding c H2_obs pred_Inf_eval simp_thms by blast
  next
    case False
    then have c: "c = False" by simp
    show ?thesis by (simp only: c H2_obs pred_Inf_eval simp_thms)
  qed
qed

lemma PBMH_ades_Inf_closed:
  fixes A :: "('t::trace, 'e) reactive_angelic_design set"
  assumes h: "\<And>P. P \<in> A \<Longrightarrow> P is PBMH_ades"
  shows "\<Squnion> A is PBMH_ades"
  unfolding Healthy_def'
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  have e: "P (ades_obs ok0 s0 c X) \<longleftrightarrow> (\<exists>Y\<subseteq>X. P (ades_obs ok0 s0 c Y))" if "P \<in> A" for P
    by (rule PBMH_ades_obs[of P ok0 s0 c X, unfolded Healthy_if[OF h[OF that]]])
  show "PBMH_ades (\<Squnion> A) (ades_obs ok0 s0 c X) = (\<Squnion> A) (ades_obs ok0 s0 c X)"
    unfolding PBMH_ades_obs pred_Inf_eval using e by blast
qed

(* a nonempty join of RAD processes is RAD *)
lemma RAD_Inf_closed:
  fixes A :: "('t::trace, 'e) reactive_angelic_design set"
  assumes ne: "A \<noteq> {}" and h: "\<And>P. P \<in> A \<Longrightarrow> P is RAD"
  shows "\<Squnion> A is RAD"
proof -
  have c: "(P is RA1) \<and> (P is RA2) \<and> (P is RA3) \<and> (P is CSPA1) \<and> (P is CSPA2) \<and> (P is PBMH_ades)"
    if "P \<in> A" for P
    using h[OF that] by (simp only: RAD_components_iff)
  have "\<Squnion> A is RA1" by (rule RA1_Inf_closed[OF ne]) (use c in blast)
  moreover have "\<Squnion> A is RA2" by (rule RA2_Inf_closed) (use c in blast)
  moreover have "\<Squnion> A is RA3" by (rule RA3_Inf_closed[OF ne]) (use c in blast)
  moreover have "\<Squnion> A is CSPA1" by (rule CSPA1_Inf_closed) (use c in blast)
  moreover have "\<Squnion> A is CSPA2" by (rule CSPA2_Inf_closed) (use c in blast)
  moreover have "\<Squnion> A is PBMH_ades" by (rule PBMH_ades_Inf_closed) (use c in blast)
  ultimately show ?thesis by (simp only: RAD_components_iff)
qed

lemma Chaos_RAD_A2: "Chaos\<^sub>R\<^sub>A\<^sub>D is A2"
  unfolding Healthy_def' by (rule ades_obs_ext) (simp add: A2_obs Chaos_RAD_eval)

lemma top_RAD_A2: "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D is A2"
  unfolding Healthy_def' by (rule ades_obs_ext) (simp add: A2_obs top_RAD_eval)

lemma Chaos_RAD_below: "P is RAD \<Longrightarrow> Chaos\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> P"
  using bottom_RAD_lower[of P] by (simp only: bottom_RAD_is_Chaos)

lemma rad_par_F_RAD:
  assumes "P is RAD" "Q is RAD"
  shows "rad_par_F P j Q is RAD"
  unfolding rad_par_F_def
proof (rule RAD_Inf_closed)
  have "Chaos\<^sub>R\<^sub>A\<^sub>D \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Chaos\<^sub>R\<^sub>A\<^sub>D \<in> {g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h | g h.
      (g is RAD) \<and> (g is A2) \<and> (h is RAD) \<and> (h is A2) \<and> g \<sqsubseteq> P \<and> h \<sqsubseteq> Q}"
    using Chaos_RAD_is_RAD Chaos_RAD_A2 Chaos_RAD_below[OF assms(1)] Chaos_RAD_below[OF assms(2)]
    by blast
  then show "{g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h | g h.
      (g is RAD) \<and> (g is A2) \<and> (h is RAD) \<and> (h is A2) \<and> g \<sqsubseteq> P \<and> h \<sqsubseteq> Q} \<noteq> {}"
    by blast
next
  fix X
  assume "X \<in> {g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h | g h.
      (g is RAD) \<and> (g is A2) \<and> (h is RAD) \<and> (h is A2) \<and> g \<sqsubseteq> P \<and> h \<sqsubseteq> Q}"
  then obtain g h where "X = g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h" "g is RAD" "h is RAD" by blast
  then show "X is RAD" by (simp only: rad_par_RAD)
qed

(* on CSP processes F stays CSP *)
lemma rad_par_F_A2_closed:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "rad_par_F P j Q is A2"
  using rad_par_A2[OF assms] by (simp only: rad_par_F_A2[OF assms(1,3,2,4)])


section \<open>Commutativity, zeros and one-way distribution\<close>

lemma rad_par_F_comm:
  assumes "j is SymMerge"
  shows "rad_par_F P j Q = rad_par_F Q j P"
proof -
  have one: "rad_par_F Q j P x" if F: "rad_par_F P j Q x" for P Q x
    unfolding rad_par_F_eval
  proof (intro allI impI)
    fix g h
    assume gh: "g is RAD" "g is A2" "h is RAD" "h is A2" "g \<sqsubseteq> Q" "h \<sqsubseteq> P"
    from F[unfolded rad_par_F_eval, rule_format, OF gh(3,4,1,2,6,5)]
    have "(h \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> g) x" .
    then show "(g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h) x" by (simp only: rad_par_comm[OF assms, where P=h and Q=g])
  qed
  show ?thesis by (rule ext) (use one in blast)
qed

lemma rad_dchoice_eval: "(P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) x \<longleftrightarrow> P x \<or> Q x"
  by (simp only: sup_fun_def sup_bool_def)

lemma ref_refl_pred: "P \<sqsubseteq> P" for P :: "'a pred"
  by (simp only: ref_by_pred_is_leq order_refl)

(* (P \<parallel>F Q) \<squnion> (P \<parallel>F R) \<sqsubseteq> P \<parallel>F (Q \<squnion> R) *)
lemma rad_par_F_angelic_subdist:
  "rad_par_F P j Q \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_par_F P j R \<sqsubseteq> rad_par_F P j (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R)"
proof -
  have "Q \<sqsubseteq> Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R" by (simp only: ref_by_pred_is_leq) (rule inf_le1)
  from rad_par_F_mono[OF ref_refl_pred[of P] this, where j=j, unfolded pred_refine_iff]
  have q: "rad_par_F P j (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R) x \<Longrightarrow> rad_par_F P j Q x" for x
    by blast
  have "R \<sqsubseteq> Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R" by (simp only: ref_by_pred_is_leq) (rule inf_le2)
  from rad_par_F_mono[OF ref_refl_pred[of P] this, where j=j, unfolded pred_refine_iff]
  have r: "rad_par_F P j (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R) x \<Longrightarrow> rad_par_F P j R x" for x
    by blast
  show ?thesis
    unfolding pred_refine_iff
  proof (intro allI impI)
    fix x assume "rad_par_F P j (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R) x"
    with q r have "rad_par_F P j Q x" "rad_par_F P j R x" by blast+
    then show "(rad_par_F P j Q \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_par_F P j R) x" by (simp only: rad_achoice_eval)
  qed
qed

(* P \<parallel>F (Q \<sqinter> R) \<sqsubseteq> (P \<parallel>F Q) \<sqinter> (P \<parallel>F R) *)
lemma rad_par_F_demonic_subdist:
  "rad_par_F P j (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) \<sqsubseteq> rad_par_F P j Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D rad_par_F P j R"
proof -
  have "Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R \<sqsubseteq> Q" by (simp only: ref_by_pred_is_leq) (rule sup_ge1)
  from rad_par_F_mono[OF ref_refl_pred[of P] this, where j=j, unfolded pred_refine_iff]
  have q: "rad_par_F P j Q x \<Longrightarrow> rad_par_F P j (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) x" for x
    by blast
  have "Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R \<sqsubseteq> R" by (simp only: ref_by_pred_is_leq) (rule sup_ge2)
  from rad_par_F_mono[OF ref_refl_pred[of P] this, where j=j, unfolded pred_refine_iff]
  have r: "rad_par_F P j R x \<Longrightarrow> rad_par_F P j (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) x" for x
    by blast
  show ?thesis
    unfolding pred_refine_iff
  proof (intro allI impI)
    fix x assume "(rad_par_F P j Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D rad_par_F P j R) x"
    then have "rad_par_F P j Q x \<or> rad_par_F P j R x" by (simp only: rad_dchoice_eval)
    with q r show "rad_par_F P j (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) x" by blast
  qed
qed

text \<open>We want Miracle and Chaos to be zeros of F, with the premises of the RAD laws.
  F lies below the lift, which gives one direction. The other direction picks
  Chaos as the CSP process below the other operand.\<close>

lemma rad_par_F_miracle:
  fixes P :: "('t::trace, 'e) reactive_angelic_design" and j :: "('t \<times> 'e set) merge"
  assumes "P is RAD"
  shows "rad_par_F P j \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
        "rad_par_F \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D j P = \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
proof -
  have c: "Chaos\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> P" by (rule Chaos_RAD_below[OF assms])
  have t: "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D" by (rule ref_refl_pred)
  have below1: "rad_par_F P j \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
    using rad_par_F_below[of P j "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"] by (simp only: rad_par_miracle(1)[OF assms])
  have below2: "rad_par_F \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D j P \<sqsubseteq> \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
    using rad_par_F_below[of "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D" j P] by (simp only: rad_par_miracle(2)[OF assms])
  show "rad_par_F P j \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
  proof (rule ext, rule iffI)
    fix x assume "rad_par_F P j \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D x"
    from this[unfolded rad_par_F_eval, rule_format,
        OF Chaos_RAD_is_RAD Chaos_RAD_A2 RAD_healthy top_RAD_A2 c t]
    show "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D x" by (simp only: rad_par_miracle(1)[OF Chaos_RAD_is_RAD])
  next
    fix x assume "(\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D :: ('t, 'e) reactive_angelic_design) x"
    then show "rad_par_F P j \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D x" using below1[unfolded pred_refine_iff] by blast
  qed
  show "rad_par_F \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D j P = \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
  proof (rule ext, rule iffI)
    fix x assume "rad_par_F \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D j P x"
    from this[unfolded rad_par_F_eval, rule_format,
        OF RAD_healthy top_RAD_A2 Chaos_RAD_is_RAD Chaos_RAD_A2 t c]
    show "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D x" by (simp only: rad_par_miracle(2)[OF Chaos_RAD_is_RAD])
  next
    fix x assume "(\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D :: ('t, 'e) reactive_angelic_design) x"
    then show "rad_par_F \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D j P x" using below2[unfolded pred_refine_iff] by blast
  qed
qed

lemma rad_par_F_chaos:
  fixes P :: "('t::trace, 'e) reactive_angelic_design" and j :: "('t \<times> 'e set) merge"
  assumes rad: "P is RAD"
      and stop: "(ac2p P \<and> ($tr\<^sup>> = $tr\<^sup><)\<^sub>e) is H4"
      and empty: "\<And>s sL sR. \<exists>s'. merge_eval j (0, s) (0, sL) (0, sR) (0, s')"
  shows "rad_par_F P j Chaos\<^sub>R\<^sub>A\<^sub>D = Chaos\<^sub>R\<^sub>A\<^sub>D"
        "rad_par_F Chaos\<^sub>R\<^sub>A\<^sub>D j P = Chaos\<^sub>R\<^sub>A\<^sub>D"
proof -
  have c: "Chaos\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> P" by (rule Chaos_RAD_below[OF rad])
  have cc: "Chaos\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> Chaos\<^sub>R\<^sub>A\<^sub>D" by (rule ref_refl_pred)
  have upper: "Chaos\<^sub>R\<^sub>A\<^sub>D x" if "(Chaos\<^sub>R\<^sub>A\<^sub>D \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Chaos\<^sub>R\<^sub>A\<^sub>D) x" for x
    using Chaos_RAD_below[OF rad_par_RAD[OF Chaos_RAD_is_RAD Chaos_RAD_is_RAD, of j],
        unfolded pred_refine_iff] that by blast
  have below1: "rad_par_F P j Chaos\<^sub>R\<^sub>A\<^sub>D \<sqsubseteq> Chaos\<^sub>R\<^sub>A\<^sub>D"
    using rad_par_F_below[of P j Chaos\<^sub>R\<^sub>A\<^sub>D] by (simp only: rad_par_chaos(1)[OF rad stop empty])
  have below2: "rad_par_F Chaos\<^sub>R\<^sub>A\<^sub>D j P \<sqsubseteq> Chaos\<^sub>R\<^sub>A\<^sub>D"
    using rad_par_F_below[of Chaos\<^sub>R\<^sub>A\<^sub>D j P] by (simp only: rad_par_chaos(2)[OF rad stop empty])
  show "rad_par_F P j Chaos\<^sub>R\<^sub>A\<^sub>D = Chaos\<^sub>R\<^sub>A\<^sub>D"
  proof (rule ext, rule iffI)
    fix x assume "rad_par_F P j Chaos\<^sub>R\<^sub>A\<^sub>D x"
    from this[unfolded rad_par_F_eval, rule_format,
        OF Chaos_RAD_is_RAD Chaos_RAD_A2 Chaos_RAD_is_RAD Chaos_RAD_A2 c cc]
    show "Chaos\<^sub>R\<^sub>A\<^sub>D x" by (rule upper)
  next
    fix x assume "(Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t, 'e) reactive_angelic_design) x"
    then show "rad_par_F P j Chaos\<^sub>R\<^sub>A\<^sub>D x" using below1[unfolded pred_refine_iff] by blast
  qed
  show "rad_par_F Chaos\<^sub>R\<^sub>A\<^sub>D j P = Chaos\<^sub>R\<^sub>A\<^sub>D"
  proof (rule ext, rule iffI)
    fix x assume "rad_par_F Chaos\<^sub>R\<^sub>A\<^sub>D j P x"
    from this[unfolded rad_par_F_eval, rule_format,
        OF Chaos_RAD_is_RAD Chaos_RAD_A2 Chaos_RAD_is_RAD Chaos_RAD_A2 cc c]
    show "Chaos\<^sub>R\<^sub>A\<^sub>D x" by (rule upper)
  next
    fix x assume "(Chaos\<^sub>R\<^sub>A\<^sub>D :: ('t, 'e) reactive_angelic_design) x"
    then show "rad_par_F Chaos\<^sub>R\<^sub>A\<^sub>D j P x" using below2[unfolded pred_refine_iff] by blast
  qed
qed


section \<open>Distribution over angelic choice fails with divergence\<close>

text \<open>We want to know whether F distributes over angelic choice once processes may
  diverge. We weaken a process so that at every started, non-waiting prior each of
  its observations may also diverge. Joined with a process that never diverges
  there, the weakened process is the same as the original, but its parallel
  with a partner can diverge. Since Chaos is the unit of angelic choice, the
  distributed form loses the deadlock.\<close>

(* rad_div P (ok, s, ok', ac') = P (ok, s, ok' \<or> ok \<and> \<not>wait, ac') *)
definition rad_div ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
  "rad_div P = (\<lambda>(x, z). P (x, des_vars.ok\<^sub>v_update
     (\<lambda>c. c \<or> des_vars.ok\<^sub>v x \<and> \<not> rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))) z))"

lemma rad_div_obs:
  "rad_div P (ades_obs ok0 s0 c X) \<longleftrightarrow> P (ades_obs ok0 s0 (c \<or> ok0 \<and> \<not> rad_wait\<^sub>v s0) X)"
  by (simp add: rad_div_def)

lemma rad_div_RAD:
  assumes "P is RAD"
  shows "rad_div P is RAD"
proof -
  have p: "P is RA1" "P is RA2" "P is RA3" "P is CSPA1" "P is CSPA2" "P is PBMH_ades"
    using assms[unfolded RAD_components_iff] by blast+
  have "rad_div P is RA1"
    unfolding Healthy_def'
  proof (rule ades_obs_ext)
    fix ok0 s0 c X
    show "RA1 (rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
      unfolding RA1_obs rad_div_obs
      by (rule RA1_obs[of P ok0 s0 "c \<or> ok0 \<and> \<not> rad_wait\<^sub>v s0" X, unfolded Healthy_if[OF p(1)], symmetric])
  qed
  moreover have "rad_div P is RA2"
    unfolding Healthy_def'
  proof (rule ades_obs_ext)
    fix ok0 s0 c X
    show "RA2 (rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
      unfolding RA2_obs' rad_div_obs rad_zero_trace_wait
      by (rule RA2_obs'[of P ok0 s0 "c \<or> ok0 \<and> \<not> rad_wait\<^sub>v s0" X, unfolded Healthy_if[OF p(2)], symmetric])
  qed
  moreover have "rad_div P is RA3"
    unfolding Healthy_def'
  proof (rule ades_obs_ext)
    fix ok0 s0 c X
    show "RA3 (rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
    proof (cases "rad_wait\<^sub>v s0")
      case True
      then show ?thesis
        unfolding RA3_obs rad_div_obs using RA3_waiting[OF p(3) True, of ok0 c X] by simp
    next
      case False
      then show ?thesis by (simp only: RA3_obs if_False)
    qed
  qed
  moreover have "rad_div P is CSPA1"
    unfolding Healthy_def'
  proof (rule ades_obs_ext)
    fix ok0 s0 c X
    have "P (ades_obs False s0 c X)" if "rad_trace_extensions s0 \<inter> X \<noteq> {}"
    proof -
      have "CSPA1 P (ades_obs False s0 c X)" unfolding CSPA1_obs using that by blast
      then show ?thesis by (simp only: Healthy_if[OF p(4)])
    qed
    then show "CSPA1 (rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
      unfolding CSPA1_obs rad_div_obs by (cases ok0) auto
  qed
  moreover have "rad_div P is CSPA2"
    unfolding Healthy_def' CSPA2_def
  proof (rule ades_obs_ext)
    fix ok0 s0 c X
    have "P (ades_obs ok0 s0 False X) \<Longrightarrow> P (ades_obs ok0 s0 True X)"
      by (rule H2_up[OF CSPA2_H2[OF p(5)]])
    then show "H2 (rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
      unfolding H2_obs rad_div_obs by (cases c; cases ok0; cases "rad_wait\<^sub>v s0") auto
  qed
  moreover have "rad_div P is PBMH_ades"
    unfolding Healthy_def'
  proof (rule ades_obs_ext)
    fix ok0 s0 c X
    show "PBMH_ades (rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
      unfolding PBMH_ades_obs rad_div_obs
      by (rule PBMH_ades_obs[of P ok0 s0 "c \<or> ok0 \<and> \<not> rad_wait\<^sub>v s0" X,
            unfolded Healthy_if[OF p(6)], symmetric])
  qed
  ultimately show ?thesis by (simp only: RAD_components_iff)
qed

lemma rad_div_A2:
  assumes "P is A2"
  shows "rad_div P is A2"
  unfolding Healthy_def'
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  show "A2 (rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
    unfolding A2_obs rad_div_obs
    by (rule A2_obs[of P ok0 s0 "c \<or> ok0 \<and> \<not> rad_wait\<^sub>v s0" X, unfolded Healthy_if[OF assms], symmetric])
qed

(* the weakened process is below the original *)
lemma rad_div_below:
  assumes "P is RAD"
  shows "rad_div P \<sqsubseteq> P"
proof -
  have up: "P (ades_obs ok0 s0 False X) \<Longrightarrow> P (ades_obs ok0 s0 True X)" for ok0 s0 X
    by (rule H2_up[OF CSPA2_H2[OF RAD_is_CSPA2[OF assms]]])
  have "P \<sqinter> rad_div P = rad_div P"
  proof (rule ades_obs_ext)
    fix ok0 s0 c X
    show "(P \<sqinter> rad_div P) (ades_obs ok0 s0 c X) = rad_div P (ades_obs ok0 s0 c X)"
      unfolding rad_dchoice_eval rad_div_obs
      using up[of ok0 s0 X] by (cases c; cases ok0; cases "rad_wait\<^sub>v s0") auto
  qed
  then show ?thesis by (simp only: ref_by_pred_is_leq le_iff_sup)
qed

(* a\<rightarrow>Skip never diverges at a started prior *)
lemma PrefixSkip_RAD_ok:
  "\<not> rad_wait\<^sub>v s0 \<Longrightarrow> PrefixSkip_RAD a (ades_obs True s0 c X) \<Longrightarrow> c"
  by (simp add: PrefixSkip_RAD_obs)

(* the angel avoids the divergence: a\<rightarrow>Skip \<squnion> rad_div (b\<rightarrow>Skip) = a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip *)
lemma rad_div_join:
  "PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_div (PrefixSkip_RAD b) = PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
proof (rule ades_obs_ext)
  fix ok0 s0 c X
  show "(PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_div (PrefixSkip_RAD b)) (ades_obs ok0 s0 c X) =
        (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) (ades_obs ok0 s0 c X)"
  proof (cases "ok0 \<and> \<not> rad_wait\<^sub>v s0")
    case True
    then have ok0: ok0 and w: "\<not> rad_wait\<^sub>v s0" by simp_all
    have "PrefixSkip_RAD a (ades_obs True s0 c X) \<Longrightarrow> c" by (rule PrefixSkip_RAD_ok[OF w])
    then show ?thesis unfolding rad_achoice_eval rad_div_obs using ok0 w by auto
  next
    case False
    then have "c \<or> ok0 \<and> \<not> rad_wait\<^sub>v s0 \<longleftrightarrow> c" by blast
    then show ?thesis by (simp only: rad_achoice_eval rad_div_obs)
  qed
qed

(* a\<rightarrow>Skip \<parallel> a\<rightarrow>Skip can end after a *)
lemma rad_sync_aa_done:
  assumes s0: "\<not> rad_wait\<^sub>v s0"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a) (ades_obs True s0 True {done_a a s0})"
  unfolding rad_par_obs
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  using pobs_done[of a s0] s0
  by (simp add: PrefixSkip_RAD_obs merge_rdes_started minus_list_def)

(* both wait at the start, the right one diverging, so anything may follow *)
lemma rad_sync_div_obs:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> rad_div (PrefixSkip_RAD b))
           (ades_obs True s0 True {done_a a s0})"
  unfolding rad_par_obs
  apply (rule exI[where x=True], rule exI[where x="{wait_ref b s0}"])
  apply (rule exI[where x=False], rule exI[where x="{wait_ref a s0}"])
  using s0 ab
  by (simp add: rad_div_obs PrefixSkip_RAD_obs[OF s0] pobs_def merge_rdes_eval minus_list_def)

(* no monotone parallel that agrees with RAD parallel on these CSP processes
   distributes over \<squnion> on the right *)
theorem sync_no_angelic_dist:
  fixes a b :: 'e and par :: "('e list, 'e) reactive_angelic_design \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
                ('e list, 'e) reactive_angelic_design"
  assumes ab: "a \<noteq> b"
    and mono: "\<And>Q Q'. Q \<sqsubseteq> Q' \<Longrightarrow> par (PrefixSkip_RAD a) Q \<sqsubseteq> par (PrefixSkip_RAD a) Q'"
    and agree_a: "par (PrefixSkip_RAD a) (PrefixSkip_RAD a) =
                  PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a"
    and agree_b: "par (PrefixSkip_RAD a) (PrefixSkip_RAD b) =
                  PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b"
    and agree_d: "par (PrefixSkip_RAD a) (rad_div (PrefixSkip_RAD b)) =
                  PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> rad_div (PrefixSkip_RAD b)"
    and dist: "par (PrefixSkip_RAD a) (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_div (PrefixSkip_RAD b)) =
               par (PrefixSkip_RAD a) (PrefixSkip_RAD a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
               par (PrefixSkip_RAD a) (rad_div (PrefixSkip_RAD b))"
  shows False
proof -
  have w: "\<not> rad_wait\<^sub>v (s_start :: ('e list, 'e) rad_state)" by simp
  have "par (PrefixSkip_RAD a) (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_div (PrefixSkip_RAD b))
          (ades_obs True s_start True {done_a a s_start})"
    unfolding dist rad_achoice_eval agree_a agree_d
    using rad_sync_aa_done[OF w] rad_sync_div_obs[OF w ab] by blast
  then have ab_obs: "par (PrefixSkip_RAD a) (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)
          (ades_obs True s_start True {done_a a s_start})"
    by (simp only: rad_div_join)
  have "PrefixSkip_RAD b \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
    by (simp only: ref_by_pred_is_leq) (rule inf_le2)
  from mono[OF this, unfolded pred_refine_iff, rule_format, OF ab_obs]
  have "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) (ades_obs True s_start True {done_a a s_start})"
    by (simp only: agree_b)
  with rad_sync_ab_not_done[OF w ab] show False by contradiction
qed

corollary rad_par_F_not_angelic_dist:
  fixes a b :: 'e
  assumes ab: "a \<noteq> b"
  shows "rad_par_F (PrefixSkip_RAD a) jsync (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_div (PrefixSkip_RAD b)) \<noteq>
         rad_par_F (PrefixSkip_RAD a) jsync (PrefixSkip_RAD a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
         rad_par_F (PrefixSkip_RAD a) jsync (rad_div (PrefixSkip_RAD b))"
proof
  assume dist: "rad_par_F (PrefixSkip_RAD a) jsync (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D rad_div (PrefixSkip_RAD b)) =
         rad_par_F (PrefixSkip_RAD a) jsync (PrefixSkip_RAD a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
         rad_par_F (PrefixSkip_RAD a) jsync (rad_div (PrefixSkip_RAD b))"
  have mono: "rad_par_F (PrefixSkip_RAD a) jsync Q \<sqsubseteq> rad_par_F (PrefixSkip_RAD a) jsync Q'"
    if "Q \<sqsubseteq> Q'" for Q Q' :: "('e list, 'e) reactive_angelic_design"
    by (rule rad_par_F_mono[OF ref_refl_pred that])
  have agree: "rad_par_F (PrefixSkip_RAD a) jsync Q = PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> Q"
    if "Q is RAD" "Q is A2" for Q :: "('e list, 'e) reactive_angelic_design"
    by (rule rad_par_F_A2[OF PrefixSkip_RAD_is_RAD PrefixSkip_RAD_is_A2 that])
  show False
    by (rule sync_no_angelic_dist[where par="\<lambda>P Q. rad_par_F P jsync Q", OF ab mono
          agree[OF PrefixSkip_RAD_is_RAD PrefixSkip_RAD_is_A2]
          agree[OF PrefixSkip_RAD_is_RAD PrefixSkip_RAD_is_A2]
          agree[OF rad_div_RAD[OF PrefixSkip_RAD_is_RAD] rad_div_A2[OF PrefixSkip_RAD_is_A2]]
          dist])
qed


section \<open>F does not distribute over demonic choice\<close>

text \<open>We want a concrete RAD instance of the failure that the interchange result
  forces. With a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip on the left, F of a\<rightarrow>Skip \<sqinter> b\<rightarrow>Skip can end
  after a or after b, while each of the two distributed parts can deadlock.\<close>

(* both done observations, a choice set no single prefix process can avoid *)
abbreviation done_ab :: "'e \<Rightarrow> 'e \<Rightarrow> ('e list, 'e) rad_state \<Rightarrow> ('e list, 'e) rad_state set" where
  "done_ab a b s0 \<equiv> {done_a a s0, done_a b s0}"

lemma A2_below_angelic_done:
  assumes s0: "\<not> rad_wait\<^sub>v s0"
    and g: "g is RAD" "g is A2" "g \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
  shows "g (ades_obs True s0 True {done_a a s0}) \<or> g (ades_obs True s0 True {done_a b s0})"
proof -
  have "(PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) (ades_obs True s0 True (done_ab a b s0))"
    using pobs_done[of a s0] pobs_done[of b s0]
    by (simp add: rad_achoice_eval PrefixSkip_RAD_obs[OF s0])
  from g(3)[unfolded pred_refine_iff, rule_format, OF this]
  have gZ: "g (ades_obs True s0 True (done_ab a b s0))" .
  have up: "g (ades_obs True s0 True {}) \<Longrightarrow> g (ades_obs True s0 True {done_a a s0})"
    using PBMH_ades_obs[of g True s0 True "{done_a a s0}"]
    by (simp only: Healthy_if[OF RAD_is_PBMH_ades[OF g(1)]]; blast)
  have a2: "g (ades_obs True s0 True (done_ab a b s0)) \<longleftrightarrow>
      g (ades_obs True s0 True {}) \<or> (\<exists>z\<in>done_ab a b s0. g (ades_obs True s0 True {z}))"
    using A2_obs[of g True s0 True "done_ab a b s0"]
    by (simp only: Healthy_if[OF g(2)])
  from gZ a2 up show ?thesis by auto
qed

lemma rad_sync_done_done:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and Z: "done_a e s0 \<in> Z"
    and g: "g (ades_obs True s0 True {done_a e s0})" and h: "h (ades_obs True s0 True {done_a e s0})"
  shows "(g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> h) (ades_obs True s0 True Z)"
proof -
  have m: "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = done_a e s0\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = done_a e s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = done_a e s0\<rparr>"
    using s0 by (simp add: merge_rdes_started minus_list_def)
  show ?thesis
    unfolding rad_par_obs
    apply (rule exI[where x=True], rule exI[where x="{done_a e s0}"])
    apply (rule exI[where x=True], rule exI[where x="{done_a e s0}"])
    using g h Z m by blast
qed

(* a\<rightarrow>Skip \<parallel> b\<rightarrow>Skip offers no choice set made of later states *)
lemma rad_sync_ab_stuck:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
    and Z: "\<forall>s'\<in>Z. rad_tr\<^sub>v s' \<noteq> rad_tr\<^sub>v s0"
  shows "\<not> (PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) (ades_obs True s0 True Z)"
proof
  assume "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) (ades_obs True s0 True Z)"
  then obtain okL acL okR acR
    where L: "PrefixSkip_RAD a (ades_obs True s0 okL acL)"
      and R: "PrefixSkip_RAD b (ades_obs True s0 okR acR)"
      and M: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>Z. merge_eval (merge_rdes jsync)
         \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>"
    unfolding rad_par_obs by blast
  from L obtain yL where yL: "yL \<in> acL" "pobs a s0 yL" and okL: okL
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  from R obtain yR where yR: "yR \<in> acR" "pobs b s0 yR" and okR: okR
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  have "\<exists>s'\<in>Z. merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yR\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>"
    using bspec[OF bspec[OF M yL(1)] yR(1)] okL okR by simp
  then obtain s' where s': "s' \<in> Z" "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yR\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>"
    by blast
  from sync_pair_stuck[OF s0 ab yL(2) yR(2) s'(2)] bspec[OF Z s'(1)]
  show False by contradiction
qed

theorem rad_par_F_not_demonic_dist:
  fixes a b :: 'e
  assumes ab: "a \<noteq> b"
  shows "rad_par_F (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) jsync (PrefixSkip_RAD a \<sqinter>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) \<noteq>
         rad_par_F (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) jsync (PrefixSkip_RAD a) \<sqinter>\<^sub>R\<^sub>A\<^sub>D
         rad_par_F (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) jsync (PrefixSkip_RAD b)"
    (is "?L \<noteq> ?R")
proof
  assume eq: "?L = ?R"
  let ?x = "ades_obs True s_start True (done_ab a b s_start)"
  have w: "\<not> rad_wait\<^sub>v (s_start :: ('e list, 'e) rad_state)" by simp
  have da: "PrefixSkip_RAD a (ades_obs True s_start True {done_a a s_start})"
    using pobs_done[of a s_start] by (simp add: PrefixSkip_RAD_obs[OF w])
  have db: "PrefixSkip_RAD b (ades_obs True s_start True {done_a b s_start})"
    using pobs_done[of b s_start] by (simp add: PrefixSkip_RAD_obs[OF w])
  have L: "?L ?x"
    unfolding rad_par_F_eval
  proof (intro allI impI)
    fix g h
    assume g: "g is RAD" "g is A2" "g \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
      and h: "h is RAD" "h is A2" "h \<sqsubseteq> PrefixSkip_RAD a \<sqinter>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
    have ha: "h (ades_obs True s_start True {done_a a s_start})"
      by (rule h(3)[unfolded pred_refine_iff, rule_format]) (simp only: rad_dchoice_eval da simp_thms)
    have hb: "h (ades_obs True s_start True {done_a b s_start})"
      by (rule h(3)[unfolded pred_refine_iff, rule_format]) (simp only: rad_dchoice_eval db simp_thms)
    from A2_below_angelic_done[OF w g]
    show "(g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> h) ?x"
    proof
      assume ga: "g (ades_obs True s_start True {done_a a s_start})"
      show ?thesis by (rule rad_sync_done_done[where g=g and h=h and e=a, OF w _ ga ha]) simp
    next
      assume gb: "g (ades_obs True s_start True {done_a b s_start})"
      show ?thesis by (rule rad_sync_done_done[where g=g and h=h and e=b, OF w _ gb hb]) simp
    qed
  qed
  have nR: "\<not> ?R ?x"
  proof -
    have Z: "\<forall>s'\<in>done_ab a b s_start. rad_tr\<^sub>v s' \<noteq> rad_tr\<^sub>v (s_start :: ('e list, 'e) rad_state)"
      by simp
    have le_a: "PrefixSkip_RAD a \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
      by (simp only: ref_by_pred_is_leq) (rule inf_le1)
    have le_b: "PrefixSkip_RAD b \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
      by (simp only: ref_by_pred_is_leq) (rule inf_le2)
    have "\<not> rad_par_F (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) jsync (PrefixSkip_RAD a) ?x"
    proof
      assume "rad_par_F (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) jsync (PrefixSkip_RAD a) ?x"
      from this[unfolded rad_par_F_eval, rule_format, OF PrefixSkip_RAD_is_RAD PrefixSkip_RAD_is_A2
          PrefixSkip_RAD_is_RAD PrefixSkip_RAD_is_A2 le_b ref_refl_pred]
      have "(PrefixSkip_RAD b \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a) ?x" .
      with rad_sync_ab_stuck[OF w ab[symmetric] Z] show False by contradiction
    qed
    moreover have "\<not> rad_par_F (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) jsync (PrefixSkip_RAD b) ?x"
    proof
      assume "rad_par_F (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) jsync (PrefixSkip_RAD b) ?x"
      from this[unfolded rad_par_F_eval, rule_format, OF PrefixSkip_RAD_is_RAD PrefixSkip_RAD_is_A2
          PrefixSkip_RAD_is_RAD PrefixSkip_RAD_is_A2 le_a ref_refl_pred]
      have "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) ?x" .
      with rad_sync_ab_stuck[OF w ab Z] show False by contradiction
    qed
    ultimately show ?thesis by (simp only: rad_dchoice_eval de_Morgan_disj; blast)
  qed
  from L have "?R ?x" by (simp only: eq)
  with nR show False by contradiction
qed

end
