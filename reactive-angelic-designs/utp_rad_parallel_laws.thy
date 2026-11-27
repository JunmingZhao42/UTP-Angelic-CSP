section \<open>Reactive Angelic Design Parallel-by-Merge Laws\<close>

theory utp_rad_parallel_laws
  imports utp_rad_parallel_merge
begin

subsection \<open>Generic parallel closure\<close>

lemma rad_par_by_merge_RA1 [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "M is RA1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RA1"
  unfolding Healthy_def'
  by (subst (2) Healthy_if[OF assms, symmetric];
      rule ades_obs_ext; simp only: RA1_obs ades_par_by_merge_obs RA1m_obs; blast)

lemma rad_par_by_merge_CSPA1 [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is CSPA1" "Q is CSPA1" "M is CSPA1m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is CSPA1"
proof -
  have branches: "P (ades_obs ok0 s0 False {s0})" "Q (ades_obs ok0 s0 False {s0})"
    if "\<not> ok0" for ok0 s0
    using that assms(1,2)
    by (metis CSPA1_obs Healthy_if rad_trace_extensions_refl IntI singletonI empty_iff)+
  show ?thesis
    unfolding Healthy_def'
    apply (subst (2) Healthy_if[OF assms(3), symmetric])
    apply (rule ades_obs_ext)
    apply (simp only: CSPA1_obs ades_par_by_merge_obs CSPA1m_obs)
    using branches by blast
qed

lemma rad_par_by_merge_RA3 [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is RA3" "Q is RA3" "M is RA3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RA3"
  unfolding Healthy_def'
  apply (subst (2) Healthy_if[OF assms(1), symmetric])
  apply (subst (2) Healthy_if[OF assms(2), symmetric])
  apply (subst (2) Healthy_if[OF assms(3), symmetric])
  apply (rule ades_obs_ext)
  subgoal for ok0 s0 ok' ac'
    by (cases "rad_wait\<^sub>v s0";
        simp add: RA3_eval ades_par_by_merge_obs RA3m_obs[simplified] II_Rac_eval; fast)
  done

text \<open>We need PBMH operands for RA2 closure. A branch observation then survives trace
  normalisation with every choice kept, not just the trace extensions, so the merge
  needs only RA2APm. RAD operands are PBMH, and so are AP operands, which may diverge
  with no trace extension among their choices.\<close>

lemma rad_par_by_merge_RA2 [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is RA2" "Q is RA2" "P is PBMH_ades" "Q is PBMH_ades" "M is RA2APm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RA2"
proof -
  let ?R = "P \<parallel>\<^bsub>M\<^esub> Q"
  have m: "ades_merge_obs M ok0 s0 okL X okR Y ok' Z =
      ades_merge_obs M ok0 (rad_zero_trace s0)
        okL (rad_trace_difference s0 ` X) okR (rad_trace_difference s0 ` Y)
        ok' (rad_normalise_choices s0 Z)" for ok0 s0 okL X okR Y ok' Z
    by (subst (1) Healthy_if[OF assms(5), symmetric]; simp only: RA2APm_obs)
  have prepend: "ades_merge_obs M ok0 s0 okL (rad_trace_prepend s0 ` X)
      okR (rad_trace_prepend s0 ` Y) ok' Z =
    ades_merge_obs M ok0 (rad_zero_trace s0) okL X okR Y ok' (rad_normalise_choices s0 Z)"
    for ok0 s0 okL X okR Y ok' Z
    by (subst (1) Healthy_if[OF assms(5), symmetric];
        simp only: RA2APm_obs image_image rad_trace_difference_prepend image_ident)
  (* PBMH keeps a branch observation when we add back the non-extensions *)
  have down: "S (ades_obs b (rad_zero_trace s1) c (rad_trace_difference s1 ` V))"
    if "S is RA2" "S is PBMH_ades" "S (ades_obs b s1 c V)"
    for S :: "('t, 'e) reactive_angelic_design" and b s1 c V
  proof -
    have "S (ades_obs b (rad_zero_trace s1) c (rad_normalise_choices s1 V))"
      using that(3) by (subst (asm) Healthy_if[OF that(1), symmetric]; simp only: RA2_obs')
    moreover have "rad_normalise_choices s1 V \<subseteq> rad_trace_difference s1 ` V"
      by (auto simp: rad_normalise_choices_def)
    ultimately show ?thesis
      by (subst Healthy_if[OF that(2), symmetric]; simp only: PBMH_ades_obs; blast)
  qed
  show ?thesis
    unfolding Healthy_def'
  proof (rule ades_obs_ext)
    fix ok0 s0 ok' Z
    show "RA2 ?R (ades_obs ok0 s0 ok' Z) = ?R (ades_obs ok0 s0 ok' Z)"
    proof
      assume "RA2 ?R (ades_obs ok0 s0 ok' Z)"
      then obtain okL X okR Y where
        p: "P (ades_obs ok0 (rad_zero_trace s0) okL X)" and
        q: "Q (ades_obs ok0 (rad_zero_trace s0) okR Y)" and
        n: "ades_merge_obs M ok0 (rad_zero_trace s0) okL X okR Y ok'
              (rad_normalise_choices s0 Z)"
        unfolding RA2_obs' ades_par_by_merge_obs by blast
      have "P (ades_obs ok0 s0 okL (rad_trace_prepend s0 ` X))"
        "Q (ades_obs ok0 s0 okR (rad_trace_prepend s0 ` Y))"
        using p q by (simp_all only: RA2_trace_prepend_obs[OF assms(1)]
            RA2_trace_prepend_obs[OF assms(2)])
      moreover have "ades_merge_obs M ok0 s0 okL (rad_trace_prepend s0 ` X)
          okR (rad_trace_prepend s0 ` Y) ok' Z"
        using n by (simp only: prepend)
      ultimately show "?R (ades_obs ok0 s0 ok' Z)"
        unfolding ades_par_by_merge_obs by blast
    next
      assume "?R (ades_obs ok0 s0 ok' Z)"
      then obtain okL X okR Y where
        p: "P (ades_obs ok0 s0 okL X)" and q: "Q (ades_obs ok0 s0 okR Y)" and
        n: "ades_merge_obs M ok0 s0 okL X okR Y ok' Z"
        unfolding ades_par_by_merge_obs by blast
      have "P (ades_obs ok0 (rad_zero_trace s0) okL (rad_trace_difference s0 ` X))"
        by (rule down[OF assms(1,3) p])
      moreover have "Q (ades_obs ok0 (rad_zero_trace s0) okR (rad_trace_difference s0 ` Y))"
        by (rule down[OF assms(2,4) q])
      moreover have "ades_merge_obs M ok0 (rad_zero_trace s0)
          okL (rad_trace_difference s0 ` X) okR (rad_trace_difference s0 ` Y)
          ok' (rad_normalise_choices s0 Z)"
        using n by (simp only: m[of okL X okR Y ok0 s0 ok' Z])
      ultimately show "RA2 ?R (ades_obs ok0 s0 ok' Z)"
        unfolding RA2_obs' ades_par_by_merge_obs by blast
    qed
  qed
qed

lemma rad_par_by_merge_RA [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is RA" "Q is RA" "P is PBMH_ades" "Q is PBMH_ades" "M is RAm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RA"
proof -
  have m: "M is RA1m" "M is RA2m" "M is RA3m"
    using assms(5) by (simp_all add: RAm_healthy_iff)
  have "(P \<parallel>\<^bsub>M\<^esub> Q) is RA1"
    "(P \<parallel>\<^bsub>M\<^esub> Q) is RA2"
    "(P \<parallel>\<^bsub>M\<^esub> Q) is RA3"
    by (rule rad_par_by_merge_RA1[OF m(1)],
        rule rad_par_by_merge_RA2[OF RA_is_RA2[OF assms(1)] RA_is_RA2[OF assms(2)]
          assms(3,4) RA2m_is_RA2APm[OF m(2)]],
        rule rad_par_by_merge_RA3[OF RA_is_RA3[OF assms(1)] RA_is_RA3[OF assms(2)] m(3)])
  then show ?thesis by (simp add: Healthy_def' RA_def)
qed

lemma rad_par_by_merge_CSPA2 [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "M is CSPA2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is CSPA2"
  using H2_par_by_merge[OF assms]
  by (simp add: Healthy_def' CSPA2_def)

lemma rad_par_by_merge_RAD [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is RAD" "Q is RAD" "M is RADm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RAD"
  using assms
  unfolding RAD_components_iff RADm_healthy_iff
  by (auto intro: rad_par_by_merge_RA1 rad_par_by_merge_RA2 RA2m_is_RA2APm
      rad_par_by_merge_RA3 rad_par_by_merge_CSPA1 rad_par_by_merge_CSPA2
      PBMH_ades_par_by_merge)

subsection \<open>Choice\<close>

text \<open>We use the UTP choice laws because RAD choices are disjunction and
  conjunction. Demonic choice therefore distributes without premises:
  P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R).\<close>

(* P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R) *)
lemma rad_par_by_merge_demonic_distl:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  shows "P \<parallel>\<^bsub>M\<^esub> (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) = (P \<parallel>\<^bsub>M\<^esub> Q) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (P \<parallel>\<^bsub>M\<^esub> R)"
  by (simp only: angelic_design_demonic par_by_merge_disj_distl)

(* (P \<sqinter> Q) \<parallel> R = (P \<parallel> R) \<sqinter> (Q \<parallel> R) *)
lemma rad_par_by_merge_demonic_distr:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  shows "(P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) \<parallel>\<^bsub>M\<^esub> R = (P \<parallel>\<^bsub>M\<^esub> R) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^bsub>M\<^esub> R)"
  by (simp only: angelic_design_demonic par_by_merge_disj_distr)

(* (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R) *)
lemma rad_par_by_merge_angelic_subdistl:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P \<parallel>\<^bsub>M\<^esub> R) \<sqsubseteq> P \<parallel>\<^bsub>M\<^esub> (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R)"
  by (simp only: angelic_design_angelic par_by_merge_conj_subdistl)

(* (P \<parallel> R) \<squnion> (Q \<parallel> R) \<sqsubseteq> (P \<squnion> Q) \<parallel> R *)
lemma rad_par_by_merge_angelic_subdistr:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design" and M :: "('t, 'e) rad_merge_rel"
  shows "(P \<parallel>\<^bsub>M\<^esub> R) \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^bsub>M\<^esub> R) \<sqsubseteq> (P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q) \<parallel>\<^bsub>M\<^esub> R"
  by (simp only: angelic_design_angelic par_by_merge_conj_subdistr)

end
