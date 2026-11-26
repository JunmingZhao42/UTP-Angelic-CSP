section \<open>Angelic Process Parallel-by-Merge Laws\<close>

theory utp_ap_parallel_laws
  imports utp_ap_parallel_merge
begin

subsection \<open>Closure\<close>

text \<open>RAD needs RA1 operands for RA2 closure. AP operands may diverge with no
  trace extension among their choices, so we use PBMH instead.\<close>

lemma ap_par_by_merge_RA2 [closure]:
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

lemma ap_par_by_merge_RA3AP [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is RA3AP" "Q is RA3AP" "M is RA3APm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RA3AP"
  unfolding Healthy_def'
  apply (subst (2) Healthy_if[OF assms(1), symmetric])
  apply (subst (2) Healthy_if[OF assms(2), symmetric])
  apply (subst (2) Healthy_if[OF assms(3), symmetric])
  apply (rule ades_obs_ext)
  subgoal for ok0 s0 ok' Z
    by (cases "rad_wait\<^sub>v s0";
        simp add: RA3AP_eval II_AP_obs ades_par_by_merge_obs RA3APm_obs[simplified];
        blast)
  done

lemma ap_par_by_merge_AP [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is AP" "Q is AP"
    and "M is H1m" "M is H2m" "M is ADm" "M is RA2APm" "M is RA3APm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is AP"
proof -
  let ?R = "P \<parallel>\<^bsub>M\<^esub> Q"
  have h1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: H_implies_H1 AP_is_H)
  have r: "?R is H2" "?R is H1" "?R is A" "?R is RA2" "?R is RA3AP"
    by (rule H2_par_by_merge[OF assms(4)],
        rule H1_par_by_merge[OF h1 assms(3)],
        rule A_par_by_merge[OF h1 assms(5)],
        rule ap_par_by_merge_RA2[OF AP_is_RA2[OF assms(1)] AP_is_RA2[OF assms(2)]
          AP_is_PBMH_ades[OF assms(1)] AP_is_PBMH_ades[OF assms(2)] assms(6)],
        rule ap_par_by_merge_RA3AP[OF AP_is_RA3AP[OF assms(1)] AP_is_RA3AP[OF assms(2)] assms(7)])
  show ?thesis
    by (simp only: Healthy_def' AP_def CSPA2_def comp_apply Healthy_if[OF r(1)]
        Healthy_if[OF r(2)] Healthy_if[OF r(3)] Healthy_if[OF r(4)] Healthy_if[OF r(5)])
qed

end
