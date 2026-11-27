section \<open>Angelic Process Parallel-by-Merge Laws\<close>

theory utp_ap_parallel_laws
  imports utp_ap_parallel_merge "UTP-Reactive-Angelic-Designs.utp_rad_parallel_laws"
begin

subsection \<open>Closure\<close>

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
        rule rad_par_by_merge_RA2[OF AP_is_RA2[OF assms(1)] AP_is_RA2[OF assms(2)]
          AP_is_PBMH_ades[OF assms(1)] AP_is_PBMH_ades[OF assms(2)] assms(6)],
        rule ap_par_by_merge_RA3AP[OF AP_is_RA3AP[OF assms(1)] AP_is_RA3AP[OF assms(2)] assms(7)])
  show ?thesis
    by (simp only: Healthy_def' AP_def CSPA2_def comp_apply Healthy_if[OF r(1)]
        Healthy_if[OF r(2)] Healthy_if[OF r(3)] Healthy_if[OF r(4)] Healthy_if[OF r(5)])
qed

end
