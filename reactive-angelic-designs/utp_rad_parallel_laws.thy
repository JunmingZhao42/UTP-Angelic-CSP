section \<open>Reactive Angelic Design Parallel-by-Merge Laws\<close>

theory utp_rad_parallel_laws
  imports utp_rad_parallel_merge
begin

subsection \<open>Generic parallel closure\<close>

lemma RA2m_trace_prepend_obs:
  assumes "M is RA2m"
  shows "ades_merge_obs M ok0 s0 okL (image (rad_trace_prepend s0) X)
      okR (image (rad_trace_prepend s0) Y) ok' Z =
    ades_merge_obs M ok0 (rad_zero_trace s0) okL X okR Y ok'
      (rad_normalise_choices s0 Z)"
proof -
  have a: "ades_merge_obs M ok0 s0 okL (image (rad_trace_prepend s0) X)
      okR (image (rad_trace_prepend s0) Y) ok' Z =
    (rad_normalise_choices s0 Z \<noteq> {} \<and>
     ades_merge_obs M ok0 (rad_zero_trace s0)
      okL (image (rad_trace_difference s0) (image (rad_trace_prepend s0) X))
      okR (image (rad_trace_difference s0) (image (rad_trace_prepend s0) Y))
      ok' (rad_normalise_choices s0 Z))"
    by (subst (1) Healthy_if[OF assms, symmetric]; rule RA2m_obs)
  have b: "ades_merge_obs M ok0 (rad_zero_trace s0) okL X okR Y ok' (rad_normalise_choices s0 Z) =
    (rad_normalise_choices s0 Z \<noteq> {} \<and>
     ades_merge_obs M ok0 (rad_zero_trace s0) okL X okR Y ok' (rad_normalise_choices s0 Z))"
    by (subst (1) Healthy_if[OF assms, symmetric]; simp add: RA2m_obs[simplified])
  show ?thesis using a b by (simp add: image_image rad_trace_difference_prepend)
qed

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

lemma rad_par_by_merge_RA2 [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is RA1" "Q is RA1" "P is RA2" "Q is RA2"
    "M is RA2m" "M is ABm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RA2"
proof -
  let ?R = "P \<parallel>\<^bsub>M\<^esub> Q"
  show ?thesis
    unfolding Healthy_def'
  proof (rule ades_obs_ext)
    fix ok0 s0 ok' ac'
    show "RA2 ?R (ades_obs ok0 s0 ok' ac') = ?R (ades_obs ok0 s0 ok' ac')"
    proof (rule iffI)
      assume "RA2 ?R (ades_obs ok0 s0 ok' ac')"
      then obtain okL X okR Y where
        p: "P (ades_obs ok0 (rad_zero_trace s0) okL X)" and
        q: "Q (ades_obs ok0 (rad_zero_trace s0) okR Y)" and
        n: "ades_merge_obs M ok0 (rad_zero_trace s0)
          okL X okR Y ok' (rad_normalise_choices s0 ac')"
        unfolding RA2_obs' ades_par_by_merge_obs by blast
      have "P (ades_obs ok0 s0 okL (rad_trace_prepend s0 ` X))"
        "Q (ades_obs ok0 s0 okR (rad_trace_prepend s0 ` Y))"
        using p q by (simp_all only: RA2_trace_prepend_obs[OF assms(3)]
            RA2_trace_prepend_obs[OF assms(4)])
      moreover have "ades_merge_obs M ok0 s0 okL
          (rad_trace_prepend s0 ` X) okR (rad_trace_prepend s0 ` Y) ok' ac'"
        using n by (simp only: RA2m_trace_prepend_obs[OF assms(5)])
      ultimately show "?R (ades_obs ok0 s0 ok' ac')"
        unfolding ades_par_by_merge_obs by blast
    next
      assume "?R (ades_obs ok0 s0 ok' ac')"
      then obtain okL X okR Y where
        p: "P (ades_obs ok0 s0 okL X)" and
        q: "Q (ades_obs ok0 s0 okR Y)" and
        n: "ades_merge_obs M ok0 s0 okL X okR Y ok' ac'"
        unfolding ades_par_by_merge_obs by blast
      have nx: "rad_trace_extensions s0 \<inter> X \<noteq> {}"
        using assms(1) p by (metis Healthy_def' RA1_obs)
      have ny: "rad_trace_extensions s0 \<inter> Y \<noteq> {}"
        using assms(2) q by (metis Healthy_def' RA1_obs)
      have nxy: "ades_merge_obs M ok0 s0 okL
          (rad_trace_extensions s0 \<inter> X) okR
          (rad_trace_extensions s0 \<inter> Y) ok' ac'"
        by (rule ABm_restrict[OF assms(6) _ _ nx ny n]; auto)
      have p0: "P (ades_obs ok0 (rad_zero_trace s0) okL
          (rad_normalise_choices s0 X))"
        using p
        by (subst (asm) Healthy_if[OF assms(3), symmetric]; simp only: RA2_obs')
      have q0: "Q (ades_obs ok0 (rad_zero_trace s0) okR
          (rad_normalise_choices s0 Y))"
        using q
        by (subst (asm) Healthy_if[OF assms(4), symmetric]; simp only: RA2_obs')
      have normalise: "rad_trace_difference s0 ` (rad_trace_extensions s0 \<inter> W) =
          rad_normalise_choices s0 W" for W
        by (auto simp: rad_normalise_choices_def rad_trace_extensions_def)
      have n0: "ades_merge_obs M ok0 (rad_zero_trace s0)
          okL (rad_normalise_choices s0 X) okR
          (rad_normalise_choices s0 Y) ok' (rad_normalise_choices s0 ac')"
        using nxy
        by (subst (asm) Healthy_if[OF assms(5), symmetric];
            simp add: RA2m_obs[simplified] normalise)
      show "RA2 ?R (ades_obs ok0 s0 ok' ac')"
        using p0 q0 n0 by (simp only: RA2_obs' ades_par_by_merge_obs; blast)
    qed
  qed
qed

lemma rad_par_by_merge_RA [closure]:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "P is RA" "Q is RA" "M is RAm"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RA"
proof -
  have ra1: "P is RA1" "Q is RA1"
    using RA1_idem[of "RA2 (RA3 P)"] RA1_idem[of "RA2 (RA3 Q)"] assms(1,2)
    by (simp_all add: Healthy_def' RA_def)
  have "(P \<parallel>\<^bsub>M\<^esub> Q) is RA1"
    "(P \<parallel>\<^bsub>M\<^esub> Q) is RA2"
    "(P \<parallel>\<^bsub>M\<^esub> Q) is RA3"
    using assms ra1
    by (auto simp: RAm_healthy_iff intro: rad_par_by_merge_RA1
        rad_par_by_merge_RA2 rad_par_by_merge_RA3 RA_is_RA2 RA_is_RA3)
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
  by (auto intro: rad_par_by_merge_RA1 rad_par_by_merge_RA2 rad_par_by_merge_RA3
      rad_par_by_merge_CSPA1 rad_par_by_merge_CSPA2 PBMH_ades_par_by_merge)

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
