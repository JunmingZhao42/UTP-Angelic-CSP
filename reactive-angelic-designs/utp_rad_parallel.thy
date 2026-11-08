section \<open>Reactive angelic design parallel by merge\<close>

theory utp_rad_parallel
  imports utp_rad_csp "UTP-Angelic-Designs.utp_ades_parallel"
    "UTP-Reactive-Designs.utp_rdes_parallel_lift"
begin

(* The ordinary parallel import restores this notation; retain the RAD meaning. *)
no_notation wait_f ("_\<^sub>f" [1000] 1000)

type_synonym ('t, 'e) rad_merge_rel =
  "(('t, 'e) rad_state) ades_merge_rel"

subsection \<open>Generic RAD merge healthiness\<close>

text \<open>The RAD fixed point separates into reactive, divergence, design, and
  upward choice-set conditions. The merge conditions below preserve each one.\<close>

subsubsection \<open>Merge healthiness transformers\<close>

(* Restrict final choices to trace extensions of the prior observation. *)
definition RA1m :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RA1m M \<equiv> (\<lambda>(m,z).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        Z = rad_trace_extensions s0 \<inter> achoices.ac\<^sub>v (des_vars.more z)
    in Z \<noteq> {} \<and> M (m, ades_output (des_vars.ok\<^sub>v z) Z))"

(* Remove the common history from the prior, both branches, and final choices. *)
definition RA2m :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RA2m M \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; p = mrg_left\<^sub>v m; q = mrg_right\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x)
    in rad_normalise_choices s0 (achoices.ac\<^sub>v (des_vars.more z)) \<noteq> {} \<and>
       ades_merge_obs M (des_vars.ok\<^sub>v x) (rad_zero_trace s0)
         (des_vars.ok\<^sub>v p) (image (rad_trace_difference s0) (achoices.ac\<^sub>v (des_vars.more p)))
         (des_vars.ok\<^sub>v q) (image (rad_trace_difference s0) (achoices.ac\<^sub>v (des_vars.more q)))
         (des_vars.ok\<^sub>v z) (rad_normalise_choices s0 (achoices.ac\<^sub>v (des_vars.more z))))"

(* While waiting, nonempty branches merge as reactive angelic skip. *)
definition RA3m :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RA3m M \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; s0 = astate.s\<^sub>v (des_vars.more x);
        X = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        Y = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m))
    in if rad_wait\<^sub>v s0 then X \<noteq> {} \<and> Y \<noteq> {} \<and> II_Rac (x,z)
       else M (m,z))"

(* Before start, nonempty branches admit every trace-feasible final set. *)
definition CSPA1m :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "CSPA1m M \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; s0 = astate.s\<^sub>v (des_vars.more x);
        X = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        Y = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        Z = achoices.ac\<^sub>v (des_vars.more z)
    in M (m,z) \<or> (\<not> des_vars.ok\<^sub>v x \<and> X \<noteq> {} \<and> Y \<noteq> {} \<and>
      rad_trace_extensions s0 \<inter> Z \<noteq> {}))"

(* CSPA2 uses the design merge condition for output termination. *)
abbreviation CSPA2m :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "CSPA2m \<equiv> H2m"

(* m = ((ok,s),(okL,acL),(okR,acR)), E_s = {s'. s.tr \<le> s'.tr}.
   RA1m M(m,(ok',ac')) = E_s \<inter> ac' \<noteq> {} \<and> M(m,(ok',E_s \<inter> ac')). *)
lemma RA1m_obs:
  "ades_merge_obs (RA1m M) ok0 s0 okL X okR Y ok' Z =
    (rad_trace_extensions s0 \<inter> Z \<noteq> {} \<and>
     ades_merge_obs M ok0 s0 okL X okR Y ok' (rad_trace_extensions s0 \<inter> Z))"
  by (simp add: RA1m_def Let_def)

(* \<delta>_s(u) = u[tr := u.tr - s.tr], N_s(ac') = \<delta>_s ` (E_s \<inter> ac').
   RA2m M((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
     N_s(ac') \<noteq> {} \<and>
     M((ok,s[tr := 0]),(okL,\<delta>_s ` acL),(okR,\<delta>_s ` acR),(ok',N_s(ac'))). *)
lemma RA2m_obs:
  "ades_merge_obs (RA2m M) ok0 s0 okL X okR Y ok' Z =
    (rad_normalise_choices s0 Z \<noteq> {} \<and>
     ades_merge_obs M ok0 (rad_zero_trace s0)
      okL (image (rad_trace_difference s0) X) okR (image (rad_trace_difference s0) Y)
      ok' (rad_normalise_choices s0 Z))"
  by (simp add: RA2m_def Let_def)

(* RA3m M(m,(ok',ac')) =
     (acL \<noteq> {} \<and> acR \<noteq> {} \<and> II_Rac((ok,s),(ok',ac'))) \<triangleleft> s.wait \<triangleright> M(m,(ok',ac')). *)
lemma RA3m_obs:
  "ades_merge_obs (RA3m M) ok0 s0 okL X okR Y ok' Z =
    (if rad_wait\<^sub>v s0 then X \<noteq> {} \<and> Y \<noteq> {} \<and> II_Rac (ades_obs ok0 s0 ok' Z)
     else ades_merge_obs M ok0 s0 okL X okR Y ok' Z)"
  by (simp add: RA3m_def Let_def)

(* CSPA1m M(m,(ok',ac')) = M(m,(ok',ac')) \<or>
     (\<not>ok \<and> acL \<noteq> {} \<and> acR \<noteq> {} \<and> E_s \<inter> ac' \<noteq> {}). *)
lemma CSPA1m_obs:
  "ades_merge_obs (CSPA1m M) ok0 s0 okL X okR Y ok' Z =
    (ades_merge_obs M ok0 s0 okL X okR Y ok' Z \<or>
     (\<not> ok0 \<and> X \<noteq> {} \<and> Y \<noteq> {} \<and> rad_trace_extensions s0 \<inter> Z \<noteq> {}))"
  by (simp add: CSPA1m_def Let_def)

subsubsection \<open>Idempotence and monotonicity\<close>

lemma RA1m_idem: "RA1m (RA1m M) = RA1m M"
  by (rule ades_merge_ext; simp add: RA1m_obs[simplified])

lemma RA2m_idem: "RA2m (RA2m M) = RA2m M"
  by (rule ades_merge_ext; simp add: RA2m_obs[simplified])

lemma RA3m_idem: "RA3m (RA3m M) = RA3m M"
  by (rule ades_merge_ext; simp add: RA3m_obs[simplified])

lemma CSPA1m_idem: "CSPA1m (CSPA1m M) = CSPA1m M"
  by (rule ades_merge_ext; simp add: CSPA1m_obs[simplified])

lemma RA1m_Idempotent [closure]: "Idempotent RA1m"
  by (simp add: Idempotent_def RA1m_idem)

lemma RA1m_Monotonic [closure]: "Monotonic RA1m"
  by (rule MonotonicI; auto simp: pred_refine_iff RA1m_def Let_def split: prod.splits if_splits; blast)

lemma RA2m_Idempotent [closure]: "Idempotent RA2m"
  by (simp add: Idempotent_def RA2m_idem)

lemma RA2m_Monotonic [closure]: "Monotonic RA2m"
  by (rule MonotonicI; auto simp: pred_refine_iff RA2m_def Let_def split: prod.splits if_splits; blast)

lemma RA3m_Idempotent [closure]: "Idempotent RA3m"
  by (simp add: Idempotent_def RA3m_idem)

lemma RA3m_Monotonic [closure]: "Monotonic RA3m"
  by (rule MonotonicI; auto simp: pred_refine_iff RA3m_def Let_def split: prod.splits if_splits; blast)

lemma CSPA1m_Idempotent [closure]: "Idempotent CSPA1m"
  by (simp add: Idempotent_def CSPA1m_idem)

lemma CSPA1m_Monotonic [closure]: "Monotonic CSPA1m"
  by (rule MonotonicI; auto simp: pred_refine_iff CSPA1m_def Let_def split: prod.splits if_splits; blast)

subsubsection \<open>Commutation\<close>

lemma RA1m_RA2m_absorb:
  "RA1m (RA2m M) = RA2m M"
  "RA2m (RA1m M) = RA2m M"
  by (rule ades_merge_ext;
      simp add: RA1m_obs[simplified] RA2m_obs[simplified]
        rad_normalise_choices_extensions rad_normalise_choices_nonempty
        rad_zero_trace_extensions)+

lemma RA1m_RA2m_commute: "RA1m (RA2m M) = RA2m (RA1m M)"
  by (simp only: RA1m_RA2m_absorb)

lemma RA1m_RA3m_commute: "RA1m (RA3m M) = RA3m (RA1m M)"
  by (rule ades_merge_ext; auto simp: RA1m_obs[simplified] RA3m_obs[simplified] II_Rac_eval rad_trace_extensions_def; blast)

lemma RA1m_CSPA1m_commute: "RA1m (CSPA1m M) = CSPA1m (RA1m M)"
  by (rule ades_merge_ext; auto simp: RA1m_obs[simplified] CSPA1m_obs[simplified] ; blast)

lemma RA1m_RABm_commute: "RA1m (RABm M) = RABm (RA1m M)"
  by (rule ades_merge_ext; auto simp: RA1m_obs[simplified] RABm_obs[simplified] ; blast)

lemma RA1m_CSPA2m_commute: "RA1m (CSPA2m M) = CSPA2m (RA1m M)"
  by (rule ades_merge_ext; auto simp: RA1m_obs[simplified] H2m_ades_obs[simplified] ; blast)

lemma RA2m_RA3m_commute: "RA2m (RA3m M) = RA3m (RA2m M)"
  by (rule ades_merge_ext;
      auto simp: RA2m_obs[simplified] RA3m_obs[simplified] II_Rac_eval
        rad_zero_trace_extensions rad_normalise_choices_nonempty rad_zero_trace_in_normalise;
      blast intro: rad_trace_extensions_refl)

lemma RA2m_CSPA1m_commute: "RA2m (CSPA1m M) = CSPA1m (RA2m M)"
  by (rule ades_merge_ext; auto simp: RA2m_obs[simplified] CSPA1m_obs[simplified] rad_normalise_choices_nonempty rad_zero_trace_extensions; blast)

lemma RA2m_CSPA2m_commute: "RA2m (CSPA2m M) = CSPA2m (RA2m M)"
  by (rule ades_merge_ext; auto simp: RA2m_obs[simplified] H2m_ades_obs[simplified] ; blast)

lemma RA3m_CSPA1m_commute: "RA3m (CSPA1m M) = CSPA1m (RA3m M)"
  by (rule ades_merge_ext; auto simp: RA3m_obs[simplified] CSPA1m_obs[simplified] II_Rac_eval; blast)

lemma RA3m_PBMHm_commute: "RA3m (PBMHm M) = PBMHm (RA3m M)"
  by (rule ades_merge_ext; auto simp: RA3m_obs[simplified] PBMHm_obs[simplified] II_Rac_eval; blast)

lemma RA3m_RABm_commute: "RA3m (RABm M) = RABm (RA3m M)"
  by (rule ades_merge_ext; auto simp: RA3m_obs[simplified] RABm_obs[simplified] ; blast)

lemma RA3m_CSPA2m_commute: "RA3m (CSPA2m M) = CSPA2m (RA3m M)"
  by (rule ades_merge_ext; auto simp: RA3m_obs[simplified] H2m_ades_obs[simplified] II_Rac_eval; blast)

lemma CSPA1m_PBMHm_commute: "CSPA1m (PBMHm M) = PBMHm (CSPA1m M)"
  by (rule ades_merge_ext; auto simp: CSPA1m_obs[simplified] PBMHm_obs[simplified] ; blast)

lemma CSPA1m_RABm_commute: "CSPA1m (RABm M) = RABm (CSPA1m M)"
  by (rule ades_merge_ext; auto simp: CSPA1m_obs[simplified] RABm_obs[simplified] ; blast)

lemma CSPA1m_CSPA2m_commute: "CSPA1m (CSPA2m M) = CSPA2m (CSPA1m M)"
  by (rule ades_merge_ext; auto simp: CSPA1m_obs[simplified] H2m_ades_obs[simplified] ; blast)

lemma RA1m_PBMHm_commute:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  shows "RA1m (PBMHm M) = PBMHm (RA1m M)"
proof (rule ades_merge_ext)
  fix ok0 okL X okR Y ok' Z and s0 :: "('t, 'e) rad_state"
  let ?E = "rad_trace_extensions s0"
  let ?F = "\<lambda>W. ades_merge_obs M ok0 s0 okL X okR Y ok' W"
  have "(?E \<inter> Z \<noteq> {} \<and> (\<exists>W \<subseteq> ?E \<inter> Z. W \<noteq> {} \<and> ?F W)) =
    (\<exists>W \<subseteq> Z. W \<noteq> {} \<and> ?E \<inter> W \<noteq> {} \<and> ?F (?E \<inter> W))"
  proof
    assume "?E \<inter> Z \<noteq> {} \<and> (\<exists>W \<subseteq> ?E \<inter> Z. W \<noteq> {} \<and> ?F W)"
    then obtain W where w: "W \<subseteq> ?E \<inter> Z" "W \<noteq> {}" "?F W" by blast
    have "?E \<inter> W = W" using w(1) by blast
    then show "\<exists>W \<subseteq> Z. W \<noteq> {} \<and> ?E \<inter> W \<noteq> {} \<and> ?F (?E \<inter> W)"
      using w by (intro exI[where x=W]; auto)
  next
    assume "\<exists>W \<subseteq> Z. W \<noteq> {} \<and> ?E \<inter> W \<noteq> {} \<and> ?F (?E \<inter> W)"
    then obtain W where w: "W \<subseteq> Z" "?E \<inter> W \<noteq> {}" "?F (?E \<inter> W)" by blast
    then show "?E \<inter> Z \<noteq> {} \<and> (\<exists>W \<subseteq> ?E \<inter> Z. W \<noteq> {} \<and> ?F W)"
      by (intro conjI exI[where x="?E \<inter> W"]; blast)
  qed
  then show "ades_merge_obs (RA1m (PBMHm M)) ok0 s0 okL X okR Y ok' Z =
    ades_merge_obs (PBMHm (RA1m M)) ok0 s0 okL X okR Y ok' Z"
    by (simp only: RA1m_obs PBMHm_obs)
qed

lemma RA2m_PBMHm_commute:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  shows "RA2m (PBMHm M) = PBMHm (RA2m M)"
proof (rule ades_merge_ext)
  fix ok0 okL X okR Y ok' Z and s0 :: "('t, 'e) rad_state"
  let ?N = "rad_normalise_choices s0"
  let ?F = "\<lambda>W. ades_merge_obs M ok0 (rad_zero_trace s0)
    okL (rad_trace_difference s0 ` X) okR (rad_trace_difference s0 ` Y) ok' W"
  have eq: "(?N Z \<noteq> {} \<and> (\<exists>W \<subseteq> ?N Z. W \<noteq> {} \<and> ?F W)) =
      (\<exists>W \<subseteq> Z. W \<noteq> {} \<and> ?N W \<noteq> {} \<and> ?F (?N W))"
  proof
    assume "?N Z \<noteq> {} \<and> (\<exists>W \<subseteq> ?N Z. W \<noteq> {} \<and> ?F W)"
    then obtain W where w: "W \<subseteq> ?N Z" "W \<noteq> {}" "?F W" by blast
    have "rad_trace_prepend s0 ` W \<subseteq> Z"
      using w(1) by (auto simp: rad_normalise_choices_as_prepend)
    then show "\<exists>W \<subseteq> Z. W \<noteq> {} \<and> ?N W \<noteq> {} \<and> ?F (?N W)"
      using w(2,3)
      by (intro exI[where x="rad_trace_prepend s0 ` W"]; simp add: rad_normalise_choices_prepend)
  next
    assume "\<exists>W \<subseteq> Z. W \<noteq> {} \<and> ?N W \<noteq> {} \<and> ?F (?N W)"
    then obtain W where w: "W \<subseteq> Z" "?N W \<noteq> {}" "?F (?N W)" by blast
    have "?N W \<subseteq> ?N Z"
      by (rule rad_normalise_choices_mono[OF w(1)])
    then show "?N Z \<noteq> {} \<and> (\<exists>W \<subseteq> ?N Z. W \<noteq> {} \<and> ?F W)"
      using w(2,3) by blast
  qed
  show "ades_merge_obs (RA2m (PBMHm M)) ok0 s0 okL X okR Y ok' Z =
    ades_merge_obs (PBMHm (RA2m M)) ok0 s0 okL X okR Y ok' Z"
    by (simp only: RA2m_obs PBMHm_obs eq)
qed

lemma RA2m_RABm_commute:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  shows "RA2m (RABm M) = RABm (RA2m M)"
proof (rule ades_merge_ext)
  fix ok0 okL X okR Y ok' Z and s0 :: "('t, 'e) rad_state"
  let ?f = "rad_trace_difference s0"
  let ?F = "\<lambda>U V. ades_merge_obs M ok0 (rad_zero_trace s0)
    okL U okR V ok' (rad_normalise_choices s0 Z)"
  have surj: "surj ?f"
    using rad_trace_difference_prepend[of s0] unfolding surj_def by metis
  have eq: "(\<exists>U V. image ?f X \<subseteq> U \<and> image ?f Y \<subseteq> V \<and> ?F U V) =
    (\<exists>U V. X \<subseteq> U \<and> Y \<subseteq> V \<and> ?F (image ?f U) (image ?f V))"
  proof
    assume "\<exists>U V. image ?f X \<subseteq> U \<and> image ?f Y \<subseteq> V \<and> ?F U V"
    then obtain U V where w: "image ?f X \<subseteq> U" "image ?f Y \<subseteq> V" "?F U V" by blast
    show "\<exists>U V. X \<subseteq> U \<and> Y \<subseteq> V \<and> ?F (image ?f U) (image ?f V)"
      apply (rule exI[where x="vimage ?f U"])
      apply (rule exI[where x="vimage ?f V"])
      using w by (simp add: image_subset_iff_subset_vimage surj)
  next
    assume "\<exists>U V. X \<subseteq> U \<and> Y \<subseteq> V \<and> ?F (image ?f U) (image ?f V)"
    then obtain U V where w: "X \<subseteq> U" "Y \<subseteq> V" "?F (image ?f U) (image ?f V)" by blast
    show "\<exists>U V. image ?f X \<subseteq> U \<and> image ?f Y \<subseteq> V \<and> ?F U V"
      apply (rule exI[where x="image ?f U"])
      apply (rule exI[where x="image ?f V"])
      using w by (auto intro: image_mono)
  qed
  show "ades_merge_obs (RA2m (RABm M)) ok0 s0 okL X okR Y ok' Z =
    ades_merge_obs (RABm (RA2m M)) ok0 s0 okL X okR Y ok' Z"
    by (cases "rad_normalise_choices s0 Z = {}";
        simp add: RA2m_obs[simplified] RABm_obs[simplified] eq[simplified])
qed

subsubsection \<open>Combined merge healthiness\<close>

(* RAm combines trace normalisation, waiting, and branch choice-set closure. *)
definition RAm :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RAm \<equiv> RA2m \<circ> RA3m \<circ> RABm"

lemma RAm_healths [closure]:
  "RAm M is RA1m"
  "RAm M is RA2m"
  "RAm M is RA3m"
  "RAm M is RABm"
  by (simp_all add: Healthy_def' RAm_def RA1m_RA2m_absorb
      RA2m_RA3m_commute[symmetric] RA2m_RABm_commute[symmetric]
      RA3m_RABm_commute[symmetric] RA2m_idem RA3m_idem RABm_idem)

lemma RAm_healthy_iff:
  "(M is RAm) \<longleftrightarrow> ((M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is RABm))"
proof
  assume "M is RAm"
  then show "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is RABm)"
    using RAm_healths[of M] by (simp only: Healthy_if)
next
  assume "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is RABm)"
  then show "M is RAm" by (simp add: Healthy_def' RAm_def)
qed

lemma RAm_Idempotent [closure]: "Idempotent RAm"
  by (simp add: Idempotent_def Healthy_def'[symmetric] RAm_healthy_iff RAm_healths)

lemma RAm_Monotonic [closure]: "Monotonic RAm"
  unfolding RAm_def
  by (intro Monotonic_comp RA2m_Monotonic RA3m_Monotonic RABm_Monotonic)

(* RADm combines the commuting reactive, design, and choice-set conditions. *)
definition RADm :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RADm \<equiv> RA2m \<circ> RA3m \<circ> CSPA1m \<circ> PBMHm \<circ> RABm \<circ> CSPA2m"

lemmas RADm_comms =
  RA1m_RA2m_commute[symmetric]
  RA1m_RA3m_commute[symmetric]
  RA1m_CSPA1m_commute[symmetric]
  RA1m_PBMHm_commute[symmetric]
  RA1m_RABm_commute[symmetric]
  RA1m_CSPA2m_commute[symmetric]
  RA2m_RA3m_commute[symmetric]
  RA2m_CSPA1m_commute[symmetric]
  RA2m_PBMHm_commute[symmetric]
  RA2m_RABm_commute[symmetric]
  RA2m_CSPA2m_commute[symmetric]
  RA3m_CSPA1m_commute[symmetric]
  RA3m_PBMHm_commute[symmetric]
  RA3m_RABm_commute[symmetric]
  RA3m_CSPA2m_commute[symmetric]
  CSPA1m_PBMHm_commute[symmetric]
  CSPA1m_RABm_commute[symmetric]
  CSPA1m_CSPA2m_commute[symmetric]
  PBMHm_RABm_commute[symmetric]
  PBMHm_H2m_commute[symmetric]
  RABm_H2m_commute[symmetric]

lemma RADm_healths [closure]:
  "RADm M is RA1m"
  "RADm M is RA2m"
  "RADm M is RA3m"
  "RADm M is CSPA1m"
  "RADm M is PBMHm"
  "RADm M is RABm"
  "RADm M is CSPA2m"
  by (simp_all add: Healthy_def' RADm_def RADm_comms
      RA1m_RA2m_absorb RA2m_idem RA3m_idem CSPA1m_idem PBMHm_idem RABm_idem H2m_idem)

lemma RADm_healthy_iff:
  "(M is RADm) \<longleftrightarrow> ((M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is CSPA1m) \<and> (M is PBMHm) \<and> (M is RABm) \<and> (M is CSPA2m))"
proof
  assume "M is RADm"
  then show "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is CSPA1m) \<and> (M is PBMHm) \<and> (M is RABm) \<and> (M is CSPA2m)"
    using RADm_healths[of M] by (simp only: Healthy_if)
next
  assume "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is CSPA1m) \<and> (M is PBMHm) \<and> (M is RABm) \<and> (M is CSPA2m)"
  then show "M is RADm" by (simp add: Healthy_def' RADm_def)
qed

lemma RADm_Idempotent [closure]: "Idempotent RADm"
  by (simp add: Idempotent_def Healthy_def'[symmetric] RADm_healthy_iff RADm_healths)

lemma RADm_Monotonic [closure]: "Monotonic RADm"
  unfolding RADm_def
  by (intro Monotonic_comp RA2m_Monotonic RA3m_Monotonic CSPA1m_Monotonic PBMHm_Monotonic RABm_Monotonic H2m_Monotonic)

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
    "M is RA2m" "M is RABm"
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
        by (rule RABm_restrict[OF assms(6) _ _ nx ny n]; auto)
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

subsection \<open>Basic RAD merge\<close>

(* Waiting uses II_Rac; unstarted observations admit trace extensions.
   Active observations synchronise trace contributions and disjoin waiting flags; refusals are unrestricted. *)
definition rad_basic_merge :: "('t::trace, 'e) rad_merge_rel" where
  "rad_basic_merge \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; p = mrg_left\<^sub>v m; q = mrg_right\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x);
        acL = achoices.ac\<^sub>v (des_vars.more p);
        acR = achoices.ac\<^sub>v (des_vars.more q);
        ac' = achoices.ac\<^sub>v (des_vars.more z)
    in acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (if rad_wait\<^sub>v s0 then II_Rac (x,z)
       else if \<not> des_vars.ok\<^sub>v x then rad_trace_extensions s0 \<inter> ac' \<noteq> {}
       else ((des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<longrightarrow> des_vars.ok\<^sub>v z) \<and>
         (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
           rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
           rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR))))"

lemma rad_basic_merge_obs:
  "ades_merge_obs rad_basic_merge ok0 s0 okL acL okR acR ok' ac' =
    (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (if rad_wait\<^sub>v s0 then II_Rac (ades_obs ok0 s0 ok' ac')
       else if \<not> ok0 then rad_trace_extensions s0 \<inter> ac' \<noteq> {}
       else ((okL \<and> okR) \<longrightarrow> ok') \<and>
         (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
           rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
           rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
           rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR))))"
  by (simp add: rad_basic_merge_def Let_def)

lemma rad_basic_merge_RA1m [closure]: "rad_basic_merge is RA1m"
  unfolding Healthy_def'
  by (rule ades_merge_ext;
      auto simp: RA1m_obs[simplified] rad_basic_merge_obs[simplified]
        II_Rac_eval rad_trace_extensions_def; blast)

lemma rad_basic_merge_RA2m [closure]:
  "(rad_basic_merge :: ('t::trace, 'e) rad_merge_rel) is RA2m"
proof -
  have normalise:
    "(\<exists>s'\<in>rad_normalise_choices s0 ac'.
       rad_tr\<^sub>v s' = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
       rad_tr\<^sub>v s' = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
       rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR)) =
     (\<exists>s'\<in>ac'.
       rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
       rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sL - rad_tr\<^sub>v s0 \<and>
       rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v sR - rad_tr\<^sub>v s0 \<and>
       rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR))"
    for s0 sL sR :: "('t::trace, 'e) rad_state" and ac'
    by (auto simp: rad_normalise_choices_def rad_trace_difference_def)
  show ?thesis
    unfolding Healthy_def'
    apply (rule ades_merge_ext)
    apply (simp add: RA2m_obs[simplified] rad_basic_merge_obs[simplified]
        II_Rac_eval rad_zero_trace_extensions rad_zero_trace_in_normalise
        rad_normalise_choices_nonempty)
    apply (simp add: rad_zero_trace_def rad_trace_difference_def normalise)
    by (auto simp: rad_trace_extensions_def)
qed

lemma rad_basic_merge_RA3m [closure]: "rad_basic_merge is RA3m"
  unfolding Healthy_def'
  by (rule ades_merge_ext; simp add: RA3m_obs[simplified] rad_basic_merge_obs[simplified])

lemma rad_basic_merge_CSPA1m [closure]: "rad_basic_merge is CSPA1m"
  unfolding Healthy_def'
  by (rule ades_merge_ext;
      auto simp: CSPA1m_obs[simplified] rad_basic_merge_obs[simplified] II_Rac_eval)

lemma rad_basic_merge_CSPA2m [closure]: "rad_basic_merge is CSPA2m"
  unfolding Healthy_def'
  by (rule ades_merge_ext;
      auto simp: H2m_ades_obs[simplified] rad_basic_merge_obs[simplified] II_Rac_eval)

lemma rad_basic_merge_PBMHm [closure]:
  "(rad_basic_merge :: ('t::trace, 'e) rad_merge_rel) is PBMHm"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  subgoal for ok0 s0 okL acL okR acR ok' ac'
    by (cases "rad_wait\<^sub>v s0"; cases ok0;
        simp add: PBMHm_obs[simplified] rad_basic_merge_obs[simplified]
          II_Rac_eval rad_trace_extensions_def; blast)
  done

lemma rad_basic_merge_RABm [closure]:
  "(rad_basic_merge :: ('t::trace, 'e) rad_merge_rel) is RABm"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  subgoal for ok0 s0 okL acL okR acR ok' ac'
    by (cases "rad_wait\<^sub>v s0"; cases ok0;
        simp add: RABm_obs[simplified] rad_basic_merge_obs[simplified]; blast)
  done

lemma rad_basic_merge_RADm [closure]: "rad_basic_merge is RADm"
  by (simp add: RADm_healthy_iff rad_basic_merge_RA1m rad_basic_merge_RA2m
      rad_basic_merge_RA3m rad_basic_merge_CSPA1m rad_basic_merge_CSPA2m
      rad_basic_merge_PBMHm rad_basic_merge_RABm)

subsection \<open>Choice-set lifting\<close>

text \<open>Every pair of branch states must have a merged output in the final set.
  The ordinary merge supplies the control, trace, waiting and refusal policy.\<close>

(* Lift ordinary reactive observations to nonempty branch choice sets. *)
definition rad_lift_merge ::
  "('t::trace, 'e set) rp merge \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "rad_lift_merge \<equiv> RABm \<circ> choice_lift_merge"

lemma rad_lift_merge_obs:
  "ades_merge_obs (rad_lift_merge M) ok0 s0 okL X okR Y ok' Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
      merge_eval M (\<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>)
        (\<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>)
        (\<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>)
        (\<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)))"
  by (simp add: rad_lift_merge_def RABm_choice_lift_merge_obs[simplified])

lemma rad_lift_merge_mono:
  "M \<sqsubseteq> N \<Longrightarrow> rad_lift_merge M \<sqsubseteq> rad_lift_merge N"
  unfolding rad_lift_merge_def comp_apply
  by (rule pred_ref_monoD[OF RABm_Monotonic];
      auto simp: pred_refine_iff choice_lift_merge_def Let_def split: prod.splits; blast)

lemma rad_lift_merge_SymMerge:
  "M is SymMerge \<Longrightarrow> rad_lift_merge M is SymMerge"
proof -
  assume assms: "M is SymMerge"
  have sym: "merge_eval M x p q z = merge_eval M x q p z" for x p q z
    using assms by (simp add: SymMerge_eval)
  show ?thesis
    by (simp add: SymMerge_eval des_vars.splits astate.splits achoices.splits
        rad_lift_merge_obs[simplified] sym; blast)
qed

subsubsection \<open>ORDm lift facts\<close>

lemma rad_lift_merge_CSPA2m:
  assumes "M is RD2"
  shows "rad_lift_merge M is CSPA2m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp only: H2m_ades_obs rad_lift_merge_obs)
  using RD2_ok_up[OF assms]
  apply auto
  by blast

lemma ORDm_div_eval:
  assumes "M is ORDm" "\<not> b" "s' \<in> rad_trace_extensions s0"
  shows "merge_eval M \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
    \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
proof -
  have "merge_eval M \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> =
    merge_eval (ORDm M) \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    using assms(1) by (simp add: Healthy_def')
  also have "... = (rea_vars.tr\<^sub>v \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> \<le>
      rea_vars.tr\<^sub>v \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>)"
    using assms(2) by (simp add: ORDm_unstarted)
  finally show ?thesis
    using assms(3) by (metis rad_tr_record rad_trace_extensions_def mem_Collect_eq)
qed

lemma ORDm_ext_eval:
  assumes "M is ORDm"
    and "merge_eval M \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
  shows "s' \<in> rad_trace_extensions s0"
proof -
  have h: "M is R1m" by (rule ORDm_R1m[OF assms(1)])
  have growth: "merge_eval M x p q z \<Longrightarrow>
      rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z" for x p q z
    using h by (metis Healthy_def' R1m_merge_eval)
  show ?thesis using growth assms(2)
    by (metis rad_tr_record rad_trace_extensions_def mem_Collect_eq)
qed

lemma R2m_rad_eval:
  assumes "M is R2m"
  shows "merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> =
    (s' \<in> rad_trace_extensions s0 \<and>
     merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = rad_zero_trace s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = rad_trace_difference s0 sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = rad_trace_difference s0 sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = rad_trace_difference s0 s'\<rparr>)"
proof -
  have "merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> =
    merge_eval (R2m M)
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    using assms by (simp add: Healthy_def')
  also have "... = (s' \<in> rad_trace_extensions s0 \<and>
     merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = rad_zero_trace s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = rad_trace_difference s0 sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = rad_trace_difference s0 sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = rad_trace_difference s0 s'\<rparr>)"
    by (cases s0; cases sL; cases sR; cases s';
        simp add: R2m_merge_eval rad_zero_trace_def
          rad_trace_difference_def rad_trace_extensions_def)
  finally show ?thesis .
qed

subsection \<open>Lifted merge healthiness\<close>

lemma R2m_choice_normalise:
  assumes "M is R2m"
  shows "(\<exists>s'\<in>Z. merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>) =
    (\<exists>z\<in>rad_normalise_choices s0 Z. merge_eval M
      \<lparr>ok\<^sub>v = b, \<dots> = rad_zero_trace s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = rad_trace_difference s0 sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = rad_trace_difference s0 sR\<rparr>
      \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>)"
  by (subst R2m_rad_eval[OF assms];
      auto simp: rad_normalise_choices_def rad_trace_extensions_def)

lemma rad_lift_merge_RA1m:
  assumes "M is ORDm"
  shows "rad_lift_merge M is RA1m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp add: RA1m_obs[simplified] rad_lift_merge_obs[simplified])
  using ORDm_ext_eval[OF assms] by blast

lemma rad_lift_merge_RA2m:
  assumes "M is R2m"
  shows "rad_lift_merge M is RA2m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp only: RA2m_obs rad_lift_merge_obs)
  apply (subst (2) R2m_choice_normalise[OF assms])
  apply simp
  by fast

lemma rad_lift_merge_CSPA1m:
  assumes "M is ORDm"
  shows "rad_lift_merge M is CSPA1m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp add: CSPA1m_obs[simplified] rad_lift_merge_obs[simplified])
  using ORDm_div_eval[OF assms] by blast

lemma rad_lift_merge_RA3m:
  assumes "M is ORDm"
  shows "rad_lift_merge M is RA3m"
proof -
  have div: "merge_eval M \<lparr>ok\<^sub>v = False, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> = (s' \<in> rad_trace_extensions s0)" for s0 p q c s'
    using ORDm_div_eval[OF assms, where b=False, simplified]
      ORDm_ext_eval[OF assms, where b=False]
    by blast
  have h: "M is R3cm" using assms by (simp add: ORDm_healthy_iff)
  have waiting: "merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> p q
      \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> = (c \<and> s' = s0)"
    if "rad_wait\<^sub>v s0" for s0 p q c s'
    by (subst Healthy_if[OF h, symmetric]; simp add: R3cm_eval that)
  show ?thesis
    unfolding Healthy_def'
    apply (rule ades_merge_ext)
    subgoal for ok0 s0 okL X okR Y ok' Z
      apply (cases "rad_wait\<^sub>v s0"; cases ok0)
      apply (simp_all add: RA3m_obs[simplified] rad_lift_merge_obs[simplified]
          II_Rac_eval waiting div)
      apply blast
      apply (simp add: rad_trace_extensions_def)
      by blast
    done
qed

lemma rad_lift_merge_PBMHm [closure]:
  "rad_lift_merge M is PBMHm"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  apply (simp add: PBMHm_obs[simplified] rad_lift_merge_obs[simplified])
  by blast

lemma rad_lift_merge_RABm [closure]:
  "rad_lift_merge M is RABm"
  by (simp add: Healthy_def' rad_lift_merge_def RABm_idem)

lemma rad_lift_merge_RADm:
  assumes "M is ORDm"
  shows "rad_lift_merge M is RADm"
  using assms unfolding RADm_healthy_iff
  by (auto simp: ORDm_healthy_iff intro: rad_lift_merge_RA1m rad_lift_merge_RA2m
      rad_lift_merge_RA3m rad_lift_merge_CSPA1m rad_lift_merge_PBMHm
      rad_lift_merge_RABm rad_lift_merge_CSPA2m)

subsection \<open>RAD parallel by merge\<close>

definition rad_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e set) rp merge \<Rightarrow>
    ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q \<equiv> (P \<parallel>\<^bsub>rad_lift_merge M\<^esub> Q)"

lemma rad_par_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
  shows "p2ac P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> p2ac Q = p2ac (P \<parallel>\<^bsub>M\<^esub> Q)"
  unfolding rad_par_def
  apply (rule ades_obs_ext)
  apply (simp only: rad_p2ac_obs par_by_merge_eval
      choices_ex rad_lift_merge_obs[simplified])
  apply (simp only: des_vars.splits)
  by (blast intro: exI[where x="{_}"])

lemma rad_par_form:
  "\<lbrakk> P is RAD; Q is RAD; P is A2; Q is A2 \<rbrakk> \<Longrightarrow>
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = p2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
proof -
  assume assms: "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  show ?thesis
  using rad_par_p2ac[of "ac2p P" M "ac2p Q"]
    by (simp only: rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
        rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])
qed

lemma rad_par_ac2p:
  "\<lbrakk> P is RAD; Q is RAD; P is A2; Q is A2 \<rbrakk> \<Longrightarrow>
    ac2p (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) = (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
proof -
  assume assms: "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  show ?thesis
  by (simp only: rad_par_form[OF assms] rad_ac2p_p2ac_inverse')
qed

lemma rad_par_A2:
  "\<lbrakk> P is RAD; Q is RAD; P is A2; Q is A2 \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A2"
proof -
  assume assms: "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  show ?thesis
  by (simp add: rad_par_form[OF assms] Healthy_def')
qed

lemma rad_par_RAD [closure]:
  assumes "P is RAD" "Q is RAD" "M is ORDm"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is RAD"
  unfolding rad_par_def
  by (rule rad_par_by_merge_RAD[OF assms(1,2) rad_lift_merge_RADm[OF assms(3)]])

subsection \<open>Algebra\<close>

lemma rad_par_mono:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow>
    P1 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q1 \<sqsubseteq> P2 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q2"
proof -
  assume assms: "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  show ?thesis
  unfolding rad_par_def
    using assms
    by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)
qed

lemma rad_par_comm:
  "rad_lift_merge M is SymMerge \<Longrightarrow>
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> P"
proof -
  assume assms: "rad_lift_merge M is SymMerge"
  show ?thesis
  unfolding rad_par_def
    by (rule par_by_merge_comm[OF assms])
qed

lemma rad_par_comm_merge:
  "M is SymMerge \<Longrightarrow>
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> P"
proof -
  assume assms: "M is SymMerge"
  show ?thesis
  by (rule rad_par_comm[OF rad_lift_merge_SymMerge[OF assms]])
qed

lemma rad_par_assoc_state:
  "\<lbrakk> P is RAD;
     Q is RAD;
     R is RAD;
     P is A2;
     Q is A2;
     R is A2;
     \<And>x p q r z.
      (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z) =
      (\<exists>u. merge_eval M x q r u \<and> merge_eval M x p u z) \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R)"
proof -
  assume assms: "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2"
    "\<And>x p q r z.
      (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z) =
      (\<exists>u. merge_eval M x q r u \<and> merge_eval M x p u z)"
  note assoc = assms(7)
  have ordinary: "((D \<parallel>\<^bsub>M\<^esub> E) \<parallel>\<^bsub>M\<^esub> F) = (D \<parallel>\<^bsub>M\<^esub> (E \<parallel>\<^bsub>M\<^esub> F))" for D E F
    using par_by_merge_assoc_iff[of M] assoc by blast
  show ?thesis
    using arg_cong[OF ordinary[of "ac2p P" "ac2p Q" "ac2p R"], of p2ac]
    by (simp only: rad_par_p2ac[symmetric]
        rad_p2ac_ac2p_RAD_A2'[OF assms(1,4)]
        rad_p2ac_ac2p_RAD_A2'[OF assms(2,5)]
        rad_p2ac_ac2p_RAD_A2'[OF assms(3,6)])
qed

lemma rad_par_assoc:
  "\<lbrakk> P is RAD; Q is RAD; R is RAD; P is A2; Q is A2; R is A2; M is SymMerge;
     AssocMerge M \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R)"
proof -
  assume assms: "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2"
    "M is SymMerge" "AssocMerge M"
  have ordinary: "\<forall>D E F.
    (D \<parallel>\<^bsub>M\<^esub> E) \<parallel>\<^bsub>M\<^esub> F =
    D \<parallel>\<^bsub>M\<^esub> (E \<parallel>\<^bsub>M\<^esub> F)"
    using par_by_merge_assoc[OF assms(7,8)] by blast
  show ?thesis
    by (rule rad_par_assoc_state[OF assms(1-6)];
        use ordinary par_by_merge_assoc_iff[of M] in blast)
qed

text \<open>The following law transfers associativity from nondivergent RD images
  through @{const p2ac}.\<close>

lemma rad_par_lift_assoc:
  "\<lbrakk> P is RAD; Q is RAD; R is RAD; P is A2; Q is A2; R is A2; j is SymMerge;
     AssocMerge j; pre\<^sub>R (ac2p P) = true\<^sub>r; pre\<^sub>R (ac2p Q) = true\<^sub>r;
     pre\<^sub>R (ac2p R) = true\<^sub>r \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>merge_rdes j\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>merge_rdes j\<^esub> R =
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>merge_rdes j\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>merge_rdes j\<^esub> R)"
proof -
  assume assms: "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2" "j is SymMerge"
    "AssocMerge j" "pre\<^sub>R (ac2p P) = true\<^sub>r" "pre\<^sub>R (ac2p Q) = true\<^sub>r"
    "pre\<^sub>R (ac2p R) = true\<^sub>r"
  let ?M = "merge_rdes j"
  have rd: "ac2p P is RD" "ac2p Q is RD" "ac2p R is RD"
    using rad_ac2p_RD assms(1-6) by blast+
  have nondiv: "ac2p P is NDRD" "ac2p Q is NDRD" "ac2p R is NDRD"
    using rd assms(9-11) by (simp_all add: NDRD_healthy_iff)
  have ordinary: "(ac2p P \<parallel>\<^bsub>?M\<^esub> ac2p Q) \<parallel>\<^bsub>?M\<^esub> ac2p R =
      ac2p P \<parallel>\<^bsub>?M\<^esub> (ac2p Q \<parallel>\<^bsub>?M\<^esub> ac2p R)"
    by (rule rdes_lift_parallel_assoc_nondiv[OF assms(7,8) rd nondiv])
  show ?thesis
    using arg_cong[OF ordinary, of p2ac]
    by (simp only: rad_par_p2ac[symmetric]
        rad_p2ac_ac2p_RAD_A2'[OF assms(1,4)]
        rad_p2ac_ac2p_RAD_A2'[OF assms(2,5)]
        rad_p2ac_ac2p_RAD_A2'[OF assms(3,6)])
qed

subsection \<open>Merge induced by j\<close>

(* Lift the completed ordinary RD merge from j to RAD choice sets. *)
definition merge_rad :: "('t::trace \<times> 'e set) merge \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "merge_rad j \<equiv> rad_lift_merge (merge_rdes j)"

lemma merge_rad_RADm [closure]:
  "merge_rad j is RADm"
  by (simp add: merge_rad_def rad_lift_merge_RADm merge_rdes_ORDm)

lemma merge_rad_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
    and j :: "('t \<times> 'e set) merge"
  shows "p2ac P \<parallel>\<^bsub>merge_rad j\<^esub> p2ac Q =
    p2ac (P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q)"
  by (simp only: merge_rad_def rad_par_def[symmetric] rad_par_p2ac)

end
