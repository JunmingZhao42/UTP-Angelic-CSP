section \<open>RAD Merge Healthiness\<close>

theory utp_rad_parallel_merge
  imports utp_rad_nd "UTP-Angelic-Designs.utp_ades_parallel_choice_lift"
    "UTP-Reactive-Designs.utp_rdes_parallel_laws"
begin

(* The ordinary parallel import restores this notation; retain the RAD meaning. *)
no_notation wait_f ("_\<^sub>f" [1000] 1000)

type_synonym ('t, 'e) rad_merge_rel =
  "(('t, 'e) rad_state) ades_merge_rel"

text \<open>The RAD fixed point separates into reactive, divergence, design, and
  upward choice-set conditions. The merge conditions below preserve each one.\<close>

subsection \<open>Merge healthiness transformers\<close>

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

subsection \<open>Idempotence and monotonicity\<close>

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

subsection \<open>Commutation\<close>

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

lemma RA1m_ABm_commute: "RA1m (ABm M) = ABm (RA1m M)"
  by (rule ades_merge_ext; auto simp: RA1m_obs[simplified] ABm_obs[simplified] ; blast)

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

lemma RA3m_ABm_commute: "RA3m (ABm M) = ABm (RA3m M)"
  by (rule ades_merge_ext; auto simp: RA3m_obs[simplified] ABm_obs[simplified] ; blast)

lemma RA3m_CSPA2m_commute: "RA3m (CSPA2m M) = CSPA2m (RA3m M)"
  by (rule ades_merge_ext; auto simp: RA3m_obs[simplified] H2m_ades_obs[simplified] II_Rac_eval; blast)

lemma CSPA1m_PBMHm_commute: "CSPA1m (PBMHm M) = PBMHm (CSPA1m M)"
  by (rule ades_merge_ext; auto simp: CSPA1m_obs[simplified] PBMHm_obs[simplified] ; blast)

lemma CSPA1m_ABm_commute: "CSPA1m (ABm M) = ABm (CSPA1m M)"
  by (rule ades_merge_ext; auto simp: CSPA1m_obs[simplified] ABm_obs[simplified] ; blast)

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

lemma RA2m_ABm_commute:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  shows "RA2m (ABm M) = ABm (RA2m M)"
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
  show "ades_merge_obs (RA2m (ABm M)) ok0 s0 okL X okR Y ok' Z =
    ades_merge_obs (ABm (RA2m M)) ok0 s0 okL X okR Y ok' Z"
    by (cases "rad_normalise_choices s0 Z = {}";
        simp add: RA2m_obs[simplified] ABm_obs[simplified] eq[simplified])
qed

subsection \<open>Combined merge healthiness\<close>

(* RAm combines trace normalisation, waiting, and branch choice-set closure. *)
definition RAm :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RAm \<equiv> RA2m \<circ> RA3m \<circ> ABm"

lemma RAm_healths [closure]:
  "RAm M is RA1m"
  "RAm M is RA2m"
  "RAm M is RA3m"
  "RAm M is ABm"
  by (simp_all add: Healthy_def' RAm_def RA1m_RA2m_absorb
      RA2m_RA3m_commute[symmetric] RA2m_ABm_commute[symmetric]
      RA3m_ABm_commute[symmetric] RA2m_idem RA3m_idem ABm_idem)

lemma RAm_healthy_iff:
  "(M is RAm) \<longleftrightarrow> ((M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is ABm))"
proof
  assume "M is RAm"
  then show "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is ABm)"
    using RAm_healths[of M] by (simp only: Healthy_if)
next
  assume "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is ABm)"
  then show "M is RAm" by (simp add: Healthy_def' RAm_def)
qed

lemma RAm_Idempotent [closure]: "Idempotent RAm"
  by (simp add: Idempotent_def Healthy_def'[symmetric] RAm_healthy_iff RAm_healths)

lemma RAm_Monotonic [closure]: "Monotonic RAm"
  unfolding RAm_def
  by (intro Monotonic_comp RA2m_Monotonic RA3m_Monotonic ABm_Monotonic)

(* RADm combines the commuting reactive, design, and choice-set conditions. *)
definition RADm :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RADm \<equiv> RA2m \<circ> RA3m \<circ> CSPA1m \<circ> PBMHm \<circ> ABm \<circ> CSPA2m"

lemmas RADm_comms =
  RA1m_RA2m_commute[symmetric]
  RA1m_RA3m_commute[symmetric]
  RA1m_CSPA1m_commute[symmetric]
  RA1m_PBMHm_commute[symmetric]
  RA1m_ABm_commute[symmetric]
  RA1m_CSPA2m_commute[symmetric]
  RA2m_RA3m_commute[symmetric]
  RA2m_CSPA1m_commute[symmetric]
  RA2m_PBMHm_commute[symmetric]
  RA2m_ABm_commute[symmetric]
  RA2m_CSPA2m_commute[symmetric]
  RA3m_CSPA1m_commute[symmetric]
  RA3m_PBMHm_commute[symmetric]
  RA3m_ABm_commute[symmetric]
  RA3m_CSPA2m_commute[symmetric]
  CSPA1m_PBMHm_commute[symmetric]
  CSPA1m_ABm_commute[symmetric]
  CSPA1m_CSPA2m_commute[symmetric]
  PBMHm_ABm_commute[symmetric]
  PBMHm_H2m_commute[symmetric]
  ABm_H2m_commute[symmetric]

lemma RADm_healths [closure]:
  "RADm M is RA1m"
  "RADm M is RA2m"
  "RADm M is RA3m"
  "RADm M is CSPA1m"
  "RADm M is PBMHm"
  "RADm M is ABm"
  "RADm M is CSPA2m"
  by (simp_all add: Healthy_def' RADm_def RADm_comms
      RA1m_RA2m_absorb RA2m_idem RA3m_idem CSPA1m_idem PBMHm_idem ABm_idem H2m_Idempotent[unfolded Idempotent_def])

lemma RADm_healthy_iff:
  "(M is RADm) \<longleftrightarrow> ((M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is CSPA1m) \<and> (M is PBMHm) \<and> (M is ABm) \<and> (M is CSPA2m))"
proof
  assume "M is RADm"
  then show "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is CSPA1m) \<and> (M is PBMHm) \<and> (M is ABm) \<and> (M is CSPA2m)"
    using RADm_healths[of M] by (simp only: Healthy_if)
next
  assume "(M is RA1m) \<and> (M is RA2m) \<and> (M is RA3m) \<and> (M is CSPA1m) \<and> (M is PBMHm) \<and> (M is ABm) \<and> (M is CSPA2m)"
  then show "M is RADm" by (simp add: Healthy_def' RADm_def)
qed

lemma RADm_Idempotent [closure]: "Idempotent RADm"
  by (simp add: Idempotent_def Healthy_def'[symmetric] RADm_healthy_iff RADm_healths)

lemma RADm_Monotonic [closure]: "Monotonic RADm"
  unfolding RADm_def
  by (intro Monotonic_comp RA2m_Monotonic RA3m_Monotonic CSPA1m_Monotonic PBMHm_Monotonic ABm_Monotonic H2m_Monotonic)

end
