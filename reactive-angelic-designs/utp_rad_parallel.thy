section \<open>Reactive Angelic Design Parallel-by-Merge\<close>

theory utp_rad_parallel
  imports utp_rad_designs
begin

subsection \<open>Merge Healthiness Conditions\<close>

text \<open>
  The angelic-design parallel operator \<open>ades_par\<close> lifts a
  state-level merge @{typ "('t::trace, 'e) rad_state merge"} to choice sets, so all
  reactive content of a reactive angelic design parallel composition lives in
  that state-level merge.  The healthiness conditions below therefore
  constrain the state-level merge directly, following the structure of
  \<open>R1m\<close>, \<open>R2m\<close>, and \<open>R3m\<close> from \<open>utp_rea_parallel\<close> rather than their
  reactive-design types.

  Unlike the reactive-design condition \<open>RDM\<close>, no quantification over
  @{term ok} or @{term wait} is needed: the design observation @{term ok} is
  combined by the angelic-design lift itself, and the waiting flag is genuine
  state of @{typ "('t::trace, 'e) rad_state"} that a merge must define, with the
  waiting-prior case handled by \<open>RA3m\<close>.
\<close>

text \<open>
  \<open>RA1m\<close> requires the merged state's trace to extend the prior trace.  The
  stronger \<open>RA1m'\<close> also requires both branch choices to extend it; it is
  intended for closure proofs where the branch choices come from
  \<open>RA1\<close>-healthy operands.
\<close>

definition RA1m ::
  "('t::trace, 'e) rad_state merge \<Rightarrow> ('t, 'e) rad_state merge"
  where [pred]: "RA1m(j) = (j \<and> $<:tr\<^sup>< \<le> $tr\<^sup>>)\<^sub>e"

definition RA1m' ::
  "('t::trace, 'e) rad_state merge \<Rightarrow> ('t, 'e) rad_state merge"
  where [pred]: "RA1m'(j) =
    (j \<and> $<:tr\<^sup>< \<le> $tr\<^sup>> \<and> $<:tr\<^sup>< \<le> $0:tr\<^sup>< \<and> $<:tr\<^sup>< \<le> $1:tr\<^sup><)\<^sub>e"

text \<open>
  \<open>RA2m\<close> makes the merge depend only on the trace contributions: the prior
  trace is replaced by zero and the branch and merged traces by their
  differences from it, exactly as in \<open>R2m\<close>.
\<close>

definition RA2m ::
  "('t::trace, 'e) rad_state merge \<Rightarrow> ('t, 'e) rad_state merge"
  where [pred]: "RA2m(j) = RA1m(j\<lbrakk>0,($tr\<^sup>>-$<:tr\<^sup><),($0:tr\<^sup><-$<:tr\<^sup><),($1:tr\<^sup><-$<:tr\<^sup><)/<:tr\<^sup><,tr\<^sup>>,0:tr\<^sup><,1:tr\<^sup><\<rbrakk>)\<^sub>e"

definition RA2m' ::
  "('t::trace, 'e) rad_state merge \<Rightarrow> ('t, 'e) rad_state merge"
  where [pred]: "RA2m'(j) = RA1m'(j\<lbrakk>0,($tr\<^sup>>-$<:tr\<^sup><),($0:tr\<^sup><-$<:tr\<^sup><),($1:tr\<^sup><-$<:tr\<^sup><)/<:tr\<^sup><,tr\<^sup>>,0:tr\<^sup><,1:tr\<^sup><\<rbrakk>)"

text \<open>
  \<open>RA3m\<close> requires a merge to restore the prior state when it is a waiting
  state, mirroring \<open>R3m\<close>.  Since the state-level merge is homogeneous, the
  generic @{const skip\<^sub>m} expresses the restored prior directly.
\<close>

definition RA3m ::
  "('t::trace, 'e) rad_state merge \<Rightarrow> ('t, 'e) rad_state merge"
  where [pred]: "RA3m(j) = skip\<^sub>m \<triangleleft> $<:wait\<^sup>< \<triangleright> j"

text \<open>
  \<open>RADM\<close> is the composite merge healthiness condition for reactive angelic
  designs.  \<open>RA1m\<close> is absorbed, because \<open>RA2m\<close> already applies it.
\<close>

definition RADM ::
  "('t::trace, 'e) rad_state merge \<Rightarrow> ('t, 'e) rad_state merge"
  where [pred]: "RADM = RA2m \<circ> RA3m"

subsection \<open>Idempotence and Monotonicity\<close>

lemma RA1m_idem: "RA1m (RA1m j) = RA1m j"
  by pred_auto

lemma RA1m'_idem: "RA1m' (RA1m' j) = RA1m' j"
  by pred_auto

lemma RA2m_idem: "RA2m (RA2m j) = RA2m j"
  by pred_auto

lemma RA2m'_idem: "RA2m' (RA2m' j) = RA2m' j"
  by pred_auto

lemma RA3m_idem: "RA3m (RA3m j) = RA3m j"
  by pred_auto

lemma RADM_idem: "RADM (RADM j) = RADM j"
  by pred_auto

lemma RA1m_Idempotent [closure]: "Idempotent RA1m"
  by (simp add: Idempotent_def RA1m_idem)

lemma RA2m_Idempotent [closure]: "Idempotent RA2m"
  by (simp add: Idempotent_def RA2m_idem)

lemma RA3m_Idempotent [closure]: "Idempotent RA3m"
  by (simp add: Idempotent_def RA3m_idem)

lemma RADM_Idempotent [closure]: "Idempotent RADM"
  by (simp add: Idempotent_def RADM_idem)

lemma RA1m_mono: "j \<sqsubseteq> k \<Longrightarrow> RA1m j \<sqsubseteq> RA1m k"
  by pred_auto

lemma RA2m_mono: "j \<sqsubseteq> k \<Longrightarrow> RA2m j \<sqsubseteq> RA2m k"
  by pred_auto

lemma RA3m_mono: "j \<sqsubseteq> k \<Longrightarrow> RA3m j \<sqsubseteq> RA3m k"
  by pred_auto

lemma RADM_mono: "j \<sqsubseteq> k \<Longrightarrow> RADM j \<sqsubseteq> RADM k"
  by (simp add: RADM_def RA2m_mono RA3m_mono)

lemma RA1m_Monotonic [closure]: "Monotonic RA1m"
  by (rule MonotonicI, rule RA1m_mono)

lemma RA2m_Monotonic [closure]: "Monotonic RA2m"
  by (rule MonotonicI, rule RA2m_mono)

lemma RA3m_Monotonic [closure]: "Monotonic RA3m"
  by (rule MonotonicI, rule RA3m_mono)

lemma RADM_Monotonic [closure]: "Monotonic RADM"
  by (rule MonotonicI, rule RADM_mono)

subsection \<open>Distribution Laws\<close>

lemma RA1m_conj: "RA1m (j \<and> k) = (RA1m j \<and> RA1m k)"
  by pred_auto

lemma RA1m_disj: "RA1m (j \<or> k) = (RA1m j \<or> RA1m k)"
  by pred_auto

lemma RA2m_conj: "RA2m (j \<and> k) = (RA2m j \<and> RA2m k)"
  by pred_auto

lemma RA2m_disj: "RA2m (j \<or> k) = (RA2m j \<or> RA2m k)"
  by pred_auto

lemma RA3m_conj: "RA3m (j \<and> k) = (RA3m j \<and> RA3m k)"
  by pred_auto

lemma RA3m_disj: "RA3m (j \<or> k) = (RA3m j \<or> RA3m k)"
  by pred_auto

lemma RA2m_wait_cond:
  "RA2m (P \<triangleleft> $<:wait\<^sup>< \<triangleright> Q) =
   (RA2m P \<triangleleft> $<:wait\<^sup>< \<triangleright> RA2m Q)"
  by pred_auto

subsection \<open>Fixed Points and Commutation\<close>

lemma RA1m_skip_merge: "RA1m skip\<^sub>m = skip\<^sub>m"
  by pred_auto

lemma RA2m_skip_merge: "RA2m skip\<^sub>m = skip\<^sub>m"
  by (pred_auto add: minus_zero_eq)

lemma RA3m_skip_merge: "RA3m skip\<^sub>m = skip\<^sub>m"
  by pred_auto

lemma RA2m_RA3m_commute: "(RA2m \<circ> RA3m) j = (RA3m \<circ> RA2m) j"
  by (simp only: comp_apply RA3m_def RA2m_wait_cond RA2m_skip_merge)

lemma RADM_skip_merge: "RADM skip\<^sub>m = skip\<^sub>m"
  by (simp add: RADM_def RA3m_skip_merge RA2m_skip_merge)

lemma RADM_is_RA1m: "RA1m (RADM j) = RADM j"
  by pred_auto

subsection \<open>Symmetry Preservation\<close>

text \<open>
  Each condition preserves the direct symmetry equation used by
  @{thm [source] ades_par_comm}, so a symmetric state-level merge
  remains symmetric after normalisation and the resulting parallel operator
  stays commutative.
\<close>

lemma RA1m_swap:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; RA1m j = RA1m j"
  using assms by (pred_auto; blast)

lemma RA2m_swap:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; RA2m j = RA2m j"
  using assms by (pred_auto; blast)

lemma RA3m_swap:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; RA3m j = RA3m j"
  using assms by (pred_auto; blast)

lemma RADM_swap:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; RADM j = RADM j"
  by (simp only: RADM_def comp_apply RA2m_swap RA3m_swap assms)

subsection \<open>Totality\<close>

text \<open>
  @{const A0j} of the healthy merge is what @{thm [source]
  ades_par_A_closure} will need.  \<open>RA3m\<close> preserves totality, since
  a waiting prior is merged to itself; totality of an \<open>RA1m\<close>- or
  \<open>RA2m\<close>-healthy merge must be established per concrete merge, because those
  conditions cut states out of the merge image.
\<close>

lemma A0j_skip_merge: "A0j skip\<^sub>m"
  by (simp add: A0j_def; pred_auto)

subsection \<open>Merge Condition Preservation\<close>

text \<open>
  \<open>RA3m\<close> preserves functionality and singleton-image exclusion: its
  waiting branch is @{const skip\<^sub>m}, and flipping the waiting flag
  supplies an excluded singleton.  \<open>RA2m\<close> preserves all three conditions:
  prepending the prior trace is inverse to taking trace differences, so
  merged states of the normalised merge and of the underlying merge are
  in bijection over the trace-extending states.
\<close>

lemma RA3m_eval:
  fixes j :: "('t::trace, 'e) rad_state merge" and s p q z :: "('t, 'e) rad_state"
  shows "RA3m j (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z) \<longleftrightarrow>
    (if rad_state.wait\<^sub>v s then z = s
     else j (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z))"
  by (simp add: RA3m_def skip_merge_eval; pred_auto)

lemma RA3m_A0j:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "A0j j"
  shows "A0j (RA3m j)"
proof (unfold A0j_def, intro allI)
  fix s p q :: "('t, 'e) rad_state"
  show "\<exists>z. RA3m j
      (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z)"
  proof (cases "rad_state.wait\<^sub>v s")
    case True
    then show ?thesis by (auto simp add: RA3m_eval)
  next
    case False
    then show ?thesis
      using assms unfolding A0j_def by (auto simp add: RA3m_eval)
  qed
qed

lemma RA3m_A2j:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "A2j j"
  shows "A2j (RA3m j)"
proof (unfold A2j_def, intro allI impI)
  fix s p q z1 z2 :: "('t, 'e) rad_state"
  let ?m = "\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>"
  assume j1: "RA3m j (?m, z1)" and j2: "RA3m j (?m, z2)"
  show "z1 = z2"
  proof (cases "rad_state.wait\<^sub>v s")
    case True
    then show ?thesis using j1 j2 by (simp add: RA3m_eval)
  next
    case False
    then have "j (?m, z1)" "j (?m, z2)"
      using j1 j2 by (simp_all add: RA3m_eval)
    then show ?thesis using assms unfolding A2j_def by blast
  qed
qed

lemma RA3m_A3j:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "A3j j"
  shows "A3j (RA3m j)"
proof (unfold A3j_def, intro allI)
  fix s :: "('t, 'e) rad_state"
  show "\<exists>z. \<forall>X Y. ades_merge_image (RA3m j) s X Y \<noteq> {z}"
  proof (cases "rad_state.wait\<^sub>v s")
    case True
    let ?z = "rad_state.wait\<^sub>v_update (\<lambda>w. \<not> w) s"
    have "?z \<noteq> s"
      by (cases s) simp
    then have "\<And>X Y. ?z \<notin> ades_merge_image (RA3m j) s X Y"
      using True by (simp add: ades_merge_image_def RA3m_eval)
    then show ?thesis by blast
  next
    case False
    obtain z where "\<forall>X Y. ades_merge_image j s X Y \<noteq> {z}"
      using assms unfolding A3j_def by blast
    then show ?thesis
      using False by (simp add: ades_merge_image_def RA3m_eval; blast)
  qed
qed

lemma RA2m_eval:
  fixes j :: "('t::trace, 'e) rad_state merge"
    and s0 p q z :: "('t, 'e) rad_state"
  shows "RA2m j (\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z)
    \<longleftrightarrow>
    (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
     j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace s0,
         mrg_left\<^sub>v = rad_trace_difference s0 p,
         mrg_right\<^sub>v = rad_trace_difference s0 q, \<dots> = ()\<rparr>,
        rad_trace_difference s0 z))"
  by (simp add: RA2m_def RA1m_def rad_zero_trace_def
      rad_trace_difference_def; pred_auto)

lemma rad_diff_prepend:
  fixes s0 w :: "('t::trace, 'e) rad_state"
  shows "rad_trace_difference s0
     (rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) w) = w"
  by (cases w) (simp add: rad_trace_difference_def)

lemma rad_prepend_ge:
  fixes s0 w :: "('t::trace, 'e) rad_state"
  shows "rad_state.tr\<^sub>v s0 \<le>
   rad_state.tr\<^sub>v (rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) w)"
  by (cases w) (simp add: le_add)

lemma rad_diff_inj:
  fixes s0 z1 z2 :: "('t::trace, 'e) rad_state"
  assumes le1: "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z1"
    and le2: "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z2"
    and deq: "rad_trace_difference s0 z1 = rad_trace_difference s0 z2"
  shows "z1 = z2"
proof -
  have tr_deq: "rad_state.tr\<^sub>v z1 - rad_state.tr\<^sub>v s0 =
      rad_state.tr\<^sub>v z2 - rad_state.tr\<^sub>v s0"
  proof -
    have "rad_state.tr\<^sub>v (rad_trace_difference s0 z1) =
        rad_state.tr\<^sub>v (rad_trace_difference s0 z2)"
      using deq by simp
    then show ?thesis by (simp add: rad_trace_difference_def)
  qed
  have tr_eq: "rad_state.tr\<^sub>v z1 = rad_state.tr\<^sub>v z2"
  proof -
    have "rad_state.tr\<^sub>v z1 =
        rad_state.tr\<^sub>v s0 + (rad_state.tr\<^sub>v z1 - rad_state.tr\<^sub>v s0)"
      using le1 by (simp add: diff_add_cancel_left')
    also have "... =
        rad_state.tr\<^sub>v s0 + (rad_state.tr\<^sub>v z2 - rad_state.tr\<^sub>v s0)"
      by (simp only: tr_deq)
    also have "... = rad_state.tr\<^sub>v z2"
      using le2 by (simp add: diff_add_cancel_left')
    finally show ?thesis .
  qed
  have "z1 = rad_state.tr\<^sub>v_update (\<lambda>_. rad_state.tr\<^sub>v z1)
      (rad_trace_difference s0 z1)"
    by (simp add: rad_trace_difference_def)
  also have "... = rad_state.tr\<^sub>v_update (\<lambda>_. rad_state.tr\<^sub>v z2)
      (rad_trace_difference s0 z2)"
    by (simp only: deq tr_eq)
  also have "... = z2"
    by (simp add: rad_trace_difference_def)
  finally show ?thesis .
qed

lemma RA2m_A0j:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "A0j j"
  shows "A0j (RA2m j)"
proof (unfold A0j_def, intro allI)
  fix s p q :: "('t, 'e) rad_state"
  obtain w where wj: "j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace s,
      mrg_left\<^sub>v = rad_trace_difference s p,
      mrg_right\<^sub>v = rad_trace_difference s q, \<dots> = ()\<rparr>, w)"
    using assms unfolding A0j_def by blast
  let ?z = "rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s + tr) w"
  have "RA2m j (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, ?z)"
    by (simp add: RA2m_eval rad_diff_prepend rad_prepend_ge wj)
  then show "\<exists>z. RA2m j
      (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z)"
    by blast
qed

lemma RA2m_A2j:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "A2j j"
  shows "A2j (RA2m j)"
proof (unfold A2j_def, intro allI impI)
  fix s p q z1 z2 :: "('t, 'e) rad_state"
  let ?m = "\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>"
  assume j1: "RA2m j (?m, z1)" and j2: "RA2m j (?m, z2)"
  have le1: "rad_state.tr\<^sub>v s \<le> rad_state.tr\<^sub>v z1"
    and w1: "j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace s,
      mrg_left\<^sub>v = rad_trace_difference s p,
      mrg_right\<^sub>v = rad_trace_difference s q, \<dots> = ()\<rparr>,
      rad_trace_difference s z1)"
    using j1 by (simp_all add: RA2m_eval)
  have le2: "rad_state.tr\<^sub>v s \<le> rad_state.tr\<^sub>v z2"
    and w2: "j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace s,
      mrg_left\<^sub>v = rad_trace_difference s p,
      mrg_right\<^sub>v = rad_trace_difference s q, \<dots> = ()\<rparr>,
      rad_trace_difference s z2)"
    using j2 by (simp_all add: RA2m_eval)
  have "rad_trace_difference s z1 = rad_trace_difference s z2"
    using assms w1 w2 unfolding A2j_def by blast
  then show "z1 = z2"
    by (rule rad_diff_inj[OF le1 le2])
qed

lemma RA2m_A3j:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "A3j j"
  shows "A3j (RA2m j)"
proof (unfold A3j_def, intro allI)
  fix s :: "('t, 'e) rad_state"
  obtain w where wb: "\<forall>X Y. ades_merge_image j (rad_zero_trace s) X Y \<noteq> {w}"
    using assms unfolding A3j_def by blast
  let ?D = "rad_trace_difference s"
  let ?U = "rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s + tr)
    :: ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state"
  have inj: "inj ?U"
    by (rule inj_on_inverseI[where g="?D"]; simp add: rad_diff_prepend)
  have image_mem: "\<And>X Y v. v \<in> ades_merge_image j (rad_zero_trace s) (?D ` X) (?D ` Y)
      \<longleftrightarrow> ?U v \<in> ades_merge_image (RA2m j) s X Y"
    by (auto simp add: ades_merge_image_def RA2m_eval rad_diff_prepend rad_prepend_ge)
  show "\<exists>z. \<forall>X Y. ades_merge_image (RA2m j) s X Y \<noteq> {z}"
  proof (intro exI[where x="?U w"] allI notI)
    fix X Y
    assume img: "ades_merge_image (RA2m j) s X Y = {?U w}"
    have "ades_merge_image j (rad_zero_trace s) (?D ` X) (?D ` Y) = {w}"
      by (rule Set.set_eqI; simp only: image_mem img singleton_iff inj_eq[OF inj])
    with wb show False by blast
  qed
qed

subsection \<open>Merge Healthiness Projections\<close>

text \<open>
  The two generic extraction lemmas turn a fixed point of a composite
  into a fixed point of an idempotent component.
\<close>

lemma idem_fix_extract:
  assumes idem: "\<And>y. F (F y) = F y" and e: "F (G x) = x"
  shows "F x = x"
proof -
  have "F x = F (F (G x))" by (simp only: e)
  also have "... = F (G x)" by (rule idem)
  also have "... = x" by (rule e)
  finally show ?thesis .
qed

lemma fix_transfer:
  assumes fk: "F (K x) = K x" and e: "K x = x"
  shows "F x = x"
proof -
  have "F x = F (K x)" by (simp only: e)
  also have "... = K x" by (rule fk)
  also have "... = x" by (rule e)
  finally show ?thesis .
qed

lemma RADM_implies_RA1m:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "j is RADM"
  shows "j is RA1m"
  using assms unfolding Healthy_def'
  by (rule fix_transfer[where F = RA1m and K = RADM, OF RADM_is_RA1m])

lemma RADM_implies_RA2m:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "j is RADM"
  shows "j is RA2m"
proof -
  have "RA2m (RA3m j) = j"
    using assms by (simp add: Healthy_def' RADM_def)
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[OF RA2m_idem])
qed

lemma RADM_implies_RA3m:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "j is RADM"
  shows "j is RA3m"
proof -
  have "RA3m (RA2m j) = j"
    using assms
    by (simp add: Healthy_def' RADM_def
        RA2m_RA3m_commute[simplified comp_apply])
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[OF RA3m_idem])
qed

subsection \<open>Strict Trace Growth\<close>

text \<open>
  Strict trace growth strengthens \<open>RA1m\<close> in the manner of reactive
  productivity.  It is a conjunctive healthiness condition, and any
  strictly-growing merge satisfies @{const A3j} outright: the prior state
  itself cannot occur in any merge image, since its trace does not strictly
  extend itself, so its singleton is excluded.
\<close>

definition RA1sm ::
  "('t::trace, 'e) rad_state merge \<Rightarrow> ('t, 'e) rad_state merge"
  where [pred]: "RA1sm(j) = (j \<and> $<:tr\<^sup>< < $tr\<^sup>>)\<^sub>e"

lemma RA1sm_idem: "RA1sm (RA1sm j) = RA1sm j"
  by (simp add: RA1sm_def; pred_auto)

lemma RA1sm_Idempotent [closure]: "Idempotent RA1sm"
  by (simp add: Idempotent_def RA1sm_idem)

lemma RA1sm_mono: "j \<sqsubseteq> k \<Longrightarrow> RA1sm j \<sqsubseteq> RA1sm k"
  by (simp add: RA1sm_def; pred_auto)

lemma RA1sm_Monotonic [closure]: "Monotonic RA1sm"
  by (rule MonotonicI, rule RA1sm_mono)

lemma RA1m_RA1sm_absorb: "RA1m (RA1sm j) = RA1sm j"
  by (simp add: RA1m_def RA1sm_def; pred_auto)

lemma RA1sm_A3j:
  fixes j :: "('t::trace, 'e) rad_state merge"
  shows "A3j (RA1sm j)"
proof (unfold A3j_def, intro allI)
  fix s :: "('t, 'e) rad_state"
  have "\<And>X Y. s \<notin> ades_merge_image (RA1sm j) s X Y"
    by (simp add: ades_merge_image_def RA1sm_def; pred_auto)
  then show "\<exists>z. \<forall>X Y. ades_merge_image (RA1sm j) s X Y \<noteq> {z}" by blast
qed

subsection \<open>Pointwise Evaluations\<close>

text \<open>
  The closure proofs below argue at the level of observations, so each
  healthiness condition is characterised at a point.
\<close>

lemma skip_merge_eval:
  "skip\<^sub>m (m, z) \<longleftrightarrow> z = mrg_prior\<^sub>v m"
  by (cases m; simp add: skip\<^sub>m_def; pred_auto)

lemma RA1m_healthy_dest:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "j is RA1m" "j (m, z)"
  shows "rad_state.tr\<^sub>v (mrg_prior\<^sub>v m) \<le> rad_state.tr\<^sub>v z"
proof -
  have jm: "RA1m j = j"
    using assms(1) by (simp add: Healthy_def')
  have "RA1m j (m, z)"
    by (simp only: jm assms(2))
  then show ?thesis
    by (cases m; simp add: RA1m_def; pred_auto)
qed

lemma RA3m_healthy_wait:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "j is RA3m" "rad_state.wait\<^sub>v (mrg_prior\<^sub>v m)"
  shows "j (m, z) \<longleftrightarrow> z = mrg_prior\<^sub>v m"
proof -
  have jm: "RA3m j = j"
    using assms(1) by (simp add: Healthy_def')
  have "j (m, z) \<longleftrightarrow> RA3m j (m, z)"
    by (simp only: jm)
  also have "... \<longleftrightarrow> z = mrg_prior\<^sub>v m"
    using assms(2) by (cases m; simp add: RA3m_def; pred_auto)
  finally show ?thesis .
qed

lemma RA2m_healthy_eval:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes "j is RA2m"
  shows "j (\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z)
    \<longleftrightarrow>
    (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
     j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace s0,
         mrg_left\<^sub>v = rad_trace_difference s0 p,
         mrg_right\<^sub>v = rad_trace_difference s0 q, \<dots> = ()\<rparr>,
        rad_trace_difference s0 z))"
proof -
  have jm: "RA2m j = j"
    using assms by (simp add: Healthy_def')
  have "j (\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z)
    \<longleftrightarrow>
    RA2m j (\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z)"
    by (simp only: jm)
  also have "... \<longleftrightarrow>
    (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
     j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace s0,
         mrg_left\<^sub>v = rad_trace_difference s0 p,
         mrg_right\<^sub>v = rad_trace_difference s0 q, \<dots> = ()\<rparr>,
        rad_trace_difference s0 z))"
    by (simp add: RA2m_def RA1m_def rad_zero_trace_def
        rad_trace_difference_def; pred_auto)
  finally show ?thesis .
qed

lemma RA1_healthy_non_empty:
  assumes "P is RA1" "P (x, y)"
  shows "rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
         achoices.ac\<^sub>v (des_vars.more y) \<noteq> {}"
proof -
  have "RA1 P (x, y)"
    using assms by (simp add: Healthy_def')
  then show ?thesis
    by (simp add: RA1_def Let_def)
qed

lemma RA2_healthy_eval:
  assumes "P is RA2"
  shows "P (x, y) \<longleftrightarrow>
    P (des_vars.more_update
         (\<lambda>_. astate.s\<^sub>v_update
            (\<lambda>_. rad_zero_trace (astate.s\<^sub>v (des_vars.more x)))
            (des_vars.more x)) x,
       des_vars.more_update
         (\<lambda>_. achoices.ac\<^sub>v_update
            (\<lambda>_. rad_normalise_choices
                   (astate.s\<^sub>v (des_vars.more x))
                   (achoices.ac\<^sub>v (des_vars.more y)))
            (des_vars.more y)) y)"
proof -
  have h: "RA2 P = P"
    using assms by (simp add: Healthy_def')
  have "P (x, y) \<longleftrightarrow> RA2 P (x, y)"
    by (simp only: h)
  also have "... \<longleftrightarrow>
    P (des_vars.more_update
         (\<lambda>_. astate.s\<^sub>v_update
            (\<lambda>_. rad_zero_trace (astate.s\<^sub>v (des_vars.more x)))
            (des_vars.more x)) x,
       des_vars.more_update
         (\<lambda>_. achoices.ac\<^sub>v_update
            (\<lambda>_. rad_normalise_choices
                   (astate.s\<^sub>v (des_vars.more x))
                   (achoices.ac\<^sub>v (des_vars.more y)))
            (des_vars.more y)) y)"
    by (simp add: RA2_def Let_def)
  finally show ?thesis .
qed

lemma II_Rac_eval:
  "II_Rac (x, y) \<longleftrightarrow>
   ((\<not> des_vars.ok\<^sub>v x \<and>
     rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
       achoices.ac\<^sub>v (des_vars.more y) \<noteq> {}) \<or>
    (des_vars.ok\<^sub>v y \<and>
     astate.s\<^sub>v (des_vars.more x) \<in> achoices.ac\<^sub>v (des_vars.more y)))"
  by (simp add: II_Rac_def RA1_def Let_def; pred_auto)

lemma RA1_not_ok_eval:
  "RA1 (\<not> ok\<^sup><) (x, y) \<longleftrightarrow>
   (\<not> des_vars.ok\<^sub>v x \<and>
    rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
      achoices.ac\<^sub>v (des_vars.more y) \<noteq> {})"
  by (simp add: RA1_def Let_def; pred_auto)

lemma RA3_eval:
  "RA3 P (x, y) \<longleftrightarrow>
   (if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
    then II_Rac (x, y) else P (x, y))"
  by (simp add: RA3_def expr_if_def SEXP_def lens_defs
      rad_state.wait_def astate.s_def des_vars.more\<^sub>L_def)

lemma RA3_healthy_wait_eval:
  assumes "P is RA3" "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))"
  shows "P (x, y) \<longleftrightarrow> II_Rac (x, y)"
proof -
  have h: "RA3 P = P"
    using assms(1) by (simp add: Healthy_def')
  have "P (x, y) \<longleftrightarrow> RA3 P (x, y)"
    by (simp only: h)
  also have "... \<longleftrightarrow> II_Rac (x, y)"
    using assms(2) by (simp add: RA3_eval)
  finally show ?thesis .
qed

subsection \<open>Trace Normalisation Support\<close>

lemma des_vars_more_update_self [simp]:
  "des_vars.more_update (\<lambda>_. des_vars.more r) r = r"
  by (cases r) simp

lemma achoices_ac_update_self [simp]:
  "achoices.ac\<^sub>v_update (\<lambda>_. achoices.ac\<^sub>v r) r = r"
  by (cases r) simp

lemma rad_trace_difference_prepend [simp]:
  "rad_trace_difference s0
     (rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m) = m"
  by (cases m) (simp add: rad_trace_difference_def)

lemma rad_trace_prepend_le [simp]:
  "rad_state.tr\<^sub>v s0 \<le>
   rad_state.tr\<^sub>v (rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m)"
  by (cases m) simp

lemma rad_trace_prepend_difference:
  assumes "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z"
  shows "rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr)
           (rad_trace_difference s0 z) = z"
  using assms
  by (cases z) (simp add: rad_trace_difference_def diff_add_cancel_left')

lemma rad_trace_prepend_inj:
  fixes s0 m m' :: "('t::trace, 'e) rad_state"
  assumes "rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m =
           rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m'"
  shows "m = m'"
proof -
  have "m = rad_trace_difference s0
              (rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m)"
    by (rule sym, rule rad_trace_difference_prepend)
  also have "... = rad_trace_difference s0
              (rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m')"
    by (simp only: assms)
  also have "... = m'"
    by (rule rad_trace_difference_prepend)
  finally show ?thesis .
qed

lemma rad_normalise_choices_mem_prepend:
  "m \<in> rad_normalise_choices s0 X \<longleftrightarrow>
   rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m \<in> X"
  by (simp add: rad_normalise_choices_as_prepend)

lemma rad_normalise_choices_prepend_image:
  "rad_normalise_choices s0
     ((\<lambda>m. rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v s0 + tr) m) ` X) = X"
  by (auto simp add: rad_normalise_choices_as_prepend image_iff
      dest: rad_trace_prepend_inj)

subsection \<open>RA1 Closure of Angelic-Design Parallel\<close>

lemma ades_par_RA1_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes P1: "P is RA1" and Q1: "Q is RA1"
    and jh: "j is RA1m" and jt: "A0j j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RA1"
proof (rule Healthy_intro, rule ext)
  fix w :: "('t, 'e) rad_state astate des_vars_ext \<times>
            ('t, 'e) rad_state achoices des_vars_ext"
  obtain x y where w_eq [simp]: "w = (x, y)"
    by (cases w) auto
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  let ?ext = "rad_trace_extensions ?s0"
  let ?A = "achoices.ac\<^sub>v (des_vars.more y)"
  let ?y' = "des_vars.more_update
    (\<lambda>_. achoices.ac\<^sub>v_update (\<lambda>_. ?ext \<inter> ?A) (des_vars.more y)) y"
  show "RA1 ?R w = ?R w"
  proof
    assume "RA1 ?R w"
    then have Ry': "?R (x, ?y')" and ne: "?ext \<inter> ?A \<noteq> {}"
      by (simp_all add: RA1_def Let_def)
    from Ry'[unfolded ades_par_eval] obtain p q where
      Pp: "P (x, p)" and Qq: "Q (x, q)" and
      ok_eq: "des_vars.ok\<^sub>v ?y' = (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q)" and
      img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
              j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                  mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
            \<subseteq> achoices.ac\<^sub>v (des_vars.more ?y')"
      by blast
    show "?R w"
      unfolding w_eq ades_par_eval
      apply (rule exI[of _ p], rule exI[of _ q])
      using Pp Qq ok_eq img by auto
  next
    assume R: "?R w"
    from R[unfolded w_eq ades_par_eval] obtain p q where
      Pp: "P (x, p)" and Qq: "Q (x, q)" and
      ok_eq: "des_vars.ok\<^sub>v y = (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q)" and
      img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
              j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                  mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
            \<subseteq> ?A"
      by blast
    have img_ext: "\<And>z a b.
        \<lbrakk> a \<in> achoices.ac\<^sub>v (des_vars.more p);
          b \<in> achoices.ac\<^sub>v (des_vars.more q);
          j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
              mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z) \<rbrakk> \<Longrightarrow>
        z \<in> ?ext"
    proof -
      fix z a b
      assume "j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                  mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)"
      then have "rad_state.tr\<^sub>v ?s0 \<le> rad_state.tr\<^sub>v z"
        using RA1m_healthy_dest[OF jh] by fastforce
      then show "z \<in> ?ext"
        by (simp add: rad_trace_extensions_def)
    qed
    have ap_ne: "achoices.ac\<^sub>v (des_vars.more p) \<noteq> {}"
      using RA1_healthy_non_empty[OF P1 Pp] by auto
    have aq_ne: "achoices.ac\<^sub>v (des_vars.more q) \<noteq> {}"
      using RA1_healthy_non_empty[OF Q1 Qq] by auto
    obtain a where a: "a \<in> achoices.ac\<^sub>v (des_vars.more p)"
      using ap_ne by auto
    obtain b where b: "b \<in> achoices.ac\<^sub>v (des_vars.more q)"
      using aq_ne by auto
    obtain z where jz:
        "j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
             mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)"
      using jt unfolding A0j_def by blast
    have z_A: "z \<in> ?A"
      using a b jz img by blast
    have z_ext: "z \<in> ?ext"
      by (rule img_ext[OF a b jz])
    have ne: "?ext \<inter> ?A \<noteq> {}"
      using z_A z_ext by blast
    have Ry': "?R (x, ?y')"
      unfolding ades_par_eval
      apply (rule exI[of _ p], rule exI[of _ q])
      using Pp Qq ok_eq img img_ext by auto
    show "RA1 ?R w"
      unfolding w_eq by (simp add: RA1_def Let_def Ry' ne)
  qed
qed

subsection \<open>RA2 Closure of Angelic-Design Parallel\<close>

lemma ades_par_RA2_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes P2: "P is RA2" and Q2: "Q is RA2" and jh: "j is RA2m"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RA2"
proof (rule Healthy_intro, rule ext)
  fix w :: "('t, 'e) rad_state astate des_vars_ext \<times>
            ('t, 'e) rad_state achoices des_vars_ext"
  obtain x y where w_eq [simp]: "w = (x, y)"
    by (cases w) auto
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  let ?A = "achoices.ac\<^sub>v (des_vars.more y)"
  let ?x0 = "des_vars.more_update
    (\<lambda>_. astate.s\<^sub>v_update (\<lambda>_. rad_zero_trace ?s0) (des_vars.more x)) x"
  let ?yn = "des_vars.more_update
    (\<lambda>_. achoices.ac\<^sub>v_update
       (\<lambda>_. rad_normalise_choices ?s0 ?A) (des_vars.more y)) y"
  show "RA2 ?R w = ?R w"
  proof
    assume "RA2 ?R w"
    then have R0: "?R (?x0, ?yn)"
      by (simp add: RA2_def Let_def)
    from R0[unfolded ades_par_eval] obtain p' q' where
      Pp': "P (?x0, p')" and Qq': "Q (?x0, q')" and
      ok': "des_vars.ok\<^sub>v ?yn = (des_vars.ok\<^sub>v p' \<and> des_vars.ok\<^sub>v q')" and
      img0: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p').
                 \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q').
               j (\<lparr>mrg_prior\<^sub>v = astate.s\<^sub>v (des_vars.more ?x0),
                   mrg_left\<^sub>v = a, mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
             \<subseteq> achoices.ac\<^sub>v (des_vars.more ?yn)"
      by blast
    have img0': "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p').
                     \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q').
                   j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace ?s0,
                       mrg_left\<^sub>v = a, mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
             \<subseteq> rad_normalise_choices ?s0 ?A"
      using img0 by simp
    let ?ph = "des_vars.more_update
      (\<lambda>_. achoices.ac\<^sub>v_update
         (\<lambda>_. (\<lambda>m. rad_state.tr\<^sub>v_update
                 (\<lambda>tr. rad_state.tr\<^sub>v ?s0 + tr) m) `
              achoices.ac\<^sub>v (des_vars.more p'))
         (des_vars.more p')) p'"
    let ?qh = "des_vars.more_update
      (\<lambda>_. achoices.ac\<^sub>v_update
         (\<lambda>_. (\<lambda>m. rad_state.tr\<^sub>v_update
                 (\<lambda>tr. rad_state.tr\<^sub>v ?s0 + tr) m) `
              achoices.ac\<^sub>v (des_vars.more q'))
         (des_vars.more q')) q'"
    have Pph: "P (x, ?ph)"
    proof -
      have "P (x, ?ph) \<longleftrightarrow> P (?x0, p')"
        using RA2_healthy_eval[OF P2, of x ?ph]
        by (simp add: rad_normalise_choices_prepend_image)
      with Pp' show ?thesis by simp
    qed
    have Qqh: "Q (x, ?qh)"
    proof -
      have "Q (x, ?qh) \<longleftrightarrow> Q (?x0, q')"
        using RA2_healthy_eval[OF Q2, of x ?qh]
        by (simp add: rad_normalise_choices_prepend_image)
      with Qq' show ?thesis by simp
    qed
    have okh: "des_vars.ok\<^sub>v y = (des_vars.ok\<^sub>v ?ph \<and> des_vars.ok\<^sub>v ?qh)"
      using ok' by simp
    have imgh: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more ?ph).
                    \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more ?qh).
                  j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                      mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)} \<subseteq> ?A"
    proof (intro subsetI)
      fix z
      assume "z \<in> {z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more ?ph).
                       \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more ?qh).
                     j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                         mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}"
      then obtain a b where
        a: "a \<in> achoices.ac\<^sub>v (des_vars.more ?ph)" and
        b: "b \<in> achoices.ac\<^sub>v (des_vars.more ?qh)" and
        jz: "j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                 mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)"
        by blast
      from a obtain a0 where
        a0: "a0 \<in> achoices.ac\<^sub>v (des_vars.more p')" and
        a_eq: "a = rad_state.tr\<^sub>v_update
                     (\<lambda>tr. rad_state.tr\<^sub>v ?s0 + tr) a0"
        by auto
      from b obtain b0 where
        b0: "b0 \<in> achoices.ac\<^sub>v (des_vars.more q')" and
        b_eq: "b = rad_state.tr\<^sub>v_update
                     (\<lambda>tr. rad_state.tr\<^sub>v ?s0 + tr) b0"
        by auto
      have both: "rad_state.tr\<^sub>v ?s0 \<le> rad_state.tr\<^sub>v z \<and>
          j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace ?s0,
              mrg_left\<^sub>v = rad_trace_difference ?s0 a,
              mrg_right\<^sub>v = rad_trace_difference ?s0 b, \<dots> = ()\<rparr>,
             rad_trace_difference ?s0 z)"
        by (rule RA2m_healthy_eval[OF jh, THEN iffD1, OF jz])
      then have le: "rad_state.tr\<^sub>v ?s0 \<le> rad_state.tr\<^sub>v z"
        by auto
      have jz0: "j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace ?s0,
                     mrg_left\<^sub>v = a0, mrg_right\<^sub>v = b0, \<dots> = ()\<rparr>,
                    rad_trace_difference ?s0 z)"
        using both by (simp add: a_eq b_eq)
      have "rad_trace_difference ?s0 z \<in> rad_normalise_choices ?s0 ?A"
        using jz0 a0 b0 img0' by blast
      then have "rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v ?s0 + tr)
                   (rad_trace_difference ?s0 z) \<in> ?A"
        by (simp add: rad_normalise_choices_mem_prepend)
      then show "z \<in> ?A"
        using rad_trace_prepend_difference[OF le] by simp
    qed
    show "?R w"
      unfolding w_eq ades_par_eval
      apply (rule exI[of _ ?ph], rule exI[of _ ?qh])
      using Pph Qqh okh imgh by auto
  next
    assume R: "?R w"
    from R[unfolded w_eq ades_par_eval] obtain p q where
      Pp: "P (x, p)" and Qq: "Q (x, q)" and
      ok_eq: "des_vars.ok\<^sub>v y = (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q)" and
      img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
              j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                  mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
            \<subseteq> ?A"
      by blast
    let ?pn = "des_vars.more_update
      (\<lambda>_. achoices.ac\<^sub>v_update
         (\<lambda>_. rad_normalise_choices ?s0
                (achoices.ac\<^sub>v (des_vars.more p)))
         (des_vars.more p)) p"
    let ?qn = "des_vars.more_update
      (\<lambda>_. achoices.ac\<^sub>v_update
         (\<lambda>_. rad_normalise_choices ?s0
                (achoices.ac\<^sub>v (des_vars.more q)))
         (des_vars.more q)) q"
    have Ppn: "P (?x0, ?pn)"
      by (rule RA2_healthy_eval[OF P2, THEN iffD1, OF Pp])
    have Qqn: "Q (?x0, ?qn)"
      by (rule RA2_healthy_eval[OF Q2, THEN iffD1, OF Qq])
    have okn: "des_vars.ok\<^sub>v ?yn = (des_vars.ok\<^sub>v ?pn \<and> des_vars.ok\<^sub>v ?qn)"
      using ok_eq by simp
    have imgn: "{z0. \<exists>a0 \<in> achoices.ac\<^sub>v (des_vars.more ?pn).
                     \<exists>b0 \<in> achoices.ac\<^sub>v (des_vars.more ?qn).
                   j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace ?s0,
                       mrg_left\<^sub>v = a0, mrg_right\<^sub>v = b0, \<dots> = ()\<rparr>, z0)}
              \<subseteq> rad_normalise_choices ?s0 ?A"
    proof (intro subsetI)
      fix z0
      assume "z0 \<in> {z0. \<exists>a0 \<in> achoices.ac\<^sub>v (des_vars.more ?pn).
                         \<exists>b0 \<in> achoices.ac\<^sub>v (des_vars.more ?qn).
                       j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace ?s0,
                           mrg_left\<^sub>v = a0, mrg_right\<^sub>v = b0, \<dots> = ()\<rparr>, z0)}"
      then obtain a0 b0 where
        a0: "a0 \<in> rad_normalise_choices ?s0
                    (achoices.ac\<^sub>v (des_vars.more p))" and
        b0: "b0 \<in> rad_normalise_choices ?s0
                    (achoices.ac\<^sub>v (des_vars.more q))" and
        jz0: "j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace ?s0,
                  mrg_left\<^sub>v = a0, mrg_right\<^sub>v = b0, \<dots> = ()\<rparr>, z0)"
        by auto
      from a0 obtain a where
        a: "a \<in> achoices.ac\<^sub>v (des_vars.more p)" and
        a_le: "rad_state.tr\<^sub>v ?s0 \<le> rad_state.tr\<^sub>v a" and
        a_eq: "a0 = rad_trace_difference ?s0 a"
        by (auto simp add: rad_normalise_choices_def)
      from b0 obtain b where
        b: "b \<in> achoices.ac\<^sub>v (des_vars.more q)" and
        b_le: "rad_state.tr\<^sub>v ?s0 \<le> rad_state.tr\<^sub>v b" and
        b_eq: "b0 = rad_trace_difference ?s0 b"
        by (auto simp add: rad_normalise_choices_def)
      let ?z = "rad_state.tr\<^sub>v_update (\<lambda>tr. rad_state.tr\<^sub>v ?s0 + tr) z0"
      have rhs: "rad_state.tr\<^sub>v ?s0 \<le> rad_state.tr\<^sub>v ?z \<and>
          j (\<lparr>mrg_prior\<^sub>v = rad_zero_trace ?s0,
              mrg_left\<^sub>v = rad_trace_difference ?s0 a,
              mrg_right\<^sub>v = rad_trace_difference ?s0 b, \<dots> = ()\<rparr>,
             rad_trace_difference ?s0 ?z)"
        using jz0 by (simp add: a_eq b_eq)
      have jzfull: "j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                        mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, ?z)"
        by (rule RA2m_healthy_eval[OF jh, THEN iffD2, OF rhs])
      have "?z \<in> ?A"
        using jzfull a b img by blast
      then show "z0 \<in> rad_normalise_choices ?s0 ?A"
        by (simp add: rad_normalise_choices_mem_prepend)
    qed
    have R0: "?R (?x0, ?yn)"
      unfolding ades_par_eval
      apply (rule exI[of _ ?pn], rule exI[of _ ?qn])
      using Ppn Qqn okn imgn by auto
    show "RA2 ?R w"
      unfolding w_eq by (simp add: RA2_def Let_def R0)
  qed
qed

subsection \<open>The Waiting Case and the RAD Operator\<close>

text \<open>
  Angelic-design parallel-by-merge is not \<open>RA3\<close>-closed, even for a totally
  healthy merge: at an unstarted waiting observation the composition forces
  the prior state into the combined choice set, whereas @{const II_Rac} only
  requires some trace-extending choice.  The identity @{const II_Rac} with
  the merge @{const skip\<^sub>m} witnesses the failure.
\<close>

lemma ades_par_RA3_counterexample:
  "\<not> (((II_Rac :: ('t::trace, 'e) reactive_angelic_design)
         \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> II_Rac) is RA3)"
proof (rule notI)
  let ?R = "(II_Rac :: ('t, 'e) reactive_angelic_design)
              \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub> II_Rac"
  assume h: "?R is RA3"
  define s0 :: "('t, 'e) rad_state" where
    "s0 = \<lparr>rad_state.tr\<^sub>v = 0, rad_state.ref\<^sub>v = {},
           rad_state.wait\<^sub>v = True, \<dots> = ()\<rparr>"
  define z0 :: "('t, 'e) rad_state" where
    "z0 = \<lparr>rad_state.tr\<^sub>v = 0, rad_state.ref\<^sub>v = {},
           rad_state.wait\<^sub>v = False, \<dots> = ()\<rparr>"
  define x where "x = \<lparr>ok\<^sub>v = False, s\<^sub>v = s0, \<dots> = ()\<rparr>"
  define y where "y = \<lparr>ok\<^sub>v = True, ac\<^sub>v = {z0}, \<dots> = ()\<rparr>"
  have eq: "RA3 ?R (x, y) \<longleftrightarrow> ?R (x, y)"
    using h by (simp add: Healthy_def')
  have wait_x: "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))"
    by (simp add: x_def s0_def)
  have lhs: "RA3 ?R (x, y)"
    by (simp add: RA3_eval wait_x II_Rac_eval x_def y_def s0_def z0_def
        rad_trace_extensions_def)
  have not_r: "\<not> ?R (x, y)"
  proof
    assume "?R (x, y)"
    from this[unfolded ades_par_eval] obtain p q where
      Pp: "II_Rac (x, p)" and Qq: "II_Rac (x, q)" and
      img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
              skip\<^sub>m (\<lparr>mrg_prior\<^sub>v = astate.s\<^sub>v (des_vars.more x),
                       mrg_left\<^sub>v = a, mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
            \<subseteq> achoices.ac\<^sub>v (des_vars.more y)"
      by blast
    have ap_ne: "achoices.ac\<^sub>v (des_vars.more p) \<noteq> {}"
      using Pp by (auto simp add: II_Rac_eval)
    have aq_ne: "achoices.ac\<^sub>v (des_vars.more q) \<noteq> {}"
      using Qq by (auto simp add: II_Rac_eval)
    obtain a where a: "a \<in> achoices.ac\<^sub>v (des_vars.more p)"
      using ap_ne by auto
    obtain b where b: "b \<in> achoices.ac\<^sub>v (des_vars.more q)"
      using aq_ne by auto
    have "s0 \<in> {z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                    \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
                  skip\<^sub>m (\<lparr>mrg_prior\<^sub>v = astate.s\<^sub>v (des_vars.more x),
                           mrg_left\<^sub>v = a, mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}"
      using a b by (auto simp add: skip_merge_eval x_def)
    then have "s0 \<in> achoices.ac\<^sub>v (des_vars.more y)"
      using img by blast
    then have "s0 = z0"
      by (simp add: y_def)
    then show False
      by (simp add: s0_def z0_def)
  qed
  from eq lhs not_r show False by simp
qed

text \<open>
  The reactive-angelic-design parallel operator therefore wraps the
  angelic-design composition in @{const CSPA1}, whose unstarted chaos
  disjunct is exactly the missing behaviour.  This mirrors the divergence
  disjunct of the reactive-design merge \<open>nmerge_rd\<close>.  Started observations
  are unaffected.
\<close>

definition rad_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) rad_state merge \<Rightarrow>
   ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where [pred]: "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = CSPA1 (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)"

lemma rad_par_comm:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P"
  by (simp only: rad_par_def ades_par_comm[OF assms])

lemma rad_par_PBMH_ades [closure]:
  "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is PBMH_ades"
  unfolding rad_par_def
  by (rule Healthy_intro, rule CSPA1_PBMH_ades_closure,
      rule ades_par_is_PBMH_ades[unfolded Healthy_def'])

lemma rad_par_CSPA1_closure [closure]:
  "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is CSPA1"
  by (simp add: rad_par_def Healthy_def' CSPA1_idem)

lemma CSPA1_closure_transfer:
  fixes H :: "('t::trace, 'e) reactive_angelic_design \<Rightarrow>
              ('t, 'e) reactive_angelic_design"
    and R :: "('t, 'e) reactive_angelic_design"
  assumes dist: "\<And>A B. H (A \<or> B) = (H A \<or> H B)"
    and raw: "H R = R"
    and unstarted: "H (RA1 (\<not> ok\<^sup><)) = RA1 (\<not> ok\<^sup><)"
  shows "CSPA1 R is H"
proof -
  have "H (CSPA1 R) = (H R \<or> H (RA1 (\<not> ok\<^sup><)))"
    by (simp add: CSPA1_def dist)
  also have "... = CSPA1 R"
    by (simp add: CSPA1_def raw unstarted)
  finally show ?thesis by (simp add: Healthy_def')
qed

lemma rad_par_RA1_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is RA1" "Q is RA1" "j is RA1m" "A0j j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RA1"
  unfolding rad_par_def
  by (rule CSPA1_closure_transfer, rule RA1_disj,
      rule ades_par_RA1_closure[OF assms, unfolded Healthy_def'],
      simp add: RA1_idem)

lemma rad_par_RA2_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is RA2" "Q is RA2" "j is RA2m"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RA2"
  unfolding rad_par_def
  by (rule CSPA1_closure_transfer, rule RA2_disj,
      rule ades_par_RA2_closure[OF assms, unfolded Healthy_def'],
      simp only: RA1_RA2_commute'[symmetric] RA2_not_ok_expr)

lemma rad_par_RA3_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes P3: "P is RA3" and Q3: "Q is RA3" and jh: "j is RA3m"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RA3"
proof (rule Healthy_intro, rule ext)
  fix w :: "('t, 'e) rad_state astate des_vars_ext \<times>
            ('t, 'e) rad_state achoices des_vars_ext"
  obtain x y where w_eq [simp]: "w = (x, y)"
    by (cases w) auto
  let ?W = "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  let ?A = "achoices.ac\<^sub>v (des_vars.more y)"
  show "RA3 ?W w = ?W w"
  proof (cases "rad_state.wait\<^sub>v ?s0")
    case False
    then show ?thesis
      by (simp add: RA3_eval)
  next
    case True
    have W_eval: "?W (x, y) \<longleftrightarrow> (?R (x, y) \<or> RA1 (\<not> ok\<^sup><) (x, y))"
      by (simp add: rad_par_def CSPA1_def; pred_auto)
    have jw: "\<And>a b z.
        j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
            mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z) \<longleftrightarrow> z = ?s0"
      by (simp add: RA3m_healthy_wait[OF jh] True)
    have Pw: "\<And>p. P (x, p) \<longleftrightarrow> II_Rac (x, p)"
      by (rule RA3_healthy_wait_eval[OF P3 True])
    have Qw: "\<And>q. Q (x, q) \<longleftrightarrow> II_Rac (x, q)"
      by (rule RA3_healthy_wait_eval[OF Q3 True])
    have RIff: "?R (x, y) \<longleftrightarrow>
        (?s0 \<in> ?A \<and> (des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v y))"
    proof
      assume "?R (x, y)"
      from this[unfolded ades_par_eval] obtain p q where
        Pp: "P (x, p)" and Qq: "Q (x, q)" and
        ok_eq: "des_vars.ok\<^sub>v y = (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q)" and
        img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                  \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
                j (\<lparr>mrg_prior\<^sub>v = ?s0, mrg_left\<^sub>v = a,
                    mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
              \<subseteq> ?A"
        by blast
      have IIp: "II_Rac (x, p)"
        using Pp by (simp add: Pw)
      have IIq: "II_Rac (x, q)"
        using Qq by (simp add: Qw)
      have ap_ne: "achoices.ac\<^sub>v (des_vars.more p) \<noteq> {}"
        using IIp by (auto simp add: II_Rac_eval)
      have aq_ne: "achoices.ac\<^sub>v (des_vars.more q) \<noteq> {}"
        using IIq by (auto simp add: II_Rac_eval)
      obtain a where a: "a \<in> achoices.ac\<^sub>v (des_vars.more p)"
        using ap_ne by auto
      obtain b where b: "b \<in> achoices.ac\<^sub>v (des_vars.more q)"
        using aq_ne by auto
      have s0A: "?s0 \<in> ?A"
        using a b img by (auto simp add: jw)
      have okimp: "des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v y"
      proof
        assume okx: "des_vars.ok\<^sub>v x"
        have "des_vars.ok\<^sub>v p"
          using IIp okx by (auto simp add: II_Rac_eval)
        moreover have "des_vars.ok\<^sub>v q"
          using IIq okx by (auto simp add: II_Rac_eval)
        ultimately show "des_vars.ok\<^sub>v y"
          by (simp add: ok_eq)
      qed
      show "?s0 \<in> ?A \<and> (des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v y)"
        using s0A okimp by simp
    next
      assume rhs: "?s0 \<in> ?A \<and> (des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v y)"
      let ?p = "\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v y, ac\<^sub>v = {?s0}, \<dots> = ()\<rparr>"
      let ?q = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s0}, \<dots> = ()\<rparr>"
      have II1: "II_Rac (x, ?p)"
        using rhs by (auto simp add: II_Rac_eval)
      have II2: "II_Rac (x, ?q)"
        by (auto simp add: II_Rac_eval)
      have Pwit: "P (x, ?p)"
        using II1 by (simp add: Pw)
      have Qwit: "Q (x, ?q)"
        using II2 by (simp add: Qw)
      show "?R (x, y)"
        unfolding ades_par_eval
        apply (rule exI[of _ ?p], rule exI[of _ ?q])
        using Pwit Qwit rhs by (auto simp add: jw)
    qed
    have IIiff: "II_Rac (x, y) \<longleftrightarrow> ?W (x, y)"
      by (auto simp add: W_eval RA1_not_ok_eval RIff II_Rac_eval
          disjoint_iff intro: exI[of _ "?s0"])
    show ?thesis
      using True by (simp add: RA3_eval IIiff)
  qed
qed

subsection \<open>Interaction with H2\<close>

lemma H2_disj: "H2 (P \<or> Q) = (H2 P \<or> H2 Q)"
  by (simp add: H2_split fun_eq_iff; pred_auto)

lemma H2_not_ok:
  "H2 ((\<not> ok\<^sup><) :: ('t::trace, 'e) reactive_angelic_design) = (\<not> ok\<^sup><)"
  by (simp add: H2_split fun_eq_iff; pred_auto)

lemma H2_RA1_commute: "H2 (RA1 P) = RA1 (H2 P)"
  by (simp add: H2_split RA1_def fun_eq_iff Let_def; pred_auto; blast)

lemma H2_RA2_commute: "H2 (RA2 P) = RA2 (H2 P)"
  by (simp add: H2_split RA2_def fun_eq_iff Let_def; pred_auto)

lemma H2_RA3_commute: "H2 (RA3 P) = RA3 (H2 P)"
  by (simp add: H2_split RA3_def II_Rac_def RA1_def expr_if_def
      fun_eq_iff Let_def; pred_auto; blast)

lemma H2_CSPA1_commute: "H2 (CSPA1 P) = CSPA1 (H2 P)"
proof -
  have "H2 (CSPA1 P) = (H2 P \<or> H2 (RA1 (\<not> ok\<^sup><)))"
    by (simp add: CSPA1_def H2_disj)
  also have "... = (H2 P \<or> RA1 (H2 (\<not> ok\<^sup><)))"
    by (simp only: H2_RA1_commute)
  also have "... = (H2 P \<or> RA1 (\<not> ok\<^sup><))"
    by (simp only: H2_not_ok)
  also have "... = CSPA1 (H2 P)"
    by (simp add: CSPA1_def)
  finally show ?thesis .
qed

lemma RAD_is_CSPA2 [closure]:
  assumes "P is RAD"
  shows "P is CSPA2"
proof -
  have h: "CSPA2 (RAD P) = RAD P"
    by (simp only: CSPA2_def RAD_def RA_def comp_apply H2_RA1_commute
        H2_RA2_commute H2_RA3_commute H2_CSPA1_commute H2_idem)
  show ?thesis
    using assms[unfolded Healthy_def'] unfolding Healthy_def'
    by (rule fix_transfer[where F = CSPA2 and K = RAD, OF h])
qed

subsection \<open>RA Projections\<close>

lemma RA_is_RA1:
  assumes "P is RA"
  shows "P is RA1"
proof -
  have "RA1 (RA2 (RA3 P)) = P"
    using assms by (simp add: Healthy_def' RA_def)
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[OF RA1_idem])
qed

lemma RA_is_RA2:
  assumes "P is RA"
  shows "P is RA2"
proof -
  have h: "RA1 (RA2 (RA3 P)) = P"
    using assms by (simp add: Healthy_def' RA_def)
  have "RA2 (RA1 (RA3 P)) = RA1 (RA2 (RA3 P))"
    by (rule RA1_RA2_commute'[symmetric])
  also have "... = P" by (rule h)
  finally have "RA2 (RA1 (RA3 P)) = P" .
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[OF RA2_idem])
qed

lemma RA_is_RA3:
  assumes "P is RA"
  shows "P is RA3"
proof -
  have h: "RA1 (RA2 (RA3 P)) = P"
    using assms by (simp add: Healthy_def' RA_def)
  have "RA3 (RA1 (RA2 P)) = RA1 (RA3 (RA2 P))"
    by (simp only: RA1_RA3_commute'[symmetric])
  also have "... = RA1 (RA2 (RA3 P))"
    by (simp only: RA2_RA3_commute'[symmetric])
  also have "... = P" by (rule h)
  finally have "RA3 (RA1 (RA2 P)) = P" .
  then show ?thesis
    unfolding Healthy_def' by (rule idem_fix_extract[OF RA3_idem])
qed

subsection \<open>RAD Closure\<close>

lemma rad_par_RA_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is RA" "Q is RA" "j is RADM" "A0j j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RA"
proof -
  let ?W = "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  have w1: "RA1 ?W = ?W"
    using rad_par_RA1_closure[OF RA_is_RA1[OF assms(1)]
        RA_is_RA1[OF assms(2)] RADM_implies_RA1m[OF assms(3)] assms(4)]
    by (simp add: Healthy_def')
  have w2: "RA2 ?W = ?W"
    using rad_par_RA2_closure[OF RA_is_RA2[OF assms(1)]
        RA_is_RA2[OF assms(2)] RADM_implies_RA2m[OF assms(3)]]
    by (simp add: Healthy_def')
  have w3: "RA3 ?W = ?W"
    using rad_par_RA3_closure[OF RA_is_RA3[OF assms(1)]
        RA_is_RA3[OF assms(2)] RADM_implies_RA3m[OF assms(3)]]
    by (simp add: Healthy_def')
  have "RA ?W = RA1 (RA2 (RA3 ?W))"
    by (simp add: RA_def)
  also have "... = ?W"
    by (simp only: w3 w2 w1)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma rad_par_RAD_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is RAD" "Q is RAD" "j is RADM" "A0j j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RAD"
proof -
  let ?W = "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  have PH2: "P is H2"
    using RAD_is_CSPA2[OF assms(1)]
    by (simp add: Healthy_def' CSPA2_def)
  have QH2: "Q is H2"
    using RAD_is_CSPA2[OF assms(2)]
    by (simp add: Healthy_def' CSPA2_def)
  have rawH2: "H2 ?R = ?R"
    using ades_par_H2_closure[OF PH2 QH2]
    by (simp add: Healthy_def')
  have wPBMH: "PBMH_ades ?W = ?W"
    using rad_par_PBMH_ades
    by (simp add: Healthy_def')
  have wH2: "CSPA2 ?W = ?W"
  proof -
    have "CSPA2 ?W = H2 (CSPA1 ?R)"
      by (simp add: CSPA2_def rad_par_def)
    also have "... = CSPA1 (H2 ?R)"
      by (rule H2_CSPA1_commute)
    also have "... = CSPA1 ?R"
      by (simp only: rawH2)
    also have "... = ?W"
      by (simp add: rad_par_def)
    finally show ?thesis .
  qed
  have wCSPA1: "CSPA1 ?W = ?W"
    using rad_par_CSPA1_closure
    by (simp add: Healthy_def')
  have wRA: "RA ?W = ?W"
    using rad_par_RA_closure[OF RAD_is_RA[OF assms(1)]
        RAD_is_RA[OF assms(2)] assms(3) assms(4)]
    by (simp add: Healthy_def')
  have "RAD ?W = RA (CSPA1 (CSPA2 (PBMH_ades ?W)))"
    by (simp add: RAD_def)
  also have "... = ?W"
    by (simp only: wPBMH wH2 wCSPA1 wRA)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

subsection \<open>A2 and A3 Closure\<close>

text \<open>
  The divergence disjunct of \<open>CSPA1\<close> is A2-healthy, so A2
  commutes with CSPA1. CSPA1 also preserves both design components and
  is absorbed by reactive designs, giving commutation with A3. These
  laws lift the angelic-design closure results to the wrapped operator.
\<close>

lemma CSPA1_preD:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "pre\<^sub>D (CSPA1 P) = pre\<^sub>D P"
  by (simp add: CSPA1_def; pred_auto)

lemma CSPA1_postD:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "post\<^sub>D (CSPA1 P) = post\<^sub>D P"
  by (simp add: CSPA1_def; pred_auto)

lemma CSPA1_rdesign:
  fixes C D :: "(('t::trace, 'e) rad_state) angelic_rel"
  shows "CSPA1 (C \<turnstile>\<^sub>r D) = (C \<turnstile>\<^sub>r D)"
  by (simp add: CSPA1_def; pred_auto)

lemma A2_CSPA1_commute:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "A2 (CSPA1 P) = CSPA1 (A2 P)"
  by (simp add: CSPA1_def A2_def RA1_def Let_def fun_eq_iff comp_def;
      pred_auto; blast)

lemma A3_CSPA1_commute:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  shows "A3 (CSPA1 P) = CSPA1 (A3 P)"
  by (simp add: A3_def CSPA1_preD CSPA1_postD CSPA1_rdesign)

lemma CSPA1_preserves_A2:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is A2"
  shows "CSPA1 P is A2"
  by (simp add: Healthy_def' A2_CSPA1_commute Healthy_if[OF assms])

lemma CSPA1_preserves_A3:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
  assumes "P is A3"
  shows "CSPA1 P is A3"
  by (simp add: Healthy_def' A3_CSPA1_commute Healthy_if[OF assms])

theorem rad_par_A2_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is \<^bold>H" "Q is \<^bold>H"
    and "(\<not> pre\<^sub>D P) is A2_rel" "post\<^sub>D P is A2_rel"
    and "(\<not> pre\<^sub>D Q) is A2_rel" "post\<^sub>D Q is A2_rel"
    and "A2j j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  unfolding rad_par_def
  apply (rule CSPA1_preserves_A2, rule ades_par_A2_closure)
  using assms(3-)
  by (auto simp only: A2_components_iff[OF assms(1)]
      A2_components_iff[OF assms(2)])

theorem rad_par_A3_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is \<^bold>H" "Q is \<^bold>H" "A3j j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  unfolding rad_par_def
  by (rule CSPA1_preserves_A3, rule ades_par_A3_closure[OF assms])

theorem rad_par_normal_A3_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  unfolding rad_par_def
  by (rule CSPA1_preserves_A3,
      rule ades_par_normal_A3_closure[OF assms])

end
