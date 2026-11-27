section \<open>Angelic Process Lifted Merge\<close>

theory utp_ap_parallel_lifted_merge
  imports utp_ap_parallel_laws "UTP-Reactive-Angelic-Designs.utp_rad_parallel_algebra"
begin

text \<open>We define AP parallel directly on AP processes, as sequential composition is
  AD sequential composition on AP processes. The merge is the RAD merge with the
  completion of the AD merge and the AP waiting condition:
  merge_ap j = RA3APm (H3m (H1m (merge_rad j))).\<close>

subsection \<open>Construction and evaluation\<close>

(* merge_ap j = RA3APm (H3m (H1m (merge_rad j))),
   cf. merge_ades j = H3m (H1m (ac'_lift_merge (merge_des_raw j))) *)
definition merge_ap :: "('t::trace \<times> 'e set) merge \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "merge_ap j \<equiv> RA3APm (H3m (H1m (merge_rad j)))"

text \<open>Once a branch diverges, any output is allowed, as in AD, but the branch states
  must still merge.\<close>

lemma merge_ap_obs:
  "ades_merge_obs (merge_ap j) ok0 s0 okL X okR Y ok' Z \<longleftrightarrow>
    (if rad_wait\<^sub>v s0 then \<not> ok0 \<or> (ok' \<and> s0 \<in> Z)
     else \<not> ok0 \<or>
       (X \<noteq> {} \<and> Y \<noteq> {} \<and>
        ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
            merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
              \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
              \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>) \<or>
         (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'.
            merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
              \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
              \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>))))"
  by (cases "rad_wait\<^sub>v s0";
      simp only: merge_ap_def RA3APm_obs II_AP_obs
        ac'_lift_merge_completion_obs if_True if_False)

(* With both branches terminating, the merge is the RAD lift *)
lemma merge_ap_both_ok:
  assumes "\<not> rad_wait\<^sub>v s0"
  shows "ades_merge_obs (merge_ap j) True s0 True X True Y c Z \<longleftrightarrow>
    X \<noteq> {} \<and> Y \<noteq> {} \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
      merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr>
        \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>)"
proof -
  have "\<not> merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>" for sL sR s'
    by (simp add: merge_rdes_eval)
  then show ?thesis
    using assms by (simp only: merge_ap_obs if_False simp_thms; blast)
qed

(* Both branches terminate, so the output terminates with a trace extension *)
lemma merge_ap_active_ok:
  assumes "\<not> rad_wait\<^sub>v s0" "ades_merge_obs (merge_ap j) True s0 True X True Y c Z"
  shows "c \<and> rad_trace_extensions s0 \<inter> Z \<noteq> {}"
proof -
  obtain sL sR s' where "s' \<in> Z" and
    m: "merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr>
        \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    using assms(2) by (simp only: merge_ap_both_ok[OF assms(1)] ex_in_conv[symmetric]; blast)
  moreover have "c \<and> rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s'"
    using m assms(1) by (cases s0; cases s'; cases c; simp add: merge_rdes_eval)
  ultimately show ?thesis by (auto simp: rad_trace_extensions_def)
qed

subsection \<open>Merge healthiness\<close>

lemma merge_ap_H1m [closure]: "(merge_ap j :: ('t::trace, 'e) rad_merge_rel) is H1m"
proof -
  have h1m: "ades_merge_obs (H1m M) ok0 s0 okL X okR Y ok' Z \<longleftrightarrow>
      (\<not> ok0 \<or> ades_merge_obs M ok0 s0 okL X okR Y ok' Z)"
    for M :: "('t, 'e) rad_merge_rel" and ok0 s0 okL X okR Y ok' Z
    by (simp add: H1m_def; pred_auto)
  have un: "ades_merge_obs (merge_ap j) False s0 okL X okR Y ok' Z" for s0 okL X okR Y ok' Z
    by (simp only: merge_ap_obs; simp)
  show ?thesis
    unfolding Healthy_def'
    apply (rule ades_merge_ext)
    subgoal for ok0 s0 okL X okR Y ok' Z
      by (cases ok0; simp only: h1m un simp_thms)
    done
qed

lemma merge_ap_H2m [closure]: "merge_ap j is H2m"
proof -
  have rd2: "merge_rdes j is RD2"
    using merge_rdes_ORDm[of j] by (simp add: ORDm_healthy_iff)
  show ?thesis
    unfolding Healthy_def'
    apply (rule ades_merge_ext)
    subgoal for ok0 s0 okL X okR Y ok' Z
      by (cases "rad_wait\<^sub>v s0"; cases ok';
          simp only: H2m_ades_obs merge_ap_obs if_True if_False simp_thms;
          blast intro: RD2_ok_up[OF rd2])
    done
qed

lemma merge_ap_ADm [closure]: "(merge_ap j :: ('t::trace, 'e) rad_merge_rel) is ADm"
proof -
  have a0m: "ades_merge_obs (A0m M) ok0 s0 okL X okR Y ok' Z \<longleftrightarrow>
      (ades_merge_obs M ok0 s0 okL X okR Y ok' Z \<and>
       (ok0 \<and> ok' \<and> Z = {} \<longrightarrow> ades_merge_obs M ok0 s0 okL X okR Y False {}))"
    for M :: "('t, 'e) rad_merge_rel" and ok0 s0 okL X okR Y ok' Z
    by (simp add: A0m_eval)
  have a1m: "ades_merge_obs (A1m M) ok0 s0 okL X okR Y ok' Z \<longleftrightarrow>
      (\<not> ok0 \<or> (\<exists>W\<subseteq>Z. ades_merge_obs M ok0 s0 okL X okR Y False W) \<or>
       (ok' \<and> (\<exists>W\<subseteq>Z. ades_merge_obs M ok0 s0 okL X okR Y True W)))"
    for M :: "('t, 'e) rad_merge_rel" and ok0 s0 okL X okR Y ok' Z
    by (simp add: A1m_eval Let_def)
  have "merge_ap j is A0m" "merge_ap j is A1m"
    unfolding Healthy_def'
    by (rule ades_merge_ext; rename_tac ok0 s0 okL X okR Y ok' Z;
        case_tac "rad_wait\<^sub>v s0"; case_tac ok';
        simp only: a0m a1m merge_ap_obs if_True if_False simp_thms; blast)+
  then show ?thesis by (simp add: ADm_healthy_iff)
qed

lemma merge_ap_RA2APm [closure]:
  "(merge_ap j :: ('t::trace, 'e) rad_merge_rel) is RA2APm"
proof -
  have r2: "merge_rdes j is R2m"
    using merge_rdes_ORDm[of j] by (simp add: ORDm_healthy_iff)
  have univ: "rad_normalise_choices s0 UNIV = UNIV" for s0 :: "('t, 'e) rad_state"
    by (simp add: rad_normalise_choices_as_prepend)
  have img: "(\<forall>a\<in>f ` X. \<forall>b\<in>f ` Y. Q a b) \<longleftrightarrow> (\<forall>sL\<in>X. \<forall>sR\<in>Y. Q (f sL) (f sR))"
    for f :: "('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state" and X Y Q
    by blast
  show ?thesis
    unfolding Healthy_def'
  proof (rule ades_merge_ext)
    fix ok0 okL X okR Y ok' Z and s0 :: "('t, 'e) rad_state"
    let ?M = "merge_eval (merge_rdes j)"
    let ?f = "rad_trace_difference s0"
    have n: "(\<exists>s'\<in>Z. ?M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
          \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>) =
        (\<exists>s'\<in>rad_normalise_choices s0 Z. ?M \<lparr>ok\<^sub>v = True, \<dots> = rad_zero_trace s0\<rparr>
          \<lparr>ok\<^sub>v = okL, \<dots> = ?f sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = ?f sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)"
      for sL sR
      by (rule R2m_choice_normalise[OF r2])
    have nU0: "(\<exists>s'\<in>UNIV. ?M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
          \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>) =
        (\<exists>s'\<in>rad_normalise_choices s0 UNIV. ?M \<lparr>ok\<^sub>v = True, \<dots> = rad_zero_trace s0\<rparr>
          \<lparr>ok\<^sub>v = okL, \<dots> = ?f sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = ?f sR\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>)"
      for sL sR
      by (rule R2m_choice_normalise[OF r2])
    note nU = nU0[simplified bex_UNIV univ]
    show "ades_merge_obs (RA2APm (merge_ap j)) ok0 s0 okL X okR Y ok' Z =
        ades_merge_obs (merge_ap j) ok0 s0 okL X okR Y ok' Z"
      by (cases "rad_wait\<^sub>v s0";
          simp only: RA2APm_obs merge_ap_obs rad_zero_trace_wait if_True if_False
            rad_zero_trace_in_normalise image_is_empty img n nU)
  qed
qed

lemma merge_ap_RA3APm [closure]: "merge_ap j is RA3APm"
  by (simp add: Healthy_def' merge_ap_def RA3APm_idem)

lemma merge_ap_A2m [closure]: "merge_ap j is A2m"
  unfolding Healthy_def'
  apply (rule ades_merge_ext)
  subgoal for ok0 s0 okL X okR Y ok' Z
    by (cases ok0; cases "rad_wait\<^sub>v s0";
        simp only: A2m_obs merge_ap_obs if_True if_False simp_thms; simp; blast)
  done

lemma merge_ap_SymMerge:
  assumes "j is SymMerge"
  shows "merge_ap j is SymMerge"
proof -
  have sym: "merge_eval (merge_rdes j) x p q z = merge_eval (merge_rdes j) x q p z" for x p q z
    using merge_rdes_SymMerge[OF assms] by (simp add: SymMerge_eval)
  show ?thesis
    unfolding SymMerge_eval
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okL X okR Y ok' Z
      by (cases ok0; cases "rad_wait\<^sub>v s0";
          simp only: merge_ap_obs[unfolded case_prod_conv] if_True if_False simp_thms sym;
          blast)
    done
qed

subsection \<open>Associativity for all operands\<close>

text \<open>As for AD, a deterministic total state merge fixes the intermediate state,
  and a divergent branch releases the output, so we need no operand premise:
  (P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R).\<close>

lemma merge_ap_AssocMerge:
  fixes j :: "('t::trace \<times> 'e set) merge"
  assumes det: "Functional j" and tot: "mergeable j" and assoc: "AssocMerge j"
  shows "AssocMerge (merge_ap j)"
proof -
  let ?K = "\<lambda>s0 sL sR s'. merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
    \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>"
  have uniq: "u = v" if active: "\<not> rad_wait\<^sub>v s0" and merged: "?K s0 sL sR u" "?K s0 sL sR v"
    for s0 sL sR u v
  proof -
    have h: "(rad_tr\<^sub>v u - rad_tr\<^sub>v s0, rad_ref\<^sub>v u) = (rad_tr\<^sub>v v - rad_tr\<^sub>v s0, rad_ref\<^sub>v v)"
      by (rule det[unfolded Functional_merge_eval, rule_format, of "(0, rad_ref\<^sub>v s0)"
          "(rad_tr\<^sub>v sL - rad_tr\<^sub>v s0, rad_ref\<^sub>v sL)"
          "(rad_tr\<^sub>v sR - rad_tr\<^sub>v s0, rad_ref\<^sub>v sR)"])
        (use merged active in \<open>auto simp: merge_rdes_eval\<close>)
    show ?thesis using merged active h
      by (cases u; cases v; auto simp: merge_rdes_eval; metis diff_add_cancel_left')
  qed
  have ex: "\<exists>u. ?K s0 sL sR u" if a: "\<not> rad_wait\<^sub>v s0" for s0 sL sR
  proof -
    obtain z where z: "merge_eval j (0, rad_ref\<^sub>v s0) (rad_tr\<^sub>v sL - rad_tr\<^sub>v s0, rad_ref\<^sub>v sL)
        (rad_tr\<^sub>v sR - rad_tr\<^sub>v s0, rad_ref\<^sub>v sR) z"
      using tot by blast
    obtain t e where te: "z = (t, e)" by (cases z)
    have "?K s0 sL sR \<lparr>wait\<^sub>v = rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR, tr\<^sub>v = rad_tr\<^sub>v s0 + t, \<dots> = e\<rparr>"
      using a z te by (cases s0; cases sL; cases sR; simp add: merge_rdes_eval)
    then show ?thesis by blast
  qed
  (* a divergent branch pair always has a merged state *)
  have divm: "\<exists>s'. merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = a, \<dots> = sa\<rparr>
      \<lparr>ok\<^sub>v = b, \<dots> = sb\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>"
    if "\<not> rad_wait\<^sub>v s0" "\<not> (a \<and> b)" for s0 a b sa sb
  proof -
    obtain z where z: "merge_eval j (0, rad_ref\<^sub>v s0) (rad_tr\<^sub>v sa - rad_tr\<^sub>v s0, rad_ref\<^sub>v sa)
        (rad_tr\<^sub>v sb - rad_tr\<^sub>v s0, rad_ref\<^sub>v sb) z"
      using tot by blast
    obtain t e where te: "z = (t, e)" by (cases z)
    have "merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = a, \<dots> = sa\<rparr>
        \<lparr>ok\<^sub>v = b, \<dots> = sb\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = rad_tr\<^sub>v_update (\<lambda>_. rad_tr\<^sub>v s0 + t) s0\<rparr>"
      using that z te by (cases s0; cases sa; cases sb; simp add: merge_rdes_eval; blast intro: order_refl)
    then show ?thesis by blast
  qed
  define g where "g \<equiv> \<lambda>s0 sL sR. THE u. ?K s0 sL sR u"
  have gK: "?K s0 sL sR (g s0 sL sR)" if a: "\<not> rad_wait\<^sub>v s0" for s0 sL sR
    unfolding g_def by (rule theI', use ex[OF a] uniq[OF a] in blast)
  have g_char: "?K s0 sL sR u \<longleftrightarrow> u = g s0 sL sR" if a: "\<not> rad_wait\<^sub>v s0" for s0 sL sR u
    using gK[OF a] uniq[OF a] by blast
  have cyc: "(\<exists>u. ?K s0 sP sQ u \<and> ?K s0 u sR s') = (\<exists>u. ?K s0 sQ sR u \<and> ?K s0 u sP s')"
    if active: "\<not> rad_wait\<^sub>v s0" for s0 sP sQ sR s'
    using merge_rdes_guard_AssocMerge[OF assoc, unfolded AssocMerge_iff, rule_format,
      of "\<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>" "\<lparr>ok\<^sub>v = True, \<dots> = sP\<rparr>"
         "\<lparr>ok\<^sub>v = True, \<dots> = sQ\<rparr>" "\<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr>"
         "\<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>"] active
    by (simp add: merge_guard_eval des_vars.splits ex_bool_eq)
  have fcyc: "g s0 (g s0 sP sQ) sR = g s0 (g s0 sQ sR) sP" if a: "\<not> rad_wait\<^sub>v s0" for s0 sP sQ sR
  proof -
    have "\<exists>u. ?K s0 sP sQ u \<and> ?K s0 u sR (g s0 (g s0 sP sQ) sR)"
      using gK[OF a] by blast
    then have "\<exists>u. ?K s0 sQ sR u \<and> ?K s0 u sP (g s0 (g s0 sP sQ) sR)"
      by (rule cyc[OF a, THEN iffD1])
    then show ?thesis by (simp only: g_char[OF a]; blast)
  qed
  (* the started merge in closed form *)
  have started: "merge_eval (merge_ap j) \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>
      (ades_output okL X) (ades_output okR Y) (ades_output ok' Z) \<longleftrightarrow>
    X \<noteq> {} \<and> Y \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. g s0 sL sR \<in> Z))"
    if a: "\<not> rad_wait\<^sub>v s0" for s0 okL X okR Y ok' Z
  proof (cases "okL \<and> okR")
    case True
    then have ok: "okL" "okR" by simp_all
    have div: "\<not> merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr>
        \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>" for sL sR s'
      by (simp add: merge_rdes_eval)
    show ?thesis
      using merge_ap_both_ok[OF a, of j X Y ok' Z, unfolded case_prod_conv] div
      by (cases ok'; simp add: ok g_char[OF a] ex_in_conv; blast)
  next
    case False
    have B: "\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'. merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>"
      using divm[OF a False] by blast
    show ?thesis
      using B False a
      by (simp only: merge_ap_obs[unfolded case_prod_conv] if_False simp_thms; blast)
  qed
  (* the smallest middle set is the image of the first merge *)
  have middle:
    "(\<exists>okU acU. (acP \<noteq> {} \<and> acQ \<noteq> {} \<and> (okP \<and> okQ \<longrightarrow> okU \<and> (\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. h sP sQ \<in> acU))) \<and>
        (acU \<noteq> {} \<and> acR \<noteq> {} \<and> (okU \<and> okR \<longrightarrow> ok' \<and> (\<forall>u\<in>acU. \<forall>sR\<in>acR. h u sR \<in> Z)))) \<longleftrightarrow>
     acP \<noteq> {} \<and> acQ \<noteq> {} \<and> acR \<noteq> {} \<and>
     (okP \<and> okQ \<and> okR \<longrightarrow> ok' \<and> (\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. h (h sP sQ) sR \<in> Z))"
    (is "?L \<longleftrightarrow> ?R")
    for h :: "('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state"
      and acP acQ acR Z :: "('t, 'e) rad_state set" and okP okQ okR ok' :: bool
  proof
    assume ?L
    then show ?R by blast
  next
    assume r: ?R
    let ?acU = "{h sP sQ | sP sQ. sP \<in> acP \<and> sQ \<in> acQ}"
    have ne: "?acU \<noteq> {}" using r by fastforce
    show ?L
      by (rule exI[where x="okP \<and> okQ"], rule exI[where x="?acU"]) (use r ne in blast)
  qed
  (* one cyclic step; three steps return to the start *)
  have rot: "\<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<forall>sP\<in>acP. g s0 (g s0 sQ sR) sP \<in> Z"
    if h: "\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. g s0 (g s0 sP sQ) sR \<in> Z" and a: "\<not> rad_wait\<^sub>v s0"
    for s0 acP acQ acR Z
  proof (intro ballI)
    fix sQ sR sP assume "sQ \<in> acQ" "sR \<in> acR" "sP \<in> acP"
    then have "g s0 (g s0 sP sQ) sR \<in> Z" using h by blast
    then show "g s0 (g s0 sQ sR) sP \<in> Z" by (simp only: fcyc[OF a, of sP sQ sR])
  qed
  have rotate: "(\<forall>sP\<in>acP. \<forall>sQ\<in>acQ. \<forall>sR\<in>acR. g s0 (g s0 sP sQ) sR \<in> Z) \<longleftrightarrow>
      (\<forall>sQ\<in>acQ. \<forall>sR\<in>acR. \<forall>sP\<in>acP. g s0 (g s0 sQ sR) sP \<in> Z)"
    if a: "\<not> rad_wait\<^sub>v s0" for s0 acP acQ acR Z
    using rot[OF _ a, where acP=acP and acQ=acQ and acR=acR and Z=Z]
      rot[OF _ a, where acP=acQ and acQ=acR and acR=acP and Z=Z]
      rot[OF _ a, where acP=acR and acQ=acP and acR=acQ and Z=Z]
    by blast
  (* elsewhere the merge ignores the branches *)
  have inact: "\<forall>p q z. merge_eval (merge_ap j) \<lparr>ok\<^sub>v = ok0, s\<^sub>v = s0, \<dots> = ()\<rparr> p q z =
      II_AP (\<lparr>ok\<^sub>v = ok0, s\<^sub>v = s0, \<dots> = ()\<rparr>, z)"
    if i: "\<not> (ok0 \<and> \<not> rad_wait\<^sub>v s0)" for ok0 s0
    apply (intro allI)
    apply (unfold des_vars.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for okL X okR Y ok' Z
      using i by (cases ok0; cases "rad_wait\<^sub>v s0";
          simp add: merge_ap_obs[simplified] II_AP_obs[simplified])
    done
  show ?thesis
    unfolding AssocMerge_iff
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okP acP okQ acQ okR acR ok' ac'
    proof (cases "ok0 \<and> \<not> rad_wait\<^sub>v s0")
      case True
      then have ok0: "ok0" and a: "\<not> rad_wait\<^sub>v s0" by simp_all
      show ?thesis
        apply (simp only: ok0 choices_ex started[OF a] middle
            rotate[OF a, where acP=acP and acQ=acQ and acR=acR and Z=ac'])
        by auto
    next
      case False
      show ?thesis by (simp only: inact[OF False, rule_format])
    qed
    done
qed

subsection \<open>Associativity on nondivergent operands\<close>

text \<open>For a partial deterministic j we guard the merge to nondivergent branches,
  as for AD and RAD. At an active prior the guarded merge is that of RAD.\<close>

lemma merge_ap_guard_AssocMerge:
  fixes j :: "('t::trace \<times> 'e set) merge"
  assumes det: "Functional j" and assoc: "AssocMerge j"
  shows "AssocMerge (merge_guard
    (\<lambda>x z. des_vars.ok\<^sub>v x \<and> \<not> rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<longrightarrow> des_vars.ok\<^sub>v z)
    (merge_ap j))"
proof -
  let ?G = "\<lambda>x z. des_vars.ok\<^sub>v x \<and> \<not> rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<longrightarrow> des_vars.ok\<^sub>v z"
  let ?A = "merge_guard ?G (merge_ap j)" and ?R = "merge_guard ?G (merge_rad j)"
  have R: "AssocMerge ?R" by (rule merge_rad_guard_AssocMerge[OF det assoc])
  (* at an active prior the guarded merges agree *)
  have act: "\<forall>p q z. merge_eval ?A \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr> p q z =
      merge_eval ?R \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr> p q z" if a: "\<not> rad_wait\<^sub>v s0" for s0
    apply (intro allI)
    apply (unfold des_vars.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for okL X okR Y ok' Z
      using a merge_ap_both_ok[OF a, of j X Y ok' Z]
      by (cases okL; cases okR; simp add: merge_guard_eval ac'_lift_merge_obs[simplified])
    done
  (* elsewhere the guarded merge ignores the branches *)
  have inact: "\<forall>p q z. merge_eval ?A \<lparr>ok\<^sub>v = ok0, s\<^sub>v = s0, \<dots> = ()\<rparr> p q z =
      II_AP (\<lparr>ok\<^sub>v = ok0, s\<^sub>v = s0, \<dots> = ()\<rparr>, z)"
    if i: "\<not> (ok0 \<and> \<not> rad_wait\<^sub>v s0)" for ok0 s0
    apply (intro allI)
    apply (unfold des_vars.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for okL X okR Y ok' Z
      using i
      by (cases ok0; cases "rad_wait\<^sub>v s0";
          simp add: merge_guard_eval merge_ap_obs[simplified] II_AP_obs[simplified])
    done
  show ?thesis
    unfolding AssocMerge_iff
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okP acP okQ acQ okR acR ok' ac'
    proof (cases "ok0 \<and> \<not> rad_wait\<^sub>v s0")
      case True
      then have ok0: "ok0" and a: "\<not> rad_wait\<^sub>v s0" by simp_all
      show ?thesis
        using R[unfolded AssocMerge_iff, rule_format, of "\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>"
            "ades_output okP acP" "ades_output okQ acQ" "ades_output okR acR" "ades_output ok' ac'"]
        by (simp only: ok0 act[OF a, rule_format])
    next
      case False
      show ?thesis by (simp only: inact[OF False, rule_format])
    qed
    done
qed

end
