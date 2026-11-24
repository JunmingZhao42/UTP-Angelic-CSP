section \<open>The Choice-Set Lift\<close>

theory utp_ades_parallel_choice_lift
  imports utp_ades_parallel_laws
begin

text \<open>The choice-set lift of an ordinary merge, its canonicity, and its correspondence
  with design merges.\<close>

subsection \<open>Choice-set lifting\<close>

(* ac'_lift_merge N ((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
     (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. N((ok,s),(okL,sL),(okR,sR),(ok',s'))). *)
definition ac'_lift_merge :: "'s des_merge \<Rightarrow> 's ades_merge_rel" where
  "ac'_lift_merge N \<equiv>
    (\<forall>sL\<in>$0:\<^bold>v\<^sub>D:ac\<^sup><. \<forall>sR\<in>$1:\<^bold>v\<^sub>D:ac\<^sup><. \<exists>s'\<in>$\<^bold>v\<^sub>D:ac\<^sup>>.
      merge_eval \<guillemotleft>N\<guillemotright>
        \<lparr>ok\<^sub>v = $<:ok\<^sup><, \<dots> = $<:\<^bold>v\<^sub>D:s\<^sup><\<rparr>
        \<lparr>ok\<^sub>v = $0:ok\<^sup><, \<dots> = sL\<rparr>
        \<lparr>ok\<^sub>v = $1:ok\<^sup><, \<dots> = sR\<rparr>
        \<lparr>ok\<^sub>v = $ok\<^sup>>, \<dots> = s'\<rparr>)\<^sub>e"

lemma ac'_lift_merge_obs:
  "ades_merge_obs (ac'_lift_merge M) ok0 s0 okL acL okR acR ok' ac' =
    (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
      merge_eval M \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)"
  by (simp add: ac'_lift_merge_def; pred_auto)

lemma ABm_ac'_lift_merge_obs:
  "ades_merge_obs (ABm (ac'_lift_merge M)) ok0 s0 okL acL okR acR ok' ac' =
    (acL \<noteq> {} \<and> acR \<noteq> {} \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
      merge_eval M \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>))"
  by (simp add: ABm_obs[simplified] ac'_lift_merge_obs[simplified]; blast)

text \<open>The AD lift of a design merge completes after lifting, so divergence
  releases the final choice set, including to the empty set.\<close>

(* Before start, ordinary merging into Z, or divergence with unrestricted output. *)
lemma ac'_lift_merge_completion_obs:
  "ades_merge_obs (H3m (H1m (ABm (ac'_lift_merge M)))) ok0 s0 okL X okR Y ok' Z \<longleftrightarrow>
    (\<not> ok0 \<or>
     (X \<noteq> {} \<and> Y \<noteq> {} \<and>
       ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
           merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
             \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
             \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>) \<or>
        (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'.
           merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
             \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
             \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>))))"
  apply (simp only: H3m_ades_obs)
  apply (simp add: H1m_def disj_pred_def expr_defs lens_defs alpha_defs)
  apply (simp add: ABm_ac'_lift_merge_obs[simplified])
  by (cases ok0; simp; blast intro: exI[where x=UNIV])

subsubsection \<open>Canonicity of the shared lift\<close>

text \<open>We show the lift L(N) = ABm (ac'_lift_merge N) is canonical: every ABm merge M
  that refines it on singletons refines it everywhere, L(N) \<sqsubseteq> M.\<close>

(* M((ok,s),(okL,{sL}),(okR,{sR}),(ok',ac')) \<Longrightarrow>
     (\<exists>s'\<in>ac'. N((ok,s),(okL,sL),(okR,sR),(ok',s'))) *)
definition singleton_refines :: "'s des_merge \<Rightarrow> 's ades_merge_rel \<Rightarrow> bool" where
  "singleton_refines N M \<equiv> (\<forall>ok0 s0 okL sL okR sR ok' ac'.
    ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac' \<longrightarrow>
    (\<exists>s'\<in>ac'. merge_eval N
      \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>))"

(* L(N)((ok,s),(okL,{sL}),(okR,{sR}),(ok',ac')) =
     (\<exists>s'\<in>ac'. N((ok,s),(okL,sL),(okR,sR),(ok',s'))) *)
lemma choice_lift_singleton:
  "ades_merge_obs (ABm (ac'_lift_merge N)) ok0 s0 okL {sL} okR {sR} ok' ac' \<longleftrightarrow>
    (\<exists>s'\<in>ac'. merge_eval N
      \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
      \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
      \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)"
  by (simp only: ABm_ac'_lift_merge_obs) simp

subsubsection \<open>The universal property\<close>

(* singleton_refines N M \<Longrightarrow> L(N) \<sqsubseteq> M *)
lemma choice_lift_least:
  assumes healthy: "M is ABm" and refines: "singleton_refines N M"
  shows "ABm (ac'_lift_merge N) \<sqsubseteq> M"
proof -
  have "ades_merge_obs (ABm (ac'_lift_merge N)) ok0 s0 okL acL okR acR ok' ac'"
    if accepted: "ades_merge_obs M ok0 s0 okL acL okR acR ok' ac'"
    for ok0 s0 okL acL okR acR ok' ac'
  proof -
    have "acL \<noteq> {} \<and> acR \<noteq> {}"
      using accepted
      by (subst (asm) Healthy_if[OF healthy, symmetric]; simp add: ABm_obs[simplified])
    moreover have "ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' ac'"
      if "sL \<in> acL" "sR \<in> acR" for sL sR
      by (rule ABm_restrict[OF healthy _ _ _ _ accepted]; use that in auto)
    ultimately show ?thesis
      unfolding ABm_ac'_lift_merge_obs
      by (auto intro: refines[unfolded singleton_refines_def, rule_format])
  qed
  then show ?thesis by (simp add: pred_refine_iff; pred_auto)
qed

(* L(N) \<sqsubseteq> M \<longleftrightarrow> singleton_refines N M *)
theorem choice_lift_refine_iff:
  assumes "M is ABm"
  shows "ABm (ac'_lift_merge N) \<sqsubseteq> M \<longleftrightarrow> singleton_refines N M"
proof
  assume "ABm (ac'_lift_merge N) \<sqsubseteq> M"
  then show "singleton_refines N M"
    unfolding singleton_refines_def
    by (auto simp: pred_refine_iff simp flip: choice_lift_singleton)
qed (rule choice_lift_least[OF assms])

text \<open>So among ABm merges M with singleton_refines N M, the lift is the least refined.\<close>

subsubsection \<open>Parallel refinement\<close>

(* P \<parallel>[L(N)] Q \<sqsubseteq> P \<parallel>[M] Q *)
theorem par_choice_lift_canonical:
  assumes "M is ABm" "singleton_refines N M"
  shows "P \<parallel>\<^bsub>ABm (ac'_lift_merge N)\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>M\<^esub> Q"
  by (rule par_by_merge_mono_merge[OF choice_lift_least[OF assms]])

subsection \<open>Correspondence with Designs\<close>

lemma A_A2_pick:
  assumes "R is A" "R is A2" "X \<noteq> {}"
  shows "R (ades_obs b s0 c X) \<longleftrightarrow> (\<exists>x\<in>X. R (ades_obs b s0 c {x}))"
proof -
  have a2: "R (ades_obs b s0 c Y) \<longleftrightarrow>
      R (ades_obs b s0 c {}) \<or> (\<exists>y\<in>Y. R (ades_obs b s0 c {y}))" for Y
    using A2_obs[of R b s0 c Y] by (simp only: Healthy_if[OF assms(2)])
  have up: "R (ades_obs b s0 c {}) \<Longrightarrow> R (ades_obs b s0 c {y})" for y
    using PBMH_ades_obs[of R b s0 c "{y}"]
    by (simp only: Healthy_if[OF A_is_PBMH_ades[OF assms(1)]]; blast)
  show ?thesis
    using a2[of X] up assms(3) by blast
qed

lemma ades_par_by_merge_d2ac_ac2p:
  fixes M :: "'s des_merge" and AM :: "'s ades_merge_rel"
  assumes ops: "P is A" "Q is A" "P is A2" "Q is A2"
    and merge: "M is HDm" "M is H3m"
    and lift: "AM = H3m (H1m (ABm (ac'_lift_merge M)))"
  shows "P \<parallel>\<^bsub>AM\<^esub> Q = d2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
proof -
  have h1: "P is H1" "Q is H1"
    using ops(1,2) by (simp_all add: A_healthy_components_iff)
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use ops(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  have H: "(ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) is \<^bold>H"
    by (rule H_par_by_merge[OF H_implies_H1[OF designs_H(1)] H_implies_H1[OF designs_H(2)] merge(1)])
  have ex_des: "(\<exists>p. F p) = (\<exists>b s. F \<lparr>ok\<^sub>v = b, \<dots> = s\<rparr>)"
    for F :: "'s des_vars_ext \<Rightarrow> bool"
    by pred_auto
  have acP: "ac2p P (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) = P (ades_obs b s0 c {z})"
    and acQ: "ac2p Q (\<lparr>ok\<^sub>v = b, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = c, \<dots> = z\<rparr>) = Q (ades_obs b s0 c {z})"
    for b s0 c z
    by (simp_all add: ac2p_healthy_obs A_is_PBMH_ades ops(1,2))
  show ?thesis
  proof (rule ades_obs_ext)
    fix b s0 c Z
    show "(P \<parallel>\<^bsub>AM\<^esub> Q) (ades_obs b s0 c Z) =
        d2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) (ades_obs b s0 c Z)"
    proof (cases b)
      case False
      have p: "P (ades_obs False s0 c' X)" "Q (ades_obs False s0 c' X)" for c' X
        using h1 by (simp_all add: H1_healthy_obs_iff)
      have bF: "b = False"
        using False by simp
      show ?thesis
        unfolding bF
        apply (simp only: d2ac_healthy_obs[OF H] ades_par_by_merge_obs lift ac'_lift_merge_completion_obs simp_thms)
        using p by blast
    next
      case True
      define Ms where "Ms okL sL okR sR c' s' \<equiv> merge_eval M \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
        \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c', \<dots> = s'\<rparr>"
        for okL sL okR sR c' s'
      have rhs: "d2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) (ades_obs True s0 c Z) \<longleftrightarrow>
          (\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z) \<or>
          (\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z)"
        by (simp only: d2ac_healthy_obs[OF H] par_by_merge_eval ex_des acP acQ Ms_def simp_thms)
      have lhs: "(P \<parallel>\<^bsub>AM\<^esub> Q) (ades_obs True s0 c Z) \<longleftrightarrow>
          (\<exists>okL X okR Y. P (ades_obs True s0 okL X) \<and> Q (ades_obs True s0 okR Y) \<and>
            X \<noteq> {} \<and> Y \<noteq> {} \<and>
            ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s')))"
        proof -
          have witnesses: "(\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. F sL sR s') =
            (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'. F sL sR s')" for X Y and F :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
            by (blast intro: exI[where x=UNIV])
          show ?thesis
            by (simp only: ades_par_by_merge_obs lift ac'_lift_merge_completion_obs
                Ms_def simp_thms witnesses)
        qed
      have divM: "Ms okL sL okR sR False s' \<Longrightarrow> Ms okL sL okR sR False z" for okL sL okR sR s' z
        unfolding Ms_def by (rule H3m_diverge[OF merge(2)])
      have bT: "b = True"
        using True by simp
      show ?thesis
        unfolding bT lhs rhs
      proof (intro iffI)
        assume "\<exists>okL X okR Y. P (ades_obs True s0 okL X) \<and> Q (ades_obs True s0 okR Y) \<and>
            X \<noteq> {} \<and> Y \<noteq> {} \<and>
            ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s'))"
        then obtain okL X okR Y where
          p: "P (ades_obs True s0 okL X)" and q: "Q (ades_obs True s0 okR Y)"
          and ne: "X \<noteq> {}" "Y \<noteq> {}"
          and m: "(\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s')"
          by blast
        obtain sL where sL: "sL \<in> X" "P (ades_obs True s0 okL {sL})"
          using p A_A2_pick[OF ops(1,3) ne(1)] by blast
        obtain sR where sR: "sR \<in> Y" "Q (ades_obs True s0 okR {sR})"
          using q A_A2_pick[OF ops(2,4) ne(2)] by blast
        show "(\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z) \<or>
          (\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z)"
          using m sL sR divM by blast
      next
        assume "(\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z) \<or>
          (\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z)"
        then show "\<exists>okL X okR Y. P (ades_obs True s0 okL X) \<and> Q (ades_obs True s0 okR Y) \<and>
            X \<noteq> {} \<and> Y \<noteq> {} \<and>
            ((\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. Ms okL sL okR sR c s') \<or>
             (\<exists>W. \<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>W. Ms okL sL okR sR False s'))"
        proof (elim disjE)
          assume "\<forall>z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR False z"
          then obtain okL sL okR sR where "P (ades_obs True s0 okL {sL})"
              "Q (ades_obs True s0 okR {sR})" "Ms okL sL okR sR False undefined"
            by blast
          then show ?thesis
            by (intro exI[of _ okL] exI[of _ "{sL}"] exI[of _ okR] exI[of _ "{sR}"]) blast
        next
          assume "\<exists>z\<in>Z. \<exists>okL sL okR sR. P (ades_obs True s0 okL {sL}) \<and>
              Q (ades_obs True s0 okR {sR}) \<and> Ms okL sL okR sR c z"
          then obtain z okL sL okR sR where "z \<in> Z" "P (ades_obs True s0 okL {sL})"
              "Q (ades_obs True s0 okR {sR})" "Ms okL sL okR sR c z"
            by blast
          then show ?thesis
            by (intro exI[of _ okL] exI[of _ "{sL}"] exI[of _ okR] exI[of _ "{sR}"]) blast
        qed
      qed
    qed
  qed
qed

lemma ades_par_by_merge_ac2p:
  fixes M :: "'s des_merge" and AM :: "'s ades_merge_rel"
  assumes ops: "P is A" "Q is A" "P is A2" "Q is A2"
    and merge: "M is HDm" "M is H3m"
    and lift: "AM = H3m (H1m (ABm (ac'_lift_merge M)))"
  shows "ac2p (P \<parallel>\<^bsub>AM\<^esub> Q) = ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q"
proof -
  have designs_H: "ac2p P is \<^bold>H" "ac2p Q is \<^bold>H"
    by (rule ac2p_H_closure;
        use ops(1,2) A_is_H[of P] A_is_H[of Q] in \<open>auto simp: Healthy_def'\<close>)+
  show ?thesis
    by (simp only: ades_par_by_merge_d2ac_ac2p[OF assms] ac2p_d2ac[OF H_par_by_merge[OF
        H_implies_H1[OF designs_H(1)] H_implies_H1[OF designs_H(2)] merge(1)], simplified comp_apply])
qed

end
