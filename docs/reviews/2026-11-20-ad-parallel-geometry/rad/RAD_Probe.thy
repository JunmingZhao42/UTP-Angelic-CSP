theory RAD_Probe
  imports "UTP-Reactive-Angelic-Designs.utp_rad" "AD_Geometry_Probe.AD_Lift_Canonical"
begin

section \<open>Prefix observations from a started, non-waiting prior\<close>

(* a \<rightarrow> Skip may be observed waiting (trace unchanged, a not refused)
   or terminated (trace extended by a) *)
definition pobs :: "'e \<Rightarrow> ('e list, 'e) rad_state \<Rightarrow> ('e list, 'e) rad_state \<Rightarrow> bool" where
  "pobs a s0 y \<longleftrightarrow>
    (if rad_wait\<^sub>v y then rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y
     else rad_tr\<^sub>v y = rad_tr\<^sub>v s0 @ [a])"

lemma pobs_ext: "pobs a s0 y \<Longrightarrow> rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v y"
  unfolding pobs_def by (cases "rad_wait\<^sub>v y") auto

lemma PrefixSkip_RAD_obs:
  assumes "\<not> rad_wait\<^sub>v s0"
  shows "PrefixSkip_RAD a (ades_obs True s0 c X) \<longleftrightarrow> c \<and> (\<exists>y\<in>X. pobs a s0 y)"
  using assms
  apply (simp add: PrefixSkip_RAD_design RA1_obs rad_trace_extensions_def pobs_def; pred_auto)
  subgoal premises prems for y
  proof -
    have "pobs a s0 y" using prems(4,5) by (simp add: pobs_def)
    then have "rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v y" by (rule pobs_ext)
    with prems(3,6) show False by blast
  qed
  subgoal premises prems for y
  proof -
    have "rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v y" using prems(4) by simp
    with prems(3,7) show False by blast
  qed
  done


section \<open>Synchronising merge and parallel evaluation\<close>

(* CSP parallel synchronising on every event: the branch traces agree,
   and the merged refusal is the union of the branch refusals *)
definition jsync :: "('e list \<times> 'e set) merge" where
  "jsync = (\<lambda>(m, z). fst (mrg_left\<^sub>v m) = fst (mrg_right\<^sub>v m) \<and> fst z = fst (mrg_left\<^sub>v m) \<and>
                    snd z = snd (mrg_left\<^sub>v m) \<union> snd (mrg_right\<^sub>v m))"

lemma jsync_eval [simp]:
  "merge_eval jsync s0 p q z \<longleftrightarrow> fst p = fst q \<and> fst z = fst p \<and> snd z = snd p \<union> snd q"
  by (simp add: jsync_def)

lemma rad_par_obs:
  "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 c Z) \<longleftrightarrow>
    (\<exists>okL acL okR acR. P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>Z. merge_eval (merge_rdes j)
         \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>))"
  by (simp only: ades_par_by_merge_obs ac'_lift_merge_obs)

(* from a started, non-waiting prior with both branches stable, merge_rdes applies j
   to the trace contributions *)
lemma merge_rdes_started:
  assumes "\<not> rad_wait\<^sub>v s0"
  shows "merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr>
           \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr> \<longleftrightarrow>
    c \<and> rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR) \<and> rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
    merge_eval j (0, rad_ref\<^sub>v s0) (rad_tr\<^sub>v sL - rad_tr\<^sub>v s0, rad_ref\<^sub>v sL)
      (rad_tr\<^sub>v sR - rad_tr\<^sub>v s0, rad_ref\<^sub>v sR) (rad_tr\<^sub>v s' - rad_tr\<^sub>v s0, rad_ref\<^sub>v s')"
  using assms by (cases c; simp add: merge_rdes_eval)

section \<open>Trace facts\<close>

lemma pobs_diff:
  "pobs a s0 y \<Longrightarrow> rad_tr\<^sub>v y - rad_tr\<^sub>v s0 = [] \<or> rad_tr\<^sub>v y - rad_tr\<^sub>v s0 = [a]"
  unfolding pobs_def by (cases "rad_wait\<^sub>v y") (auto simp: minus_list_def)

lemma list_diff_nil: "(t0 :: 'e list) \<le> t \<Longrightarrow> t - t0 = [] \<Longrightarrow> t = t0"
  using diff_add_cancel_left'[of t0 t] by (simp add: plus_list_def)

(* a stable a-observation and a stable b-observation can only merge before either event *)
lemma sync_pair_stuck:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
    and L: "pobs a s0 yL" and R: "pobs b s0 yR"
    and M: "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr>
              \<lparr>ok\<^sub>v = True, \<dots> = yR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
  shows "rad_tr\<^sub>v s' = rad_tr\<^sub>v s0"
proof -
  from M[unfolded merge_rdes_started[OF s0]]
  have le: "rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s'"
    and eq: "rad_tr\<^sub>v yL - rad_tr\<^sub>v s0 = rad_tr\<^sub>v yR - rad_tr\<^sub>v s0"
    and out: "rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = rad_tr\<^sub>v yL - rad_tr\<^sub>v s0"
    by simp_all
  have "rad_tr\<^sub>v yL - rad_tr\<^sub>v s0 = []"
    using pobs_diff[OF L] pobs_diff[OF R] eq ab by auto
  with out have "rad_tr\<^sub>v s' - rad_tr\<^sub>v s0 = []" by simp
  with le show ?thesis by (rule list_diff_nil)
qed

section \<open>Probes\<close>

(* the terminated observation after a, refusing nothing *)
abbreviation done_a :: "'e \<Rightarrow> ('e list, 'e) rad_state \<Rightarrow> ('e list, 'e) rad_state" where
  "done_a a s0 \<equiv> rea_vars_ext False (rad_tr\<^sub>v s0 @ [a]) {}"

lemma pobs_done: "pobs a s0 (done_a a s0)"
  by (simp add: pobs_def)

(* with a partner that also does a, the composite can terminate after a *)
lemma rad_sync_progress:
  assumes s0: "\<not> rad_wait\<^sub>v s0"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a) (ades_obs True s0 True {done_a a s0})"
  unfolding rad_par_obs
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  using pobs_done[of a s0] s0
  by (simp add: PrefixSkip_RAD_obs merge_rdes_started minus_list_def)

(* a demonic partner does not block progress *)
lemma rad_sync_demonic_progress:
  assumes s0: "\<not> rad_wait\<^sub>v s0"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<sqinter>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
           (ades_obs True s0 True {done_a a s0})"
  unfolding rad_par_obs RAD_demonic_choice
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  using pobs_done[of a s0] s0
  by (simp add: PrefixSkip_RAD_obs merge_rdes_started minus_list_def disj_pred_def sup_fun_def sup_bool_def)

(* an angelic partner blocks progress: every offered set holds an observation before a or b *)
lemma rad_sync_angelic_stuck:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
    and P: "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
              (ades_obs True s0 c Z)"
  shows "\<exists>z\<in>Z. rad_tr\<^sub>v z = rad_tr\<^sub>v s0"
proof -
  from P obtain okL acL okR acR
    where L: "PrefixSkip_RAD a (ades_obs True s0 okL acL)"
      and R: "PrefixSkip_RAD a (ades_obs True s0 okR acR)" "PrefixSkip_RAD b (ades_obs True s0 okR acR)"
      and M: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>Z. merge_eval (merge_rdes jsync)
         \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    unfolding rad_par_obs RAD_angelic_choice by (auto simp: conj_pred_def inf_fun_def inf_bool_def)
  from L obtain yL where yL: "yL \<in> acL" "pobs a s0 yL" and okL: okL
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  from R(2) obtain yB where yB: "yB \<in> acR" "pobs b s0 yB" and okR: okR
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  have "\<exists>s'\<in>Z. merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr>
       \<lparr>ok\<^sub>v = True, \<dots> = yB\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    using bspec[OF bspec[OF M yL(1)] yB(1)] okL okR by simp
  then obtain s' where
    "s' \<in> Z" "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr>
       \<lparr>ok\<^sub>v = True, \<dots> = yB\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>" by (rule bexE)
  then show ?thesis using sync_pair_stuck[OF s0 ab yL(2) yB(2)] by blast
qed

lemma rad_sync_angelic_no_progress:
  assumes "\<not> rad_wait\<^sub>v s0" "a \<noteq> b"
  shows "\<not> (PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
           (ades_obs True s0 True {done_a a s0})"
proof
  assume "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
           (ades_obs True s0 True {done_a a s0})"
  from rad_sync_angelic_stuck[OF assms this] obtain z
    where "z \<in> {done_a a s0}" "rad_tr\<^sub>v z = rad_tr\<^sub>v s0" by (rule bexE)
  then show False by simp
qed


(* the composite is exactly "wait at the start, offering a": it never diverges and never
   performs a, so it behaves as a followed by Miracle *)
lemma rad_sync_angelic_eval:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
           (ades_obs True s0 c Z) \<longleftrightarrow>
         c \<and> (\<exists>y\<in>Z. rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y)"
proof
  assume P: "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
           (ades_obs True s0 c Z)"
  from P obtain okL acL okR acR
    where L: "PrefixSkip_RAD a (ades_obs True s0 okL acL)"
      and R: "PrefixSkip_RAD a (ades_obs True s0 okR acR)" "PrefixSkip_RAD b (ades_obs True s0 okR acR)"
      and M: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>Z. merge_eval (merge_rdes jsync)
         \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    unfolding rad_par_obs RAD_angelic_choice by (auto simp: conj_pred_def inf_fun_def inf_bool_def)
  from L obtain yL where yL: "yL \<in> acL" "pobs a s0 yL" and okL: okL
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  from R(1) obtain yA where yA: "yA \<in> acR" "pobs a s0 yA"
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  from R(2) obtain yB where yB: "yB \<in> acR" "pobs b s0 yB" and okR: okR
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  (* the left option merges with the right b-option, so it has not moved *)
  obtain s1 where "s1 \<in> Z" and m1: "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yB\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s1\<rparr>"
    using bspec[OF bspec[OF M yL(1)] yB(1)] okL okR by auto
  from m1[unfolded merge_rdes_started[OF s0]]
  have c and eqLB: "rad_tr\<^sub>v yL - rad_tr\<^sub>v s0 = rad_tr\<^sub>v yB - rad_tr\<^sub>v s0"
    by simp_all
  have incL: "rad_tr\<^sub>v yL - rad_tr\<^sub>v s0 = []"
    using pobs_diff[OF yL(2)] pobs_diff[OF yB(2)] eqLB ab by auto
  have wL: "rad_wait\<^sub>v yL" "a \<notin> rad_ref\<^sub>v yL"
    using yL(2) incL unfolding pobs_def by (auto split: if_splits simp: minus_list_def)
  (* the left option also merges with the right a-option, giving a waiting state that offers a *)
  obtain s2 where s2: "s2 \<in> Z" and m2: "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yA\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s2\<rparr>"
    using bspec[OF bspec[OF M yL(1)] yA(1)] okL okR by auto
  from m2[unfolded merge_rdes_started[OF s0]]
  have w2: "rad_wait\<^sub>v s2" and le2: "rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s2"
    and eqLA: "rad_tr\<^sub>v yL - rad_tr\<^sub>v s0 = rad_tr\<^sub>v yA - rad_tr\<^sub>v s0"
    and out2: "rad_tr\<^sub>v s2 - rad_tr\<^sub>v s0 = rad_tr\<^sub>v yL - rad_tr\<^sub>v s0"
    and ref2: "rad_ref\<^sub>v s2 = rad_ref\<^sub>v yL \<union> rad_ref\<^sub>v yA"
    using wL(1) by simp_all
  have "a \<notin> rad_ref\<^sub>v yA"
    using yA(2) eqLA incL unfolding pobs_def by (auto split: if_splits simp: minus_list_def)
  moreover have "rad_tr\<^sub>v s2 = rad_tr\<^sub>v s0"
    using list_diff_nil[OF le2] out2 incL by simp
  ultimately show "c \<and> (\<exists>y\<in>Z. rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y)"
    using \<open>c\<close> s2 w2 ref2 wL(2) by blast
next
  assume "c \<and> (\<exists>y\<in>Z. rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y)"
  then obtain w where c and w: "w \<in> Z" "rad_wait\<^sub>v w" "rad_tr\<^sub>v w = rad_tr\<^sub>v s0" "a \<notin> rad_ref\<^sub>v w"
    by blast
  (* pair w with a right option that waits at the start and refuses nothing *)
  let ?y0 = "rea_vars_ext True (rad_tr\<^sub>v s0) {} :: ('a list, 'a) rad_state"
  have pw: "pobs a s0 w" using w by (simp add: pobs_def)
  have p0: "pobs a s0 ?y0" "pobs b s0 ?y0" by (simp_all add: pobs_def)
  have m: "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = w\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = ?y0\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = w\<rparr>"
    using w \<open>c\<close> by (simp add: merge_rdes_started[OF s0] minus_list_def)
  show "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
           (ades_obs True s0 c Z)"
    unfolding rad_par_obs RAD_angelic_choice
    apply (rule exI[where x=True], rule exI[where x="{w}"])
    apply (rule exI[where x=True], rule exI[where x="{?y0}"])
    using pw p0 m w(1) s0
    by (simp add: PrefixSkip_RAD_obs conj_pred_def inf_fun_def inf_bool_def; blast)
qed

(* a followed by Miracle waits at the start offering a, and has no observation after a *)
lemma Prefix_RAD_top_obs:
  assumes s0: "\<not> rad_wait\<^sub>v s0"
  shows "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D) (ades_obs True s0 c Z) \<longleftrightarrow>
         c \<and> (\<exists>y\<in>Z. rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y)"
  unfolding Prefix_RAD_def angelic_design_seq_def
  by (auto simp: PrefixSkip_RAD_obs[OF s0] top_RAD_eval pobs_def split: if_splits)

(* so the composite is exactly a followed by Miracle *)
theorem rad_sync_angelic_miracle:
  assumes ab: "a \<noteq> b"
  shows "PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) =
         a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D"
proof (rule RAD_eq_active)
  show "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)) is RAD"
    by (intro rad_par_RAD RAD_angelic_closure PrefixSkip_RAD_is_RAD)
  show "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D) is RAD"
    by (rule Prefix_RAD_closure[OF RAD_healthy])
  show "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
          (ades_obs True s0 ok' Z) \<longleftrightarrow> (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D) (ades_obs True s0 ok' Z)"
    if "\<not> rad_wait\<^sub>v s0" for s0 ok' Z
    by (simp only: rad_sync_angelic_eval[OF that ab] Prefix_RAD_top_obs[OF that])
qed

(* the angel cannot use the demon's choice in the other branch either:
   demonic choice against angelic choice is still stuck *)
lemma rad_sync_demonic_angelic_stuck:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
    and P: "((PrefixSkip_RAD a \<sqinter>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub>
              (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)) (ades_obs True s0 c Z)"
  shows "\<exists>z\<in>Z. rad_tr\<^sub>v z = rad_tr\<^sub>v s0"
proof -
  from P obtain okL acL okR acR
    where L: "PrefixSkip_RAD a (ades_obs True s0 okL acL) \<or> PrefixSkip_RAD b (ades_obs True s0 okL acL)"
      and R: "PrefixSkip_RAD a (ades_obs True s0 okR acR)" "PrefixSkip_RAD b (ades_obs True s0 okR acR)"
      and M: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>Z. merge_eval (merge_rdes jsync)
         \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
    unfolding rad_par_obs RAD_angelic_choice RAD_demonic_choice
    by (auto simp: conj_pred_def inf_fun_def inf_bool_def disj_pred_def sup_fun_def sup_bool_def)
  from R(1) obtain yA where yA: "yA \<in> acR" "pobs a s0 yA" and okR: okR
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  from R(2) obtain yB where yB: "yB \<in> acR" "pobs b s0 yB"
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  have stuck: "\<exists>z\<in>Z. rad_tr\<^sub>v z = rad_tr\<^sub>v s0"
    if yL: "yL \<in> acL" "pobs e s0 yL" and yR: "yR \<in> acR" "pobs f s0 yR" and ef: "e \<noteq> f" and okL: okL
    for yL yR e f
  proof -
    have "\<exists>s'\<in>Z. merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr>
         \<lparr>ok\<^sub>v = True, \<dots> = yR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>"
      using bspec[OF bspec[OF M yL(1)] yR(1)] okL okR by simp
    then obtain s' where "s' \<in> Z" "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
         \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>" by (rule bexE)
    then show ?thesis using sync_pair_stuck[OF s0 ef yL(2) yR(2)] by blast
  qed
  from L show ?thesis
  proof
    assume "PrefixSkip_RAD a (ades_obs True s0 okL acL)"
    then obtain yL where "yL \<in> acL" "pobs a s0 yL" okL by (auto simp: PrefixSkip_RAD_obs[OF s0])
    then show ?thesis using stuck[OF _ _ yB ab] by blast
  next
    assume "PrefixSkip_RAD b (ades_obs True s0 okL acL)"
    then obtain yL where "yL \<in> acL" "pobs b s0 yL" okL by (auto simp: PrefixSkip_RAD_obs[OF s0])
    then show ?thesis using stuck[OF _ _ yA ab[symmetric]] by blast
  qed
qed

section \<open>Blocking holds for every admissible lift\<close>

(* any merge on choice sets that is antitone, needs nonempty branch sets, and merges
   single states no more than merge_rdes jsync still blocks the angelic partner *)
lemma rad_sync_angelic_stuck_any_lift:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
    and adm: "antitone_m M" "nonempty_m M" "sound_m (merge_rdes jsync) M"
    and P: "(PrefixSkip_RAD a \<parallel>\<^bsub>M\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
              (ades_obs True s0 c Z)"
  shows "\<exists>z\<in>Z. rad_tr\<^sub>v z = rad_tr\<^sub>v s0"
proof -
  have R: "PrefixSkip_RAD a \<parallel>\<^bsub>ac'_lift_merge (merge_rdes jsync)\<^esub>
             (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) \<sqsubseteq>
           PrefixSkip_RAD a \<parallel>\<^bsub>M\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)"
    by (rule par_lift_canonical[OF adm])
  from R[unfolded pred_refine_iff, rule_format, OF P]
  have "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
          (ades_obs True s0 c Z)" .
  then show ?thesis by (rule rad_sync_angelic_stuck[OF s0 ab])
qed

end

