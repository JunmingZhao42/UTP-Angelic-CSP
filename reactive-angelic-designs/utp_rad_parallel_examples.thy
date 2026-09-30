section \<open>Basic Parallel Merge Examples\<close>

theory utp_rad_parallel_examples
  imports utp_rad_parallel utp_rad_ops
begin

subsection \<open>A singleton lifting of the basic reactive merge\<close>

text \<open>
  The trace policy follows the state-free instance of BasicMerge in
  UTP-Reactive-Designs.utp_rdes_parallel. Our alphabet has no separate ordinary
  state to frame. We additionally choose a disjunction for the waiting flags:
  both branch traces and the resulting trace agree, and the result waits when
  either branch waits.  Refusals are unconstrained.  These clauses are an
  explicit choice of merge policy, rather than part of the generic operator.

  The successful seed below requires singleton branch observations.  Merely
  selecting an element from each branch choice set would allow upward-closed
  operands to add arbitrary states and circumvent the trace policy.  This
  singleton lifting does not specify general multi-state angelic merging.
  The seed tests only branch and output observations with ok = True; waiting
  is handled separately. Healthiness supplies startup and waiting-prior
  behaviour. This example does not define general divergence propagation.
\<close>

definition basic_merge_state ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow>
   ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> bool"
where
  "basic_merge_state s0 l r z \<longleftrightarrow>
    rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
    rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v l \<and>
    rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v r \<and>
    rad_state.wait\<^sub>v z = (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r)"

definition basic_merge_seed :: "('t::trace, 'e) rad_merge_rel"
where
  "basic_merge_seed = (\<lambda>(m,out).
    des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
    des_vars.ok\<^sub>v (mrg_right\<^sub>v m) \<and> des_vars.ok\<^sub>v out \<and>
    (\<exists>l r z.
      achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)) = {l} \<and>
      achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m)) = {r} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      basic_merge_state (astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m))) l r z))"

lemma basic_merge_seed_eval:
  "ades_merge_eval basic_merge_seed x p q out \<longleftrightarrow>
    des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q \<and> des_vars.ok\<^sub>v out \<and>
    (\<exists>l r z. achoices.ac\<^sub>v (des_vars.more p) = {l} \<and>
      achoices.ac\<^sub>v (des_vars.more q) = {r} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      basic_merge_state (astate.s\<^sub>v (des_vars.more x)) l r z)"
  by (simp add: basic_merge_seed_def)

lemma basic_merge_seed_obs:
  "(\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs b s0 c X) \<longleftrightarrow>
    des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q \<and> c \<and>
    (\<exists>l r z. achoices.ac\<^sub>v (des_vars.more p) = {l} \<and>
      achoices.ac\<^sub>v (des_vars.more q) = {r} \<and>
      z \<in> X \<and> basic_merge_state s0 l r z)"
  by (simp add: basic_merge_seed_eval)

lemma basic_merge_seed_SymMerge: "basic_merge_seed is SymMerge"
  by (auto simp add: SymMerge_ades basic_merge_seed_eval basic_merge_state_def;
      blast)


lemma A_basic_merge_seed_obs:
  "(\<lambda>(x,out). ades_merge_eval (A0m (A1m basic_merge_seed)) x p q out) (ades_obs b s0 c X) =
    (\<not> b \<or> (\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs b s0 c X))"
  by (auto simp: A0m_design A1m_design A_def[symmetric] A_obs basic_merge_seed_eval; blast)

lemma A_basic_merge_seed_eval:
  "ades_merge_eval (A0m (A1m basic_merge_seed)) x p q out =
    (\<not> des_vars.ok\<^sub>v x \<or> ades_merge_eval basic_merge_seed x p q out)"
proof -
  obtain b s0 c X where obs: "(x,out) = ades_obs b s0 c X"
    by (cases x; cases out; pred_auto)
  show ?thesis
    using A_basic_merge_seed_obs[of p q b s0 c X] obs
    by (simp only: case_prod_conv; cases x; cases out; auto)
qed

text \<open>
  Applying A0m and A1m to the seed also gives A2m and A3m healthiness.
  Any A3m witness works because a started merge never accepts a failed final
  observation. A_basic_merge_seed_AssocMerge below establishes associativity
  before the reactive healthiness conditions are applied.
\<close>

lemma A_basic_merge_seed_A2m: "A0m (A1m basic_merge_seed) is A2m"
  by (rule Healthy_intro, rule ades_merge_ext, rule ades_obs_ext;
      simp only: A2m_design A2_obs;
      auto simp: A_basic_merge_seed_eval basic_merge_seed_eval; blast)

lemma A_basic_merge_seed_A3m: "A0m (A1m basic_merge_seed) is A3m w"
  by (rule Healthy_intro, rule ades_merge_ext, rule ades_obs_ext;
      simp only: A3m_obs;
      auto simp: A_basic_merge_seed_eval basic_merge_seed_eval)

lemma rad_ok_body_basic_merge_seed_obs:
  "(\<lambda>(x,out). ades_merge_eval (rad_ok_body basic_merge_seed) x p q out) (ades_obs b s0 c X) =
    (if b then (\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs b s0 c X)
     else rad_trace_extensions s0 \<inter> X \<noteq> {})"
  by (cases b; auto simp: rad_ok_body_eval basic_merge_seed_eval
      basic_merge_state_def rad_trace_extensions_def; blast)

definition BasicMerge_RAD :: "('t::trace, 'e) rad_merge_rel"
where "BasicMerge_RAD = RADOKM basic_merge_seed"

lemma RADOKM_basic_merge_seed:
  "RADOKM basic_merge_seed = BasicMerge_RAD"
  by (simp only: BasicMerge_RAD_def)

lemma BasicMerge_RAD_healthy [closure]: "BasicMerge_RAD is RADOKM"
  by (simp add: BasicMerge_RAD_def RADOKM_healthy)

lemma BasicMerge_RAD_SymMerge: "BasicMerge_RAD is SymMerge"
  unfolding BasicMerge_RAD_def
  by (rule RADOKM_SymMerge[OF basic_merge_seed_SymMerge])

lemma rad_par_basic_closure [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "rad_par P basic_merge_seed Q is RAD"
  by (rule rad_par_RAD_closure[OF assms])

lemma rad_par_basic_comm:
  "rad_par P basic_merge_seed Q = rad_par Q basic_merge_seed P"
  by (rule rad_par_comm[OF basic_merge_seed_SymMerge])

lemma BasicMerge_RAD_def':
  "BasicMerge_RAD = RA3M (RA2M (rad_ok_body basic_merge_seed))"
  by (simp only: BasicMerge_RAD_def RADOKM_def RA2M_RA3M_commute)

lemmas rad_ok_body_basic_merge_seed_eval =
  rad_ok_body_basic_merge_seed_obs[simplified]

lemma BasicMerge_RAD_started_zero:
  fixes s0 :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_RAD x p q out) (ades_obs True s0 c X) =
    (\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs True s0 c X)"
  by (simp add: BasicMerge_RAD_def' RA3M_eval RA2M_zero
      rad_ok_body_basic_merge_seed_eval assms)

lemma BasicMerge_RAD_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_RAD x \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr> out)
      (ades_obs True s0 c {z}) \<longleftrightarrow>
    (c \<and> basic_merge_state s0 l r z)"
  by (simp only: BasicMerge_RAD_started_zero[OF assms] basic_merge_seed_obs; simp)

lemma BasicMerge_RAD_matching_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
    "rad_state.tr\<^sub>v l = rad_state.tr\<^sub>v r"
    "rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v l"
    "rad_state.wait\<^sub>v z = (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r)"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_RAD x \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 True {z})"
  by (simp only: BasicMerge_RAD_singletons[OF assms(1,2)];
      simp add: basic_merge_state_def assms)

lemma BasicMerge_RAD_mismatching_singletons:
  fixes s0 l r z :: "('t::trace, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
    "rad_state.tr\<^sub>v l \<noteq> rad_state.tr\<^sub>v r"
  shows "\<not> (\<lambda>(x,out). ades_merge_eval BasicMerge_RAD x \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr> out)
    (ades_obs True s0 c {z})"
  using assms(3)
  by (simp only: BasicMerge_RAD_singletons[OF assms(1,2)];
      auto simp: basic_merge_state_def)

lemma rad_par_basic_started_zero:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and s0 :: "('t, 'e) rad_state"
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
  shows "rad_par P basic_merge_seed Q (ades_obs True s0 c X) \<longleftrightarrow>
    (c \<and> (\<exists>l r z.
      P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and>
      z \<in> X \<and> basic_merge_state s0 l r z))"
proof -
  have eval: "rad_par P basic_merge_seed Q (ades_obs True s0 c X) =
    (\<exists>p q. P (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,p) \<and>
      Q (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,q) \<and>
      (\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs True s0 c X))"
    by (subst rad_par_eval; simp only: RADOKM_basic_merge_seed
        BasicMerge_RAD_started_zero[OF assms, simplified case_prod_conv] case_prod_conv)
  have obs: "p = \<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>"
    if "des_vars.ok\<^sub>v p" "achoices.ac\<^sub>v (des_vars.more p) = {l}" for p l
    using that by (cases p; pred_auto)
  show ?thesis
  proof
    assume h: "rad_par P basic_merge_seed Q (ades_obs True s0 c X)"
    obtain p q l r z where h:
      "P (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,p)"
      "Q (\<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr>,q)"
      "des_vars.ok\<^sub>v p" "des_vars.ok\<^sub>v q" "c"
      "achoices.ac\<^sub>v (des_vars.more p) = {l}"
      "achoices.ac\<^sub>v (des_vars.more q) = {r}"
      "z \<in> X" "basic_merge_state s0 l r z"
      using h by (auto simp: eval basic_merge_seed_eval)
    show "c \<and> (\<exists>l r z. P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and> z \<in> X \<and> basic_merge_state s0 l r z)"
      using h(1,2,5,8,9) by (simp only: obs[OF h(3,6)] obs[OF h(4,7)]; blast)
  next
    assume "c \<and> (\<exists>l r z. P (ades_obs True s0 True {l}) \<and>
      Q (ades_obs True s0 True {r}) \<and> z \<in> X \<and> basic_merge_state s0 l r z)"
    then obtain l r z where h: "c" "P (ades_obs True s0 True {l})"
      "Q (ades_obs True s0 True {r})" "z \<in> X" "basic_merge_state s0 l r z" by blast
    show "rad_par P basic_merge_seed Q (ades_obs True s0 c X)"
      unfolding eval
      apply (rule exI[of _ "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {l}, \<dots> = ()\<rparr>"])
      apply (rule exI[of _ "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {r}, \<dots> = ()\<rparr>"])
      using h by (auto simp: basic_merge_seed_eval)
  qed
qed

subsection \<open>Associativity and Worked Prefixes\<close>

lemma trace_difference_eq_iff:
  fixes t0 a b :: "'t::trace"
  assumes "t0 \<le> a" "t0 \<le> b"
  shows "a - t0 = b - t0 \<longleftrightarrow> a = b"
proof
  assume eq: "a - t0 = b - t0"
  have "a = t0 + (a - t0)"
    using assms(1) by (simp add: diff_add_cancel_left')
  also have "... = t0 + (b - t0)" by (simp only: eq)
  also have "... = b" by (rule diff_add_cancel_left'[OF assms(2)])
  finally show "a = b" .
next
  assume "a = b"
  then show "a - t0 = b - t0" by simp
qed

(* Simultaneous normalization preserves associativity: the intermediate
   choice observation can be renamed through its surjective output map. *)
lemma RA2M_AssocMerge:
  fixes M :: "('t::trace, 'e) rad_merge_rel"
  assumes "AssocMerge M"
  shows "AssocMerge (RA2M M)"
proof (unfold AssocMerge_ades, intro allI)
  fix x :: "('t, 'e) rad_state astate des_vars_ext"
    and p q r out :: "('t, 'e) rad_state achoices des_vars_ext"
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  let ?N = "rad_merge_output ?s0"
  let ?x = "rad_merge_input x"
  have assoc:
    "(\<exists>y. ades_merge_eval M ?x (?N p) (?N q) y \<and>
          ades_merge_eval M ?x y (?N r) (?N out)) =
     (\<exists>y. ades_merge_eval M ?x (?N q) (?N r) y \<and>
          ades_merge_eval M ?x y (?N p) (?N out))"
    using assms unfolding AssocMerge_ades by blast
  show "(\<exists>y. ades_merge_eval (RA2M M) x p q y \<and>
          ades_merge_eval (RA2M M) x y r out) =
     (\<exists>y. ades_merge_eval (RA2M M) x q r y \<and>
          ades_merge_eval (RA2M M) x y p out)"
  proof
    assume left: "\<exists>y. ades_merge_eval (RA2M M) x p q y \<and>
      ades_merge_eval (RA2M M) x y r out"
    then obtain y where
      "ades_merge_eval M ?x (?N p) (?N q) (?N y)"
      "ades_merge_eval M ?x (?N y) (?N r) (?N out)"
      by (auto simp only: RA2M_eval)
    with assoc obtain z where z:
      "ades_merge_eval M ?x (?N q) (?N r) z"
      "ades_merge_eval M ?x z (?N p) (?N out)" by blast
    obtain target where target: "?N target = z"
      by (rule rad_merge_output_surj)
    show "\<exists>y. ades_merge_eval (RA2M M) x q r y \<and>
      ades_merge_eval (RA2M M) x y p out"
      using z target by (auto simp only: RA2M_eval)
  next
    assume right: "\<exists>y. ades_merge_eval (RA2M M) x q r y \<and>
      ades_merge_eval (RA2M M) x y p out"
    then obtain y where
      "ades_merge_eval M ?x (?N q) (?N r) (?N y)"
      "ades_merge_eval M ?x (?N y) (?N p) (?N out)"
      by (auto simp only: RA2M_eval)
    with assoc obtain z where z:
      "ades_merge_eval M ?x (?N p) (?N q) z"
      "ades_merge_eval M ?x z (?N r) (?N out)" by blast
    obtain target where target: "?N target = z"
      by (rule rad_merge_output_surj)
    show "\<exists>y. ades_merge_eval (RA2M M) x p q y \<and>
      ades_merge_eval (RA2M M) x y r out"
      using z target by (auto simp only: RA2M_eval)
  qed
qed

(* The raw state relation is associative. The intermediate refusal is free;
   reuse the final state's refusal and replace only its waiting flag. *)
lemma basic_merge_state_assoc:
  "(\<exists>v. basic_merge_state s0 a b v \<and> basic_merge_state s0 v c z) =
   (\<exists>v. basic_merge_state s0 b c v \<and> basic_merge_state s0 a v z)"
proof -
  have left:
    "(\<exists>v. basic_merge_state s0 a b v \<and> basic_merge_state s0 v c z) =
     (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v a \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v b \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v c \<and>
      rad_state.wait\<^sub>v z =
        ((rad_state.wait\<^sub>v a \<or> rad_state.wait\<^sub>v b) \<or> rad_state.wait\<^sub>v c))"
    by (auto simp add: basic_merge_state_def
        intro!: exI[where x="rad_state.wait\<^sub>v_update
          (\<lambda>_. rad_state.wait\<^sub>v a \<or> rad_state.wait\<^sub>v b) z"])
  have right:
    "(\<exists>v. basic_merge_state s0 b c v \<and> basic_merge_state s0 a v z) =
     (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v a \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v b \<and>
      rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v c \<and>
      rad_state.wait\<^sub>v z =
        (rad_state.wait\<^sub>v a \<or> (rad_state.wait\<^sub>v b \<or> rad_state.wait\<^sub>v c)))"
    by (auto simp add: basic_merge_state_def
        intro!: exI[where x="rad_state.wait\<^sub>v_update
          (\<lambda>_. rad_state.wait\<^sub>v b \<or> rad_state.wait\<^sub>v c) z"])
  show ?thesis by (simp only: left right disj_assoc)
qed

(* Generic exact-singleton lifting: only the final choice is upward closed.
   This is deliberately different from selecting arbitrary members of both
   branch choice sets, which does NOT preserve associativity. *)
lemma singleton_merge_AssocMerge:
  fixes M :: "'s ades_merge_rel"
    and B :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
  assumes eval: "\<And>x p q out.
    ades_merge_eval M x p q out \<longleftrightarrow>
    (des_vars.ok\<^sub>v out \<and> (\<exists>a b z.
      p = ades_output True {a} \<and>
      q = ades_output True {b} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      B (astate.s\<^sub>v (des_vars.more x)) a b z))"
    and state_assoc: "\<And>s0 a b c z.
      (\<exists>v. B s0 a b v \<and> B s0 v c z) =
      (\<exists>v. B s0 b c v \<and> B s0 v a z)"
  shows "AssocMerge M"
proof (unfold AssocMerge_ades, intro allI)
  fix x :: "'s astate des_vars_ext"
    and p q r out :: "'s achoices des_vars_ext"
  let ?s0 = "astate.s\<^sub>v (des_vars.more x)"
  show "(\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out) =
    (\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x y p out)"
  proof
    assume "\<exists>y. ades_merge_eval M x p q y \<and> ades_merge_eval M x y r out"
    then obtain a b c v z where
      p: "p = ades_output True {a}" and
      q: "q = ades_output True {b}" and
      r: "r = ades_output True {c}" and
      out: "des_vars.ok\<^sub>v out" "z \<in> achoices.ac\<^sub>v (des_vars.more out)" and
      steps: "B ?s0 a b v" "B ?s0 v c z"
      by (auto simp add: eval)
    from steps state_assoc[of ?s0 a b c z]
    obtain w where w: "B ?s0 b c w" "B ?s0 w a z" by blast
    have "ades_merge_eval M x q r (ades_output True {w})"
      using q r w by (auto simp add: eval)
    moreover have "ades_merge_eval M x (ades_output True {w}) p out"
      using p out w by (auto simp add: eval)
    ultimately show "\<exists>y. ades_merge_eval M x q r y \<and>
      ades_merge_eval M x y p out" by blast
  next
    assume "\<exists>y. ades_merge_eval M x q r y \<and> ades_merge_eval M x y p out"
    then obtain a b c w z where
      p: "p = ades_output True {a}" and
      q: "q = ades_output True {b}" and
      r: "r = ades_output True {c}" and
      out: "des_vars.ok\<^sub>v out" "z \<in> achoices.ac\<^sub>v (des_vars.more out)" and
      steps: "B ?s0 b c w" "B ?s0 w a z"
      by (auto simp add: eval)
    from steps state_assoc[of ?s0 a b c z]
    obtain v where v: "B ?s0 a b v" "B ?s0 v c z" by blast
    have "ades_merge_eval M x p q (ades_output True {v})"
      using p q v by (auto simp add: eval)
    moreover have "ades_merge_eval M x (ades_output True {v}) r out"
      using r out v by (auto simp add: eval)
    ultimately show "\<exists>y. ades_merge_eval M x p q y \<and>
      ades_merge_eval M x y r out" by blast
  qed
qed

lemma BasicMerge_RAD_prefix_singleton:
  assumes "\<not> rad_state.wait\<^sub>v s0"
  shows "PrefixSkip_RAD a (ades_obs True s0 True {z}) \<longleftrightarrow>
    (if rad_state.wait\<^sub>v z
     then rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v s0 \<and> a \<notin> rad_state.ref\<^sub>v z
     else rad_state.tr\<^sub>v z = rad_state.tr\<^sub>v s0 @ [a])"
  using assms
  by (simp add: PrefixSkip_RAD_design RA1_def Let_def prefix_post_p2ac
      p2ac_def ades_state_choice_def rad_trace_extensions_def;
      pred_auto)

lemma basic_merge_seed_eval':
  "ades_merge_eval basic_merge_seed x p q out \<longleftrightarrow>
    (des_vars.ok\<^sub>v out \<and> (\<exists>l r z.
      p = ades_output True {l} \<and> q = ades_output True {r} \<and>
      z \<in> achoices.ac\<^sub>v (des_vars.more out) \<and>
      basic_merge_state (astate.s\<^sub>v (des_vars.more x)) l r z))"
proof -
  have obs: "p = ades_output True {l} \<longleftrightarrow>
      (des_vars.ok\<^sub>v p \<and> achoices.ac\<^sub>v (des_vars.more p) = {l})" for p l
    by (cases p; pred_auto)
  show ?thesis by (simp only: basic_merge_seed_eval obs; blast)
qed

lemma basic_merge_seed_AssocMerge:
  "AssocMerge (basic_merge_seed :: ('t::trace, 'e) rad_merge_rel)"
proof (rule singleton_merge_AssocMerge[OF basic_merge_seed_eval'])
  fix s0 a b c z :: "('t, 'e) rad_state"
  show "(\<exists>v. basic_merge_state s0 a b v \<and> basic_merge_state s0 v c z) =
    (\<exists>v. basic_merge_state s0 b c v \<and> basic_merge_state s0 v a z)"
    using basic_merge_state_assoc[of s0 a b c z]
    by (simp only: basic_merge_state_def conj_ac disj_ac)
qed

lemma A_basic_merge_seed_AssocMerge:
  "AssocMerge (A0m (A1m (basic_merge_seed :: ('t::trace, 'e) rad_merge_rel)))"
proof -
  have eval: "ades_merge_eval (A0m (A1m basic_merge_seed)) x p q out =
    (\<not> des_vars.ok\<^sub>v x \<or> ades_merge_eval basic_merge_seed x p q out)" for x p q out
    by (rule A_basic_merge_seed_eval)
  show ?thesis using basic_merge_seed_AssocMerge
    by (auto simp only: AssocMerge_ades eval; blast)
qed

lemma RA3M_AssocMerge:
  assumes "AssocMerge M"
  shows "AssocMerge (RA3M M)"
proof -
  have eval: "ades_merge_eval (RA3M M) x p q out =
    (if rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))
     then II_Rac (x,out) else ades_merge_eval M x p q out)" for x p q out
    by (simp add: RA3M_eval)
  show ?thesis using assms
    by (auto simp only: AssocMerge_ades eval split: if_splits; blast)
qed

lemma basic_merge_rad_ok_body_AssocMerge:
  "AssocMerge (rad_ok_body (basic_merge_seed :: ('t::trace, 'e) rad_merge_rel))"
proof -
  have obs: "(\<lambda>(x,out). ades_merge_eval (rad_ok_body (basic_merge_seed :: ('t, 'e) rad_merge_rel)) x p q out) (ades_obs b s0 c X) =
      (if b then (\<lambda>(x,out). ades_merge_eval basic_merge_seed x p q out) (ades_obs b s0 c X)
       else rad_trace_extensions s0 \<inter> X \<noteq> {})"
    for p q b s0 c X
    by (rule rad_ok_body_basic_merge_seed_obs)
  have eval: "ades_merge_eval (rad_ok_body (basic_merge_seed :: ('t, 'e) rad_merge_rel)) x p q out =
    (if des_vars.ok\<^sub>v x then ades_merge_eval basic_merge_seed x p q out
     else rad_trace_extensions (astate.s\<^sub>v (des_vars.more x)) \<inter>
       achoices.ac\<^sub>v (des_vars.more out) \<noteq> {})" for x p q out
  proof -
    obtain b s0 c X where obs_pair: "(x,out) = ades_obs b s0 c X"
      by (cases x; cases out; pred_auto)
    note result = obs[of p q b s0 c X]
    show ?thesis using result obs_pair
      by (simp only: case_prod_conv; cases x; cases out; auto)
  qed
  show ?thesis using basic_merge_seed_AssocMerge
    by (auto simp only: AssocMerge_ades eval split: if_splits; blast)
qed

lemma BasicMerge_RAD_AssocMerge: "AssocMerge BasicMerge_RAD"
  by (simp only: BasicMerge_RAD_def';
      intro RA3M_AssocMerge RA2M_AssocMerge basic_merge_rad_ok_body_AssocMerge)

lemma rad_par_basic_assoc:
  "rad_par (rad_par P basic_merge_seed Q) basic_merge_seed R =
    rad_par P basic_merge_seed (rad_par Q basic_merge_seed R)"
  by (rule rad_par_assoc; simp only: RADOKM_basic_merge_seed BasicMerge_RAD_SymMerge BasicMerge_RAD_AssocMerge)

lemma rad_par_basic_prefixes_complete:
  assumes "\<not> rad_state.wait\<^sub>v s0" "rad_state.tr\<^sub>v s0 = 0"
    "\<not> rad_state.wait\<^sub>v z"
  shows "rad_par (PrefixSkip_RAD a) basic_merge_seed (PrefixSkip_RAD b)
    (ades_obs True s0 c {z}) \<longleftrightarrow>
    (c \<and> a = b \<and> rad_state.tr\<^sub>v z = [a])"
  by (simp only: rad_par_basic_started_zero[OF assms(1,2)]
      BasicMerge_RAD_prefix_singleton[OF assms(1)];
      auto simp: basic_merge_state_def assms zero_list_def intro!: exI[where x=z])

lemma BasicMerge_RAD_wait:
  assumes "rad_state.wait\<^sub>v s0"
  shows "(\<lambda>(x,out). ades_merge_eval BasicMerge_RAD x p q out) (ades_obs b s0 c X) =
    ((\<not> b \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}) \<or> (c \<and> s0 \<in> X))"
  by (simp add: BasicMerge_RAD_def' RA3M_eval
      II_Rac_eval assms)

lemma basic_merge_seed_not_RADOKM:
  "\<not> ((basic_merge_seed :: ('t::trace, 'e) rad_merge_rel) is RADOKM)"
proof
  let ?M = "basic_merge_seed :: ('t, 'e) rad_merge_rel"
  let ?s0 = "\<lparr>tr\<^sub>v = 0, ref\<^sub>v = {}, wait\<^sub>v = True, \<dots> = ()\<rparr>
    :: ('t, 'e) rad_state"
  let ?p = "ades_output False {}"
  assume h: "?M is RADOKM"
  have fixed: "RADOKM ?M = ?M" by (rule Healthy_if[OF h])
  have eq: "(\<lambda>(x,out). ades_merge_eval BasicMerge_RAD x ?p ?p out) (ades_obs True ?s0 True {?s0}) =
    (\<lambda>(x,out). ades_merge_eval ?M x ?p ?p out) (ades_obs True ?s0 True {?s0})"
    by (simp only: BasicMerge_RAD_def fixed)
  show False using eq
    by (simp add: BasicMerge_RAD_def' RA3M_eval
        II_Rac_eval basic_merge_seed_eval)
qed

lemma basic_merge_state_increments:
  assumes "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v l"
    "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v r"
  shows "basic_merge_state s0 l r z =
    (rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z \<and>
     rad_state.tr\<^sub>v z - rad_state.tr\<^sub>v s0 =
       rad_state.tr\<^sub>v l - rad_state.tr\<^sub>v s0 \<and>
     rad_state.tr\<^sub>v z - rad_state.tr\<^sub>v s0 =
       rad_state.tr\<^sub>v r - rad_state.tr\<^sub>v s0 \<and>
     rad_state.wait\<^sub>v z = (rad_state.wait\<^sub>v l \<or> rad_state.wait\<^sub>v r))"
  using assms
  by (cases "rad_state.tr\<^sub>v s0 \<le> rad_state.tr\<^sub>v z";
      simp add: basic_merge_state_def trace_difference_eq_iff)

end
