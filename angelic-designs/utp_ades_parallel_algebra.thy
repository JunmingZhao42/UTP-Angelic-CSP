section \<open>AD Parallel Algebra\<close>

theory utp_ades_parallel_algebra
  imports utp_ades_parallel_operator
begin

text \<open>Algebraic laws of AD parallel.\<close>

subsection \<open>Choice\<close>

text \<open>The choice laws for any AD merge apply to the lifted merge. The angelic law can be
  strict, since the left side may resolve the shared operand's demonic choice twice.\<close>

(* P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R) *)
lemma ades_par_demonic_distl:
  "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<sqinter>\<^sub>A\<^sub>D R) = (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<sqinter>\<^sub>A\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (simp only: ades_par_def ades_par_by_merge_demonic_distl)

(* (P \<sqinter> Q) \<parallel> R = (P \<parallel> R) \<sqinter> (Q \<parallel> R) *)
lemma ades_par_demonic_distr:
  "(P \<sqinter>\<^sub>A\<^sub>D Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqinter>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (simp only: ades_par_def ades_par_by_merge_demonic_distr)

(* (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R) *)
lemma ades_par_angelic_subdistl:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<squnion>\<^sub>A\<^sub>D R)"
  by (simp only: ades_par_def ades_par_by_merge_angelic_subdistl)

(* (P \<parallel> R) \<squnion> (Q \<parallel> R) \<sqsubseteq> (P \<squnion> Q) \<parallel> R *)
lemma ades_par_angelic_subdistr:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqsubseteq> (P \<squnion>\<^sub>A\<^sub>D Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R"
  by (simp only: ades_par_def ades_par_by_merge_angelic_subdistr)

text \<open>The angelic laws are equalities when the shared operand Q has no demonic choice,
  so its offered sets are closed under intersection, and no operand diverges:
  (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q.\<close>

(* (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q *)
lemma ades_par_angelic_distr:
  fixes P P' Q :: "'s angelic_design"
  assumes a: "P is A" "P' is A"
    and nd: "P is NDAD" "P' is NDAD" "Q is NDAD"
    and q: "\<And>s0 Y Y'. Q (ades_obs True s0 True Y) \<Longrightarrow> Q (ades_obs True s0 True Y') \<Longrightarrow>
      Q (ades_obs True s0 True (Y \<inter> Y'))"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  have un: "S (ades_obs False s0 c X)" if "S is A" for S :: "'s angelic_design" and c X
    using that by (simp add: A_healthy_components_iff H1_healthy_obs_iff)
  have up: "S (ades_obs True s0 True X')"
    if "S is A" "S (ades_obs True s0 True X)" "X \<subseteq> X'" for S :: "'s angelic_design" and X X'
  proof -
    have pb: "S is PBMH_ades" using that(1) by (simp add: A_healthy_components_iff)
    show ?thesis by (rule PBMH_ades_upward[OF pb that(2)]; simp add: that(3))
  qed
  have ndt: "c \<and> X \<noteq> {}" if "S is NDAD" "S (ades_obs True s0 c X)" for S :: "'s angelic_design" and c X
    using NDAD_obs[of S True s0 c X] that by (simp add: Healthy_if[OF that(1)])
  show "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac') = ((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: ades_par_eval inf_fun_def inf_bool_def un[OF a(1)] un[OF a(2)])
  next
    case True
    show ?thesis
    proof
      assume "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac')"
      then obtain okL X okR Y okL' X' okR' Y' where
        px: "P (ades_obs True s0 okL X)" and qy: "Q (ades_obs True s0 okR Y)"
        and f: "\<forall>a\<in>X. \<forall>b\<in>Y. \<exists>s'. merge_eval j s0 a b s'"
        and h: "okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>a\<in>X. \<forall>b\<in>Y. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        and px': "P' (ades_obs True s0 okL' X')" and qy': "Q (ades_obs True s0 okR' Y')"
        and f': "\<forall>a\<in>X'. \<forall>b\<in>Y'. \<exists>s'. merge_eval j s0 a b s'"
        and h': "okL' \<and> okR' \<longrightarrow> ok' \<and> (\<forall>a\<in>X'. \<forall>b\<in>Y'. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        using True by (simp only: ades_par_eval inf_fun_def inf_bool_def simp_thms) blast
      note ok = ndt[OF nd(1) px] ndt[OF nd(3) qy] ndt[OF nd(2) px'] ndt[OF nd(3) qy']
      have T: "P (ades_obs True s0 True X)" "P' (ades_obs True s0 True X')"
          "Q (ades_obs True s0 True Y)" "Q (ades_obs True s0 True Y')"
        using px px' qy qy' ok by simp_all
      have qi: "Q (ades_obs True s0 True (Y \<inter> Y'))" by (rule q[OF T(3,4)])
      have "((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def
        by (rule exI[where x=True], rule exI[where x="X \<union> X'"],
            rule exI[where x=True], rule exI[where x="Y \<inter> Y'"])
           (use up[OF a(1) T(1) Un_upper1] up[OF a(2) T(2) Un_upper2] ndt[OF nd(3) qi]
             ndt[OF nd(1) T(1)] qi ok f f' h h' in blast)
      then show "((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
        using True by simp
    next
      assume "((P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
      then show "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def by blast
    qed
  qed
qed

(* (Q \<parallel> P) \<squnion> (Q \<parallel> P') = Q \<parallel> (P \<squnion> P') *)
lemma ades_par_angelic_distl:
  fixes P P' Q :: "'s angelic_design"
  assumes a: "P is A" "P' is A"
    and nd: "P is NDAD" "P' is NDAD" "Q is NDAD"
    and q: "\<And>s0 Y Y'. Q (ades_obs True s0 True Y) \<Longrightarrow> Q (ades_obs True s0 True Y') \<Longrightarrow>
      Q (ades_obs True s0 True (Y \<inter> Y'))"
  shows "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P') = Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  have un: "S (ades_obs False s0 c X)" if "S is A" for S :: "'s angelic_design" and c X
    using that by (simp add: A_healthy_components_iff H1_healthy_obs_iff)
  have up: "S (ades_obs True s0 True X')"
    if "S is A" "S (ades_obs True s0 True X)" "X \<subseteq> X'" for S :: "'s angelic_design" and X X'
  proof -
    have pb: "S is PBMH_ades" using that(1) by (simp add: A_healthy_components_iff)
    show ?thesis by (rule PBMH_ades_upward[OF pb that(2)]; simp add: that(3))
  qed
  have ndt: "c \<and> X \<noteq> {}" if "S is NDAD" "S (ades_obs True s0 c X)" for S :: "'s angelic_design" and c X
    using NDAD_obs[of S True s0 c X] that by (simp add: Healthy_if[OF that(1)])
  show "((Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac') = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: ades_par_eval inf_fun_def inf_bool_def un[OF a(1)] un[OF a(2)])
  next
    case True
    show ?thesis
    proof
      assume "((Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac')"
      then obtain okR Y okL X okR' Y' okL' X' where
        qy: "Q (ades_obs True s0 okR Y)" and px: "P (ades_obs True s0 okL X)"
        and f: "\<forall>a\<in>Y. \<forall>b\<in>X. \<exists>s'. merge_eval j s0 a b s'"
        and h: "okR \<and> okL \<longrightarrow> ok' \<and> (\<forall>a\<in>Y. \<forall>b\<in>X. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        and qy': "Q (ades_obs True s0 okR' Y')" and px': "P' (ades_obs True s0 okL' X')"
        and f': "\<forall>a\<in>Y'. \<forall>b\<in>X'. \<exists>s'. merge_eval j s0 a b s'"
        and h': "okR' \<and> okL' \<longrightarrow> ok' \<and> (\<forall>a\<in>Y'. \<forall>b\<in>X'. \<exists>s'\<in>ac'. merge_eval j s0 a b s')"
        using True by (simp only: ades_par_eval inf_fun_def inf_bool_def simp_thms) blast
      note ok = ndt[OF nd(1) px] ndt[OF nd(3) qy] ndt[OF nd(2) px'] ndt[OF nd(3) qy']
      have T: "P (ades_obs True s0 True X)" "P' (ades_obs True s0 True X')"
          "Q (ades_obs True s0 True Y)" "Q (ades_obs True s0 True Y')"
        using px px' qy qy' ok by simp_all
      have qi: "Q (ades_obs True s0 True (Y \<inter> Y'))" by (rule q[OF T(3,4)])
      have "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs True s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def
        by (rule exI[where x=True], rule exI[where x="Y \<inter> Y'"],
            rule exI[where x=True], rule exI[where x="X \<union> X'"])
           (use up[OF a(1) T(1) Un_upper1] up[OF a(2) T(2) Un_upper2] ndt[OF nd(3) qi]
             ndt[OF nd(1) T(1)] qi ok f f' h h' in blast)
      then show "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
        using True by simp
    next
      assume "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
      then show "((Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>A\<^sub>D (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac')"
        unfolding ades_par_eval inf_fun_def inf_bool_def by blast
    qed
  qed
qed

subsection \<open>Monotonicity\<close>

lemma ades_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "(P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1) \<sqsubseteq> (P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2)"
  unfolding ades_par_def
  using assms by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)

subsection \<open>Zero Laws\<close>

text \<open>A nonterminating branch observation releases the output guarantee.
  Chaos in both branches therefore yields Chaos whenever the state merge has
  some merged state at every initial state.\<close>

lemma ades_par_chaos_chaos:
  assumes "\<And>s0. \<exists>sL sR s'. merge_eval j s0 sL sR s'"
  shows "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true :: 's angelic_design) = true"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' X
  obtain sL sR s' where witness: "merge_eval j s0 sL sR s'"
    using assms by blast
  have started: "\<exists>okL acL okR acR. acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow>
        (ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>X. merge_eval j s0 sL sR s')))"
    by (rule exI[of _ False], rule exI[of _ "{sL}"], rule exI[of _ False],
        rule exI[of _ "{sR}"]) (use witness in blast)
  show "(true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true :: 's angelic_design) (ades_obs ok0 s0 ok' X) =
    (true :: 's angelic_design) (ades_obs ok0 s0 ok' X)"
    using started
    by (simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified] true_pred_def)
qed

(* We let Chaos absorb any feasible operand: by upward closure P offers the
   full choice set, Chaos diverges offering it too, and a mergeable j merges
   each pair, so every output is released:
     P is A, P ;; true = true \<Longrightarrow> P \<parallel>AD[j] Chaos = Chaos *)
lemma ades_par_chaos:
  fixes P :: "'s angelic_design"
  assumes "P is A" "P is H4" "mergeable j"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true = true" "true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = true"
proof -
  have obs: "P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not> b \<or> (\<exists>Y \<subseteq> X. P (ades_obs True s0 False Y)) \<or>
      (c \<and> X \<noteq> {} \<and> (\<exists>Y \<subseteq> X. P (ades_obs True s0 True Y))))" for b s0 c X
    by (subst Healthy_if[OF assms(1), symmetric], rule A_obs)
  have "\<exists>c. P (ades_obs b s0 c UNIV)" for b s0
  proof -
    have "\<exists>p. P (fst (ades_obs b s0 True {}), p)"
      using fun_cong[OF is_H4_alt_def[THEN iffD1, OF assms(2)],
          of "(fst (ades_obs b s0 True {}), undefined)"]
      by (simp add: seq_def true_pred_def)
    then obtain c X where "P (ades_obs b s0 c X)"
      unfolding fst_conv choices_ex by blast
    then show ?thesis
      using obs[of b s0 c X] obs[of b s0 c UNIV] by blast
  qed
  then have feasible: "P (ades_obs b s0 (SOME c. P (ades_obs b s0 c UNIV)) UNIV)" for b s0
    by (rule someI_ex)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> true = true"
    by (rule ades_obs_ext, simp only: ades_par_eval true_pred_def SEXP_def simp_thms,
        rule exI, rule exI[of _ UNIV], rule exI[of _ False], rule exI[of _ UNIV])
       (use feasible assms(3) in blast)
  show "true \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = true"
    by (rule ades_obs_ext, simp only: ades_par_eval true_pred_def SEXP_def simp_thms,
        rule exI[of _ False], rule exI[of _ UNIV], rule exI, rule exI[of _ UNIV])
       (use feasible assms(3) in blast)
qed

lemma ades_par_miracle:
  assumes "P is H1"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>A\<^sub>D"
        "\<^bold>\<top>\<^sub>A\<^sub>D \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>D"
proof -
  have miracle: "(A false :: 's angelic_design) = \<top>\<^sub>D"
    by (rule ades_obs_ext; simp add: A_obs top_d_not_ok; pred_simp)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>D = \<^bold>\<top>\<^sub>A\<^sub>D"
       "\<^bold>\<top>\<^sub>A\<^sub>D \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>D"
    unfolding miracle ades_par_def
    by (rule par_by_merge_miracle[OF assms merge_ades_is_H1m])+
qed

subsection \<open>Commutativity\<close>

lemma ades_par_comm:
  assumes "j is SymMerge"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P)"
  unfolding ades_par_def
  by (rule par_by_merge_comm[OF merge_ades_SymMerge[OF assms]])

subsection \<open>Associativity\<close>

text \<open>Associativity of the design images transfers to the lifted merge.\<close>

lemma ades_lift_par_assoc_transfer:
  fixes M :: "'s des_merge"
  assumes ops: "P is A" "Q is A" "R is A" "P is A2" "Q is A2" "R is A2"
    and merge: "M is HDm" "M is H3m"
    and ordinary: "(ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) \<parallel>\<^bsub>M\<^esub> ac2p R = ac2p P \<parallel>\<^bsub>M\<^esub> (ac2p Q \<parallel>\<^bsub>M\<^esub> ac2p R)"
  shows "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R =
    P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> (Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R)"
proof -
  have pq: "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) is A" "(P \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> Q) is A2"
    and qr: "(Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R) is A" "(Q \<parallel>\<^bsub>H3m (H1m (ABm (ac'_lift_merge M)))\<^esub> R) is A2"
    by (simp_all only: ades_par_by_merge_d2ac_ac2p[OF ops(1,2,4,5) merge refl]
        ades_par_by_merge_d2ac_ac2p[OF ops(2,3,5,6) merge refl] d2ac_is_A d2ac_is_A2)
  show ?thesis
    by (simp only: ades_par_by_merge_d2ac_ac2p[OF pq(1) ops(3) pq(2) ops(6) merge refl]
        ades_par_by_merge_d2ac_ac2p[OF ops(1) qr(1) ops(4) qr(2) merge refl]
        ades_par_by_merge_ac2p[OF ops(1,2,4,5) merge refl] ades_par_by_merge_ac2p[OF ops(2,3,5,6) merge refl]
        ordinary)
qed

lemma A_ac2p_NDD:
  assumes "P is A" "P is NDAD"
  shows "ac2p P is NDD"
proof -
  have "ac2p (A P) is NDD"
    using assms(2) unfolding NDD_healthy_iff preD_true_iff NDAD_healthy_obs_iff
    by (auto simp: ac2p_def A_PBMH_ades A_obs StateII_def)
  then show ?thesis
    by (simp only: Healthy_if[OF assms(1)])
qed

text \<open>For H1 and A2 operands, AD parallel by @{term j} first normalises the
  operands with @{const A}.\<close>

lemma A_preserves_NDAD:
  assumes "P is A2" "P is NDAD"
  shows "A P is NDAD"
  using assms(2) unfolding NDAD_healthy_obs_iff
  by (simp add: A_obs_A2[OF assms(1)]; blast)

lemma ades_par_normalise_A3:
  assumes ops: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R"
    "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
proof -
  have pq: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A" "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2" "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
    and qr: "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is A2" "(Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) is H1"
    using ades_par_A_closure[OF h1(1,2)] ades_par_A2_closure[OF ops(1,2)]
      ades_par_A_closure[OF h1(2,3)] ades_par_A2_closure[OF ops(2,3)]
    by (simp_all add: A_healthy_components_iff)
  show "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R"
    apply (subst ades_par_normalise_A[OF pq(2) ops(3) pq(3) h1(3)])
    apply (subst Healthy_if[OF pq(1)])
    by (subst ades_par_normalise_A[OF ops(1,2) h1(1,2)], rule refl)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (A Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A R)"
    apply (subst ades_par_normalise_A[OF ops(1) qr(2) h1(1) qr(3)])
    apply (subst Healthy_if[OF qr(1)])
    by (subst ades_par_normalise_A[OF ops(2,3) h1(2,3)], rule refl)
qed

lemma ades_par_assoc:
  fixes j :: "'s merge"
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and merge: "j is SymMerge" "AssocMerge j" "mergeable j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have a: "A S is A" for S :: "'s angelic_design"
    by (simp add: Healthy_def' A_idem)
  show ?thesis
    unfolding ades_par_normalise_A3[OF operands h1]
    unfolding ades_par_def merge_ades_design_lift
    by (rule ades_lift_par_assoc_transfer[OF a a a A_preserves_A2[OF operands(1)]
          A_preserves_A2[OF operands(2)] A_preserves_A2[OF operands(3)]
          merge_des_is_HDm merge_des_is_H3m des_par_assoc[OF merge]])
qed

lemma ades_par_assoc_nd:
  fixes j :: "'s merge"
  assumes operands: "P is A2" "Q is A2" "R is A2"
      and h1: "P is H1" "Q is H1" "R is H1"
      and nondiv: "P is NDAD" "Q is NDAD" "R is NDAD"
      and merge: "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have a: "A S is A" for S :: "'s angelic_design"
    by (simp add: Healthy_def' A_idem)
  show ?thesis
    unfolding ades_par_normalise_A3[OF operands h1]
    unfolding ades_par_def merge_ades_design_lift
    by (rule ades_lift_par_assoc_transfer[OF a a a A_preserves_A2[OF operands(1)]
          A_preserves_A2[OF operands(2)] A_preserves_A2[OF operands(3)]
          merge_des_is_HDm merge_des_is_H3m
          des_par_assoc_nd[OF
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(1) nondiv(1)]]
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(2) nondiv(2)]]
            A_ac2p_NDD[OF a A_preserves_NDAD[OF operands(3) nondiv(3)]] merge]])
qed

text \<open>For a deterministic (Functional) merge we get associativity for all operands,
  without A2 or nondivergence: (P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R).
  As in D, it follows from associativity of the lifted merge.\<close>

theorem ades_par_assoc_det:
  fixes j :: "'s merge" and P Q R :: "'s angelic_design"
  assumes det: "Functional j" and tot: "mergeable j"
    and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  unfolding ades_par_def
  by (rule par_by_merge_assoc[OF merge_ades_SymMerge[OF sym] merge_ades_AssocMerge[OF det tot assoc]])

text \<open>For nondivergent operands a deterministic merge need not be total:
  (P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R). With divergence, a partial merge breaks this.\<close>

theorem ades_par_assoc_det_nd:
  fixes j :: "'s merge" and P Q R :: "'s angelic_design"
  assumes nondiv: "P is NDAD" "Q is NDAD" "R is NDAD"
    and det: "Functional j" and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  unfolding ades_par_def
proof (rule par_by_merge_assoc_guard[OF SymMerge_merge_guard[OF merge_ades_SymMerge[OF sym]]
      merge_ades_guard_AssocMerge[OF det assoc]])
  (* nondivergent operands never pass from a started prior to ok' = False *)
  have nd_ok: "\<And>x z. S (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z"
    if "S is NDAD" for S :: "'s angelic_design"
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    by (metis (full_types) NDAD_obs Healthy_if[OF that] des_vars.select_convs(1))
  show "\<lbrakk> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v p; des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v q;
      merge_eval (merge_ades j) x p q z \<rbrakk> \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z" for x p q z
    by (auto simp: merge_ades_unfold Let_def)
  show "P (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z"
    "Q (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z"
    "R (x, z) \<Longrightarrow> des_vars.ok\<^sub>v x \<longrightarrow> des_vars.ok\<^sub>v z" for x z
    using nd_ok[OF nondiv(1)] nd_ok[OF nondiv(2)] nd_ok[OF nondiv(3)] by blast+
qed

end
