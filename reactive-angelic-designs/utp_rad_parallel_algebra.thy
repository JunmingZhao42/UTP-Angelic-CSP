section \<open>RAD Parallel Algebra\<close>

theory utp_rad_parallel_algebra
  imports utp_rad_parallel_operator
begin

subsection \<open>Algebra\<close>

lemma rad_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "P1 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q1 \<sqsubseteq> P2 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q2"
  using assms
  by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)

lemma rad_par_comm:
  assumes "j is SymMerge"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P"
  by (rule par_by_merge_comm[OF rad_lift_merge_SymMerge[OF merge_rdes_SymMerge[OF assms]]])

text \<open>Associativity of the lifted merge transfers from the ordinary
  nondivergent law through @{const p2ac}. The premises on @{term M} are those of
  @{thm [source] par_by_merge_assoc_NDRD}.\<close>

lemma par_by_rad_lift_merge_assoc_NDRAD:
  fixes M :: "('t::trace, 'e set) rp merge"
  assumes rad: "P is RAD" "Q is RAD" "R is RAD"
      and a2: "P is A2" "Q is A2" "R is A2"
      and nondiv: "P is NDRAD" "Q is NDRAD" "R is NDRAD"
      and merge: "M is SymMerge" "M is NDRDm"
        "AssocMerge (merge_guard (\<lambda>x z. ok\<^sub>v x \<and> \<not> wait\<^sub>v x \<longrightarrow> ok\<^sub>v z) M)"
  shows "(P \<parallel>\<^bsub>rad_lift_merge M\<^esub> Q) \<parallel>\<^bsub>rad_lift_merge M\<^esub> R =
    P \<parallel>\<^bsub>rad_lift_merge M\<^esub> (Q \<parallel>\<^bsub>rad_lift_merge M\<^esub> R)"
proof -
  have rd: "ac2p P is RD" "ac2p Q is RD" "ac2p R is RD"
    using rad a2 by (blast intro: rad_ac2p_RD)+
  have nd: "ac2p P is NDRD" "ac2p Q is NDRD" "ac2p R is NDRD"
    using rad a2 nondiv by (blast intro: rad_ac2p_NDRD)+
  have ordinary: "(ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q) \<parallel>\<^bsub>M\<^esub> ac2p R =
      ac2p P \<parallel>\<^bsub>M\<^esub> (ac2p Q \<parallel>\<^bsub>M\<^esub> ac2p R)"
    by (rule par_by_merge_assoc_NDRD[OF rd nd merge])
  show ?thesis
    using arg_cong[OF ordinary, of p2ac]
    by (simp only: rad_lift_par_p2ac[symmetric]
        rad_p2ac_ac2p_RAD_A2'[OF rad(1) a2(1)]
        rad_p2ac_ac2p_RAD_A2'[OF rad(2) a2(2)]
        rad_p2ac_ac2p_RAD_A2'[OF rad(3) a2(3)])
qed

lemma rad_par_assoc:
  assumes rad: "P is RAD" "Q is RAD" "R is RAD"
      and a2: "P is A2" "Q is A2" "R is A2"
      and nondiv: "P is NDRAD" "Q is NDRAD" "R is NDRAD"
      and merge: "j is SymMerge" "AssocMerge j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R =
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (rule par_by_rad_lift_merge_assoc_NDRAD[OF rad a2 nondiv
        merge_rdes_SymMerge[OF merge(1)] merge_rdes_NDRDm
        merge_rdes_guard_AssocMerge[OF merge(2)]])

(* We transfer the RD law for normal operands through ac2p:
     (P \<parallel>RAD[j] Q) \<parallel>RAD[j] R = P \<parallel>RAD[j] (Q \<parallel>RAD[j] R) *)
lemma rad_par_assoc_nrd:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design" and j :: "('t \<times> 'e set) merge"
  assumes rad: "P is RAD" "Q is RAD" "R is RAD"
      and a2: "P is A2" "Q is A2" "R is A2"
      and nrd: "ac2p P is NRD" "ac2p Q is NRD" "ac2p R is NRD"
      and sym: "j is SymMerge" and assoc: "AssocMerge j"
      and absorb: "\<And>x p q. {u. \<exists>z. merge_eval j x p q z \<and> fst z \<le> fst u} \<subseteq>
        {u. \<exists>p'. fst p \<le> fst p' \<and> merge_eval j x p' q u}"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  have ordinary: "(ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p Q) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p R =
      ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> (ac2p Q \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p R)"
    by (rule rdes_lift_parallel_assoc_nrd[OF nrd sym assoc absorb])
  show ?thesis
    using arg_cong[OF ordinary, of p2ac]
    by (simp only: rad_lift_par_p2ac[symmetric]
        rad_p2ac_ac2p_RAD_A2'[OF rad(1) a2(1)]
        rad_p2ac_ac2p_RAD_A2'[OF rad(2) a2(2)]
        rad_p2ac_ac2p_RAD_A2'[OF rad(3) a2(3)])
qed

subsubsection \<open>Choice\<close>

text \<open>We instantiate the arbitrary-merge laws with the lifted merge:
  P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R).\<close>

(* P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R) *)
lemma rad_par_demonic_distl:
  "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<sqinter>\<^sub>R\<^sub>A\<^sub>D R) = (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (rule rad_par_by_merge_demonic_distl)

(* (P \<sqinter> Q) \<parallel> R = (P \<parallel> R) \<sqinter> (Q \<parallel> R) *)
lemma rad_par_demonic_distr:
  "(P \<sqinter>\<^sub>R\<^sub>A\<^sub>D Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R = (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqinter>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  by (rule rad_par_by_merge_demonic_distr)

(* (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R) *)
lemma rad_par_angelic_subdistl:
  "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqsubseteq> P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R)"
  by (rule rad_par_by_merge_angelic_subdistl)

(* (P \<parallel> R) \<squnion> (Q \<parallel> R) \<sqsubseteq> (P \<squnion> Q) \<parallel> R *)
lemma rad_par_angelic_subdistr:
  "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqsubseteq> (P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R"
  by (rule rad_par_by_merge_angelic_subdistr)

text \<open>We combine the varying offers by union and the shared offers by
  intersection. We require intersection closure for all shared offers,
  including waiting states, and nondivergence so their termination flags agree:
  (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q.\<close>

(* (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q *)
lemma rad_par_angelic_distr:
  fixes P P' Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes rad: "P is RAD" "P' is RAD"
    and nd: "P is NDRAD" "P' is NDRAD" "Q is NDRAD"
    and q: "\<And>s0 Y Y'. Q (ades_obs True s0 True Y) \<Longrightarrow> Q (ades_obs True s0 True Y') \<Longrightarrow>
      Q (ades_obs True s0 True (Y \<inter> Y'))"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P' \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (P \<squnion>\<^sub>R\<^sub>A\<^sub>D P') \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  have un: "S (ades_obs False s0 c X) \<longleftrightarrow> rad_trace_extensions s0 \<inter> X \<noteq> {}"
    if "S is RAD" for S :: "('t, 'e) reactive_angelic_design" and c X
  proof -
    have a: "S (ades_obs False s0 c X) =
        (S (ades_obs False s0 c (rad_trace_extensions s0 \<inter> X)) \<and> rad_trace_extensions s0 \<inter> X \<noteq> {})"
      using RA1_obs[of S False s0 c X] by (simp only: Healthy_if[OF RAD_is_RA1[OF that]])
    have b: "S (ades_obs False s0 c X) = (S (ades_obs False s0 c X) \<or> rad_trace_extensions s0 \<inter> X \<noteq> {})"
      using CSPA1_obs[of S False s0 c X] by (simp only: Healthy_if[OF RAD_is_CSPA1[OF that]] simp_thms)
    show ?thesis using a b by blast
  qed
  have up: "S (ades_obs True s0 True X')"
    if "S is RAD" "S (ades_obs True s0 True X)" "X \<subseteq> X'"
    for S :: "('t, 'e) reactive_angelic_design" and X X'
    by (rule PBMH_ades_upward[OF RAD_is_PBMH_ades[OF that(1)] that(2)]; simp add: that(3))
  have ndt: "c \<and> X \<noteq> {}" if "S is NDRAD" "S (ades_obs True s0 c X)"
    for S :: "('t, 'e) reactive_angelic_design" and c X
  proof -
    have "Choice\<^sub>R\<^sub>A\<^sub>D (ades_obs True s0 c X)"
      using that(2) by (subst (asm) Healthy_if[OF that(1), symmetric]) (simp add: NDRAD_def inf_fun_def)
    then show ?thesis
      unfolding Choice_RAD_design RA1_obs by (simp add: design_def; pred_auto)
  qed
  let ?M = "\<lambda>a b sa sb s'. merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = a, \<dots> = sa\<rparr> \<lparr>ok\<^sub>v = b, \<dots> = sb\<rparr>
    \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>"
  show "((P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P' \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac') =
        ((P \<squnion>\<^sub>R\<^sub>A\<^sub>D P') \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis
      by (simp add: rad_par_eval inf_fun_def inf_bool_def un[OF rad(1)] un[OF rad(2)])
  next
    case True
    show ?thesis
    proof
      assume "((P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P' \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac')"
      then obtain okL X okR Y okL' X' okR' Y' where
        px: "P (ades_obs True s0 okL X)" and qy: "Q (ades_obs True s0 okR Y)"
        and h: "\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>ac'. ?M okL okR sL sR s'"
        and px': "P' (ades_obs True s0 okL' X')" and qy': "Q (ades_obs True s0 okR' Y')"
        and h': "\<forall>sL\<in>X'. \<forall>sR\<in>Y'. \<exists>s'\<in>ac'. ?M okL' okR' sL sR s'"
        using True by (simp only: rad_par_eval inf_fun_def inf_bool_def simp_thms) blast
      note ok = ndt[OF nd(1) px] ndt[OF nd(3) qy]
        ndt[OF nd(2) px'] ndt[OF nd(3) qy']
      have T: "P (ades_obs True s0 True X)" "P' (ades_obs True s0 True X')"
          "Q (ades_obs True s0 True Y)" "Q (ades_obs True s0 True Y')"
        using px px' qy qy' ok by simp_all
      have cover: "\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>ac'. ?M True True sL sR s'"
          "\<forall>sL\<in>X'. \<forall>sR\<in>Y'. \<exists>s'\<in>ac'. ?M True True sL sR s'"
        using h h' ok by simp_all
      have qi: "Q (ades_obs True s0 True (Y \<inter> Y'))" by (rule q[OF T(3,4)])
      have "((P \<squnion>\<^sub>R\<^sub>A\<^sub>D P') \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 ok' ac')"
        unfolding rad_par_eval inf_fun_def inf_bool_def
        by (rule exI[where x=True], rule exI[where x="X \<union> X'"],
            rule exI[where x=True], rule exI[where x="Y \<inter> Y'"])
           (use up[OF rad(1) T(1) Un_upper1] up[OF rad(2) T(2) Un_upper2] qi ndt[OF nd(3) qi] ok cover in blast)
      then show "((P \<squnion>\<^sub>R\<^sub>A\<^sub>D P') \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')" using True by simp
    next
      assume "((P \<squnion>\<^sub>R\<^sub>A\<^sub>D P') \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac')"
      then show "((P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P' \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)) (ades_obs ok0 s0 ok' ac')"
        unfolding rad_par_eval inf_fun_def inf_bool_def by blast
    qed
  qed
qed

(* (Q \<parallel> P) \<squnion> (Q \<parallel> P') = Q \<parallel> (P \<squnion> P') *)
lemma rad_par_angelic_distl:
  fixes P P' Q :: "('t::trace, 'e) reactive_angelic_design"
  assumes rad: "P is RAD" "P' is RAD"
    and nd: "P is NDRAD" "P' is NDRAD" "Q is NDRAD"
    and q: "\<And>s0 Y Y'. Q (ades_obs True s0 True Y) \<Longrightarrow> Q (ades_obs True s0 True Y') \<Longrightarrow>
      Q (ades_obs True s0 True (Y \<inter> Y'))"
  shows "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P') = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>R\<^sub>A\<^sub>D P')"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  have un: "S (ades_obs False s0 c X) \<longleftrightarrow> rad_trace_extensions s0 \<inter> X \<noteq> {}"
    if "S is RAD" for S :: "('t, 'e) reactive_angelic_design" and c X
  proof -
    have a: "S (ades_obs False s0 c X) =
        (S (ades_obs False s0 c (rad_trace_extensions s0 \<inter> X)) \<and> rad_trace_extensions s0 \<inter> X \<noteq> {})"
      using RA1_obs[of S False s0 c X] by (simp only: Healthy_if[OF RAD_is_RA1[OF that]])
    have b: "S (ades_obs False s0 c X) = (S (ades_obs False s0 c X) \<or> rad_trace_extensions s0 \<inter> X \<noteq> {})"
      using CSPA1_obs[of S False s0 c X] by (simp only: Healthy_if[OF RAD_is_CSPA1[OF that]] simp_thms)
    show ?thesis using a b by blast
  qed
  have up: "S (ades_obs True s0 True X')"
    if "S is RAD" "S (ades_obs True s0 True X)" "X \<subseteq> X'"
    for S :: "('t, 'e) reactive_angelic_design" and X X'
    by (rule PBMH_ades_upward[OF RAD_is_PBMH_ades[OF that(1)] that(2)]; simp add: that(3))
  have ndt: "c \<and> X \<noteq> {}" if "S is NDRAD" "S (ades_obs True s0 c X)"
    for S :: "('t, 'e) reactive_angelic_design" and c X
  proof -
    have "Choice\<^sub>R\<^sub>A\<^sub>D (ades_obs True s0 c X)"
      using that(2) by (subst (asm) Healthy_if[OF that(1), symmetric]) (simp add: NDRAD_def inf_fun_def)
    then show ?thesis
      unfolding Choice_RAD_design RA1_obs by (simp add: design_def; pred_auto)
  qed
  let ?M = "\<lambda>a b sa sb s'. merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = a, \<dots> = sa\<rparr> \<lparr>ok\<^sub>v = b, \<dots> = sb\<rparr>
    \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>"
  show "((Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac') =
        (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>R\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case False
    then show ?thesis
      by (simp add: rad_par_eval inf_fun_def inf_bool_def un[OF rad(1)] un[OF rad(2)])
  next
    case True
    show ?thesis
    proof
      assume "((Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac')"
      then obtain okL X okR Y okL' X' okR' Y' where
        px: "P (ades_obs True s0 okL X)" and qy: "Q (ades_obs True s0 okR Y)"
        and h: "\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>ac'. ?M okR okL sR sL s'"
        and px': "P' (ades_obs True s0 okL' X')" and qy': "Q (ades_obs True s0 okR' Y')"
        and h': "\<forall>sL\<in>X'. \<forall>sR\<in>Y'. \<exists>s'\<in>ac'. ?M okR' okL' sR sL s'"
        using True by (simp only: rad_par_eval inf_fun_def inf_bool_def simp_thms) blast
      note ok = ndt[OF nd(1) px] ndt[OF nd(3) qy]
        ndt[OF nd(2) px'] ndt[OF nd(3) qy']
      have T: "P (ades_obs True s0 True X)" "P' (ades_obs True s0 True X')"
          "Q (ades_obs True s0 True Y)" "Q (ades_obs True s0 True Y')"
        using px px' qy qy' ok by simp_all
      have cover: "\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>ac'. ?M True True sR sL s'"
          "\<forall>sL\<in>X'. \<forall>sR\<in>Y'. \<exists>s'\<in>ac'. ?M True True sR sL s'"
        using h h' ok by simp_all
      have qi: "Q (ades_obs True s0 True (Y \<inter> Y'))" by (rule q[OF T(3,4)])
      have "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>R\<^sub>A\<^sub>D P')) (ades_obs True s0 ok' ac')"
        unfolding rad_par_eval inf_fun_def inf_bool_def
        by (rule exI[where x=True], rule exI[where x="Y \<inter> Y'"],
            rule exI[where x=True], rule exI[where x="X \<union> X'"])
           (use up[OF rad(1) T(1) Un_upper1] up[OF rad(2) T(2) Un_upper2] qi ndt[OF nd(3) qi] ok cover in blast)
      then show "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>R\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')" using True by simp
    next
      assume "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (P \<squnion>\<^sub>R\<^sub>A\<^sub>D P')) (ades_obs ok0 s0 ok' ac')"
      then show "((Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P) \<squnion>\<^sub>R\<^sub>A\<^sub>D (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> P')) (ades_obs ok0 s0 ok' ac')"
        unfolding rad_par_eval inf_fun_def inf_bool_def by blast
    qed
  qed
qed


subsubsection \<open>Associativity without A2\<close>

text \<open>A deterministic state merge fixes the intermediate result for each
  branch pair, so associativity does not require A2. Nondivergence excludes
  trace extension by divergent intermediate observations; j may be partial.\<close>

lemma merge_rad_guard_AssocMerge:
  fixes j :: "('t::trace \<times> 'e set) merge"
  assumes det: "Functional j" and assoc: "AssocMerge j"
  shows "AssocMerge (merge_guard
    (\<lambda>x z. des_vars.ok\<^sub>v x \<and> \<not> rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<longrightarrow> des_vars.ok\<^sub>v z)
    (merge_rad j))"
proof -
  (* started, non-waiting observations preserve termination *)
  let ?G = "\<lambda>x z. des_vars.ok\<^sub>v x \<and> \<not> rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<longrightarrow> des_vars.ok\<^sub>v z"
  (* the state merge with all termination flags true *)
  let ?K = "\<lambda>s0 sL sR z. merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
    \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = z\<rparr>"
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
  have cyc: "(\<exists>u. ?K s0 sL sR u \<and> ?K s0 u sT z) = (\<exists>u. ?K s0 sR sT u \<and> ?K s0 u sL z)"
    if active: "\<not> rad_wait\<^sub>v s0" for s0 sL sR sT z
    using merge_rdes_guard_AssocMerge[OF assoc, unfolded AssocMerge_iff, rule_format,
      of "\<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>" "\<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr>"
         "\<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr>" "\<lparr>ok\<^sub>v = True, \<dots> = sT\<rparr>"
         "\<lparr>ok\<^sub>v = True, \<dots> = z\<rparr>"] active
    by (simp add: merge_guard_eval des_vars.splits ex_bool_eq)
  (* the smallest middle set collects the unique first-step results *)
  have middle: "(\<exists>okU U.
      (okL \<and> okR \<and> X \<noteq> {} \<and> Y \<noteq> {} \<and> okU \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>u\<in>U. ?K s0 sL sR u)) \<and>
      (okU \<and> okT \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> ok' \<and> (\<forall>u\<in>U. \<forall>sT\<in>V. \<exists>z\<in>ac'. ?K s0 u sT z))) =
    (okL \<and> okR \<and> okT \<and> ok' \<and> X \<noteq> {} \<and> Y \<noteq> {} \<and> V \<noteq> {} \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<forall>sT\<in>V. \<exists>z\<in>ac'. \<exists>u. ?K s0 sL sR u \<and> ?K s0 u sT z))"
    (is "?L = ?R") if active: "\<not> rad_wait\<^sub>v s0" for s0 okL okR okT ok' X Y V ac'
  proof
    assume ?L then show ?R by blast
  next
    assume r: ?R
    let ?U = "{u. \<exists>sL\<in>X. \<exists>sR\<in>Y. ?K s0 sL sR u}"
    have uz: "\<exists>z\<in>ac'. ?K s0 u sT z" if "u \<in> ?U" "sT \<in> V" for u sT
      using that r uniq[OF active] by blast
    show ?L by (rule exI[where x=True], rule exI[where x="?U"]) (use r uz in blast)
  qed
  have active_obs: "merge_eval (merge_guard ?G (merge_rad j))
      \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr> (ades_output okL X) (ades_output okR Y) (ades_output ok' ac') =
    (okL \<and> okR \<and> X \<noteq> {} \<and> Y \<noteq> {} \<and> ok' \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>z\<in>ac'. ?K s0 sL sR z))"
    if "\<not> rad_wait\<^sub>v s0" for s0 okL X okR Y ok' ac'
    using that
    by (cases okL; cases okR; cases ok';
        simp add: merge_guard_eval rad_lift_merge_obs[simplified] merge_rdes_eval; blast)
  have unstarted_obs: "merge_eval (merge_guard ?G (merge_rad j))
      \<lparr>ok\<^sub>v = False, s\<^sub>v = s0, \<dots> = ()\<rparr> (ades_output okL X) (ades_output okR Y) (ades_output ok' ac') =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> rad_trace_extensions s0 \<inter> ac' \<noteq> {})"
    for s0 okL X okR Y ok' ac'
    by (cases ok'; auto simp: merge_guard_eval rad_lift_merge_obs[simplified]
        merge_rdes_eval rad_trace_extensions_def; blast)
  have waiting_obs: "merge_eval (merge_guard ?G (merge_rad j))
      \<lparr>ok\<^sub>v = True, s\<^sub>v = s0, \<dots> = ()\<rparr> (ades_output okL X) (ades_output okR Y) (ades_output ok' ac') =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> ok' \<and> s0 \<in> ac')"
    if "rad_wait\<^sub>v s0" for s0 okL X okR Y ok' ac'
    using that by (auto simp: merge_guard_eval rad_lift_merge_obs[simplified] merge_rdes_eval; blast)
  show ?thesis
    unfolding AssocMerge_iff
    apply (intro allI)
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okL X okR Y okT V ok' ac'
    proof (cases "ok0 \<and> \<not> rad_wait\<^sub>v s0")
      case True
      then have started: ok0 and active: "\<not> rad_wait\<^sub>v s0" by simp_all
      show ?thesis
        apply (simp only: started choices_ex active_obs[OF active] middle[OF active])
        using cyc[OF active] by blast
    next
      case False
      then show ?thesis
        by (cases ok0; simp add: choices_ex unstarted_obs waiting_obs;
            blast intro: exI[where x="{s0}"])
    qed
    done
qed

(* Determinism replaces A2; nondivergence keeps trace completion inactive. *)
theorem rad_par_assoc_det_nd:
  fixes P Q R :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t \<times> 'e set) merge"
  assumes nondiv: "P is NDRAD" "Q is NDRAD" "R is NDRAD"
    and det: "Functional j" and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R =
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
proof -
  let ?G = "\<lambda>x z. des_vars.ok\<^sub>v x \<and> \<not> rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<longrightarrow> des_vars.ok\<^sub>v z"
  (* the merge keeps nondivergent branches nondivergent *)
  have closed: "\<And>x p q z. \<lbrakk>?G x p; ?G x q; merge_eval (merge_rad j) x p q z\<rbrakk> \<Longrightarrow> ?G x z"
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okL X okR Y ok' ac'
      by (auto simp: rad_lift_merge_obs[simplified] merge_rdes_eval)
    done
  (* nondivergent operands satisfy the guard *)
  have nd: "\<And>x z. S (x, z) \<Longrightarrow> ?G x z" if "S is NDRAD" for S :: "('t, 'e) reactive_angelic_design"
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 ok' ac'
    proof -
      assume "S (ades_obs ok0 s0 ok' ac')"
      then have "Choice\<^sub>R\<^sub>A\<^sub>D (ades_obs ok0 s0 ok' ac')"
        by (subst (asm) Healthy_if[OF that, symmetric]) (simp add: NDRAD_def inf_fun_def)
      then show ?thesis
        unfolding Choice_RAD_design RA1_obs by (simp add: design_def; pred_auto)
    qed
    done
  show ?thesis
    by (rule par_by_merge_assoc_guard[OF
        SymMerge_merge_guard[OF rad_lift_merge_SymMerge[OF merge_rdes_SymMerge[OF sym]]]
        merge_rad_guard_AssocMerge[OF det assoc] closed
        nd[OF nondiv(1)] nd[OF nondiv(2)] nd[OF nondiv(3)]])
qed

end
