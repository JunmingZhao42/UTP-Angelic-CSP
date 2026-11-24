theory AD_Seq_Par
  imports "UTP-Angelic-Designs.utp_ades"
begin

text \<open>We state the sequential comparisons of the geometry review for the real AD
  operators. The branches use separate parts of the state: P ignores a lens a, Q uses
  only a, and the merge j takes a from Q and the rest from P. Then
  P ;; Q \<sqsubseteq> P \<parallel> Q and Q ;; P \<sqsubseteq> P \<parallel> Q. These laws stay in the review: they hold for
  one merge and need independence premises, unlike the production laws for any j.\<close>

section \<open>Evaluation\<close>

(* For nondivergent operands, P ;; Q offers ac' when P offers the states from which
   Q offers ac'. *)
lemma ades_seq_eval:
  assumes "P is A" "P is NDAD" "Q is NDAD"
  shows "(P ;;\<^sub>A\<^sub>D Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not>ok0 \<or> ok' \<and> P (ades_obs True s0 True {s'. Q (ades_obs True s' True ac')}))"
proof -
  have p: "\<And>X. \<not> P (ades_obs True s0 False X)" "\<not> P (ades_obs True s0 True {})"
    using assms(2) unfolding NDAD_healthy_obs_iff by blast+
  have q: "\<And>s'. \<not> Q (ades_obs True s' False ac')"
    using assms(3) unfolding NDAD_healthy_obs_iff by blast
  have un: "\<And>ok' X. P (ades_obs False s0 ok' X)"
    using assms(1) by (simp add: A_healthy_components_iff H1_healthy_obs_iff)
  show ?thesis
    by (cases ok0; cases ok'; simp add: angelic_design_seq_def ex_bool_eq p q un)
qed

(* When j takes a from the right branch and the rest from the left, a started
   parallel offers ac' when ac' holds sL \<oplus> sR on a for some offered acL and acR. *)
lemma ades_par_override_eval:
  fixes P Q :: "'s angelic_design"
  assumes h: "P is A" "Q is A" and nd: "P is NDAD" "Q is NDAD"
    and j: "\<And>s0 sL sR s'. merge_eval j s0 sL sR s' \<longleftrightarrow> s' = sL \<oplus>\<^sub>L sR on a"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not>ok0 \<or> ok' \<and> (\<exists>acL acR. P (ades_obs True s0 True acL) \<and> Q (ades_obs True s0 True acR) \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. sL \<oplus>\<^sub>L sR on a \<in> ac')))"
proof -
  have ndt: "c \<and> X \<noteq> {}" if "S is NDAD" "S (ades_obs True s0 c X)" for S :: "'s angelic_design" and c X
    using NDAD_obs[of S True s0 c X] that by (simp add: Healthy_if[OF that(1)])
  have un: "S (ades_obs False s0 c X)" if "S is A" for S :: "'s angelic_design" and c X
    using that by (simp add: A_healthy_components_iff H1_healthy_obs_iff)
  show ?thesis
  proof (cases ok0)
    case False
    then show ?thesis by (simp add: ades_par_eval un[OF h(1)] un[OF h(2)])
  next
    case True
    let ?R = "\<exists>acL acR. P (ades_obs True s0 True acL) \<and> Q (ades_obs True s0 True acR) \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. sL \<oplus>\<^sub>L sR on a \<in> ac')"
    have "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 ok' ac') \<longleftrightarrow> ok' \<and> ?R"
    proof
      assume "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 ok' ac')"
      then obtain okL acL okR acR where p: "P (ades_obs True s0 okL acL)"
        and q: "Q (ades_obs True s0 okR acR)"
        and m: "okL \<and> okR \<longrightarrow> ok' \<and> (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s')"
        unfolding ades_par_eval by blast
      have ok: "okL" "okR" using ndt[OF nd(1) p] ndt[OF nd(2) q] by simp_all
      show "ok' \<and> ?R" using p q m ok by (auto simp: j)
    next
      assume "ok' \<and> ?R"
      then obtain acL acR where ok': ok' and p: "P (ades_obs True s0 True acL)"
        and q: "Q (ades_obs True s0 True acR)"
        and m: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. sL \<oplus>\<^sub>L sR on a \<in> ac'" by blast
      show "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 ok' ac')"
        unfolding ades_par_eval
        by (rule exI[where x=True], rule exI[where x=acL], rule exI[where x=True], rule exI[where x=acR])
           (use p q m ok' ndt[OF nd(1) p] ndt[OF nd(2) q] in \<open>simp add: j\<close>)
    qed
    then show ?thesis using True by simp
  qed
qed

(* An A-healthy design offers every superset of an offered set. *)
lemma A_obs_upward:
  fixes S :: "'s angelic_design"
  assumes "S is A" "S (ades_obs True s0 True X)" "X \<subseteq> X'"
  shows "S (ades_obs True s0 True X')"
proof -
  have pb: "S is PBMH_ades" using assms(1) by (simp add: A_healthy_components_iff)
  show ?thesis by (rule PBMH_ades_upward[OF pb assms(2)]; simp add: assms(3))
qed

(* Refinement holds when it holds at every AD observation. *)
lemma ades_obs_refine:
  fixes P Q :: "'s angelic_design"
  assumes "\<And>b s0 c X. Q (ades_obs b s0 c X) \<Longrightarrow> P (ades_obs b s0 c X)"
  shows "P \<sqsubseteq> Q"
  using assms by (simp add: pred_refine_iff; pred_auto)

section \<open>Laws\<close>

(* P ;; Q \<sqsubseteq> P \<parallel> Q *)
lemma ades_par_refines_seq:
  fixes P Q :: "'s angelic_design"
  assumes lens: "vwb_lens a"
    and h: "P is A" "Q is A" and nd: "P is NDAD" "Q is NDAD"
    and j: "\<And>s0 sL sR s'. merge_eval j s0 sL sR s' \<longleftrightarrow> s' = sL \<oplus>\<^sub>L sR on a"
    and p: "\<And>s0 t X. P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
      P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
    and q: "\<And>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
      Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
  shows "P ;;\<^sub>A\<^sub>D Q \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
proof -
  have obs: "P (ades_obs True s0 True {s1. Q (ades_obs True s1 True ac')})"
    if pl: "P (ades_obs True s0 True acL)" and qr: "Q (ades_obs True s0 True acR)"
      and m: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. sL \<oplus>\<^sub>L sR on a \<in> ac'" for s0 acL acR ac'
  proof -
    let ?S = "(\<lambda>s'. s' \<oplus>\<^sub>L s0 on a) ` acL"
    have "P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L s0 on a \<in> ?S})"
      by (rule A_obs_upward[OF h(1) pl]) blast
    then have pS: "P (ades_obs True s0 True ?S)"
      using p[of s0 s0 ?S] lens by simp
    have "Q (ades_obs True s1 True ac')" if "s1 \<in> ?S" for s1
    proof -
      obtain sL where sL: "sL \<in> acL" "s1 = sL \<oplus>\<^sub>L s0 on a" using \<open>s1 \<in> ?S\<close> by blast
      have "Q (ades_obs True s0 True {s'. sL \<oplus>\<^sub>L s' on a \<in> ac'})"
        by (rule A_obs_upward[OF h(2) qr]) (use sL m in blast)
      then show ?thesis using q[of sL s0 ac'] sL by simp
    qed
    then show ?thesis by (intro A_obs_upward[OF h(1) pS]) blast
  qed
  show ?thesis
    by (rule ades_obs_refine)
       (auto simp: ades_par_override_eval[OF h nd j] ades_seq_eval[OF h(1) nd] intro: obs)
qed

(* Q ;; P \<sqsubseteq> P \<parallel> Q *)
lemma ades_par_refines_seq_swap:
  fixes P Q :: "'s angelic_design"
  assumes lens: "vwb_lens a"
    and h: "P is A" "Q is A" and nd: "P is NDAD" "Q is NDAD"
    and j: "\<And>s0 sL sR s'. merge_eval j s0 sL sR s' \<longleftrightarrow> s' = sL \<oplus>\<^sub>L sR on a"
    and p: "\<And>s0 t X. P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
      P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
    and q: "\<And>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
      Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
  shows "Q ;;\<^sub>A\<^sub>D P \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
proof -
  have obs: "Q (ades_obs True s0 True {s1. P (ades_obs True s1 True ac')})"
    if pl: "P (ades_obs True s0 True acL)" and qr: "Q (ades_obs True s0 True acR)"
      and m: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. sL \<oplus>\<^sub>L sR on a \<in> ac'" for s0 acL acR ac'
  proof -
    let ?S = "(\<lambda>s'. s0 \<oplus>\<^sub>L s' on a) ` acR"
    have "Q (ades_obs True s0 True {s'. s0 \<oplus>\<^sub>L s' on a \<in> ?S})"
      by (rule A_obs_upward[OF h(2) qr]) blast
    then have qS: "Q (ades_obs True s0 True ?S)"
      using q[of s0 s0 ?S] lens by simp
    have "P (ades_obs True s1 True ac')" if "s1 \<in> ?S" for s1
    proof -
      obtain sR where sR: "sR \<in> acR" "s1 = s0 \<oplus>\<^sub>L sR on a" using \<open>s1 \<in> ?S\<close> by blast
      have "P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L sR on a \<in> ac'})"
        by (rule A_obs_upward[OF h(1) pl]) (use sR m in blast)
      then show ?thesis using p[of s0 sR ac'] sR by simp
    qed
    then show ?thesis by (intro A_obs_upward[OF h(2) qS]) blast
  qed
  show ?thesis
    by (rule ades_obs_refine)
       (auto simp: ades_par_override_eval[OF h nd j] ades_seq_eval[OF h(2) nd(2,1)] intro: obs)
qed

(* P \<parallel> Q = P ;; Q when P has no angelic choice *)
lemma ades_par_eq_seq:
  fixes P Q :: "'s angelic_design"
  assumes lens: "vwb_lens a"
    and h: "P is A" "Q is A" and nd: "P is NDAD" "Q is NDAD"
    and j: "\<And>s0 sL sR s'. merge_eval j s0 sL sR s' \<longleftrightarrow> s' = sL \<oplus>\<^sub>L sR on a"
    and p: "\<And>s0 t X. P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
      P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
    and q: "\<And>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
      Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
    and a2: "P is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = P ;;\<^sub>A\<^sub>D Q"
proof (rule ref_antisym)
  have obs: "\<exists>acL acR. P (ades_obs True s0 True acL) \<and> Q (ades_obs True s0 True acR) \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. sL \<oplus>\<^sub>L sR on a \<in> ac')"
    if ps: "P (ades_obs True s0 True {s1. Q (ades_obs True s1 True ac')})" for s0 ac'
  proof -
    let ?S = "{s'. s' \<oplus>\<^sub>L s0 on a \<in> {s1. Q (ades_obs True s1 True ac')}}"
    have "P (ades_obs True s0 True ?S)"
      using p[of s0 s0 "{s1. Q (ades_obs True s1 True ac')}"] ps lens by simp
    moreover have "\<not> P (ades_obs True s0 True {})"
      using nd(1) unfolding NDAD_healthy_obs_iff by blast
    ultimately obtain z where z: "z \<in> ?S" "P (ades_obs True s0 True {z})"
      using A2_obs[of P True s0 True ?S] by (simp only: Healthy_if[OF a2]; blast)
    have "Q (ades_obs True s0 True {s'. z \<oplus>\<^sub>L s' on a \<in> ac'})"
      using z(1) q[of z s0 ac'] by simp
    with z(2) show ?thesis by blast
  qed
  show "P ;;\<^sub>A\<^sub>D Q \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
    using lens h nd j p q by (rule ades_par_refines_seq)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> P ;;\<^sub>A\<^sub>D Q"
  proof (rule ades_obs_refine)
    fix b s0 c X
    assume "(P ;;\<^sub>A\<^sub>D Q) (ades_obs b s0 c X)"
    then show "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs b s0 c X)"
      unfolding ades_par_override_eval[OF h nd j] ades_seq_eval[OF h(1) nd] using obs by blast
  qed
qed

(* P \<parallel> Q = Q ;; P when P has no demonic choice *)
lemma ades_par_eq_seq_swap:
  fixes P Q :: "'s angelic_design"
  assumes lens: "vwb_lens a"
    and h: "P is A" "Q is A" and nd: "P is NDAD" "Q is NDAD"
    and j: "\<And>s0 sL sR s'. merge_eval j s0 sL sR s' \<longleftrightarrow> s' = sL \<oplus>\<^sub>L sR on a"
    and p: "\<And>s0 t X. P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
      P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
    and q: "\<And>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
      Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
    and least: "\<And>s0. \<exists>Y. \<forall>X. P (ades_obs True s0 True X) \<longleftrightarrow> Y \<subseteq> X"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = Q ;;\<^sub>A\<^sub>D P"
proof (rule ref_antisym)
  have obs: "\<exists>acL acR. P (ades_obs True s0 True acL) \<and> Q (ades_obs True s0 True acR) \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. sL \<oplus>\<^sub>L sR on a \<in> ac')"
    if qs: "Q (ades_obs True s0 True {s1. P (ades_obs True s1 True ac')})" for s0 ac'
  proof -
    obtain Y where Y: "\<And>X. P (ades_obs True s0 True X) \<longleftrightarrow> Y \<subseteq> X" using least by blast
    let ?R = "{s'. s0 \<oplus>\<^sub>L s' on a \<in> {s1. P (ades_obs True s1 True ac')}}"
    have r: "Q (ades_obs True s0 True ?R)"
      using q[of s0 s0 "{s1. P (ades_obs True s1 True ac')}"] qs lens by simp
    have "sL \<oplus>\<^sub>L sR on a \<in> ac'" if "sL \<in> Y" "sR \<in> ?R" for sL sR
      using that p[of s0 sR ac'] Y by auto
    with r Y show ?thesis by blast
  qed
  show "Q ;;\<^sub>A\<^sub>D P \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
    using lens h nd j p q by (rule ades_par_refines_seq_swap)
  show "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> Q ;;\<^sub>A\<^sub>D P"
  proof (rule ades_obs_refine)
    fix b s0 c X
    assume "(Q ;;\<^sub>A\<^sub>D P) (ades_obs b s0 c X)"
    then show "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs b s0 c X)"
      unfolding ades_par_override_eval[OF h nd j] ades_seq_eval[OF h(2) nd(2,1)] using obs by blast
  qed
qed

(* (P \<parallel> Q) ;; (P' \<parallel> Q') \<sqsubseteq> (P ;; P') \<parallel> (Q ;; Q') *)
lemma ades_par_seq_exchange:
  fixes P Q P' Q' :: "'s angelic_design"
  assumes lens: "vwb_lens a"
    and h: "P is A" "Q is A" "P' is A" "Q' is A"
    and nd: "P is NDAD" "Q is NDAD" "P' is NDAD" "Q' is NDAD"
    and j: "\<And>s0 sL sR s'. merge_eval j s0 sL sR s' \<longleftrightarrow> s' = sL \<oplus>\<^sub>L sR on a"
    and p: "\<And>s0 t X. P' (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
      P' (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
    and q: "\<And>s0 t X. Q' (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
      Q' (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) ;;\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q') \<sqsubseteq>
    (P ;;\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q ;;\<^sub>A\<^sub>D Q')"
proof -
  have ne: "\<not> S (ades_obs True s0 True {})" if "S is NDAD" for S :: "'s angelic_design" and s0
    using that unfolding NDAD_healthy_obs_iff by blast
  have seq_nd: "(S ;;\<^sub>A\<^sub>D S') is NDAD"
    if "S is A" "S is NDAD" "S' is NDAD" for S S' :: "'s angelic_design"
    by (auto simp: NDAD_healthy_obs_iff ades_seq_eval[OF that] ne[OF that(2)] ne[OF that(3)])
  have par_nd: "(S \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> S') is NDAD"
    if "S is A" "S' is A" "S is NDAD" "S' is NDAD" for S S' :: "'s angelic_design"
    unfolding NDAD_healthy_obs_iff ades_par_override_eval[OF that j]
    using ne[OF that(3)] ne[OF that(4)] by (simp; metis ex_in_conv)
  have par_a: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
    by (rule ades_par_A_closure) (use h(1,2) in \<open>simp_all add: A_healthy_components_iff\<close>)
  note sa = angelic_design_seq_A_closure[OF h(1,3)] angelic_design_seq_A_closure[OF h(2,4)]
  note sn = seq_nd[OF h(1) nd(1,3)] seq_nd[OF h(2) nd(2,4)]
  have obs: "P (ades_obs True s0 True {u. P' (ades_obs True u True XL)}) \<Longrightarrow>
      Q (ades_obs True s0 True {u. Q' (ades_obs True u True XR)}) \<Longrightarrow>
      \<forall>sL\<in>XL. \<forall>sR\<in>XR. sL \<oplus>\<^sub>L sR on a \<in> ac' \<Longrightarrow>
      (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs True s0 True {u. (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q') (ades_obs True u True ac')})"
    for s0 XL XR ac'
  proof -
    assume pl: "P (ades_obs True s0 True {u. P' (ades_obs True u True XL)})"
      and qr: "Q (ades_obs True s0 True {u. Q' (ades_obs True u True XR)})"
      and m: "\<forall>sL\<in>XL. \<forall>sR\<in>XR. sL \<oplus>\<^sub>L sR on a \<in> ac'"
    have mid: "(P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q') (ades_obs True (uL \<oplus>\<^sub>L uR on a) True ac')"
      if pa: "P' (ades_obs True uL True XL)" and qb: "Q' (ades_obs True uR True XR)" for uL uR
    proof -
      let ?L = "(\<lambda>s'. s' \<oplus>\<^sub>L uR on a) ` XL" and ?R = "(\<lambda>s'. uL \<oplus>\<^sub>L s' on a) ` XR"
      have "P' (ades_obs True uL True {s'. s' \<oplus>\<^sub>L uR on a \<in> ?L})"
        by (rule A_obs_upward[OF h(3) pa]) blast
      then have l: "P' (ades_obs True (uL \<oplus>\<^sub>L uR on a) True ?L)" using p[of uL uR ?L] by simp
      have "Q' (ades_obs True uR True {s'. uL \<oplus>\<^sub>L s' on a \<in> ?R})"
        by (rule A_obs_upward[OF h(4) qb]) blast
      then have r: "Q' (ades_obs True (uL \<oplus>\<^sub>L uR on a) True ?R)" using q[of uL uR ?R] by simp
      have "\<forall>sL\<in>?L. \<forall>sR\<in>?R. sL \<oplus>\<^sub>L sR on a \<in> ac'"
        using m lens by (auto simp: lens_override_overshadow_left lens_override_overshadow_right)
      with l r show ?thesis unfolding ades_par_override_eval[OF h(3,4) nd(3,4) j] by blast
    qed
    show ?thesis
      unfolding ades_par_override_eval[OF h(1,2) nd(1,2) j]
      using pl qr mid by blast
  qed
  show ?thesis
  proof (rule ades_obs_refine)
    fix b s0 c X
    assume "((P ;;\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q ;;\<^sub>A\<^sub>D Q')) (ades_obs b s0 c X)"
    then show "((P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) ;;\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q')) (ades_obs b s0 c X)"
      unfolding ades_par_override_eval[OF sa sn j] ades_seq_eval[OF h(1) nd(1,3)]
        ades_seq_eval[OF h(2) nd(2,4)]
        ades_seq_eval[OF par_a par_nd[OF h(1,2) nd(1,2)] par_nd[OF h(3,4) nd(3,4)]]
      using obs by blast
  qed
qed


section \<open>Reading the premises\<close>

(* An AD assignment offers the sets that hold the assigned state. *)
lemma assigns_ades_obs:
  "assigns_ades x e (ades_obs b s0 c X) \<longleftrightarrow> (b \<longrightarrow> c \<and> put\<^bsub>x\<^esub> s0 (e s0) \<in> X)"
  by (simp add: assigns_ades_def assign_arel_def arel_to_ades_def; pred_auto)

(* An assignment before or after a nondivergent P moves the prior or the offered sets. *)
lemma assigns_seq_eval:
  fixes P :: "'s angelic_design"
  assumes "P is A" "P is NDAD"
  shows "(assigns_ades x e ;;\<^sub>A\<^sub>D P) (ades_obs b s0 c X) \<longleftrightarrow>
      (b \<longrightarrow> P (ades_obs True (put\<^bsub>x\<^esub> s0 (e s0)) c X))"
    and "(P ;;\<^sub>A\<^sub>D assigns_ades x e) (ades_obs b s0 c X) \<longleftrightarrow>
      (b \<longrightarrow> c \<and> P (ades_obs True s0 True {s1. put\<^bsub>x\<^esub> s1 (e s1) \<in> X}))"
proof -
  have nd: "\<And>s0 X. \<not> P (ades_obs True s0 False X)" "\<And>s0. \<not> P (ades_obs True s0 True {})"
    using assms(2) unfolding NDAD_healthy_obs_iff by blast+
  have un: "\<And>s0 c X. P (ades_obs False s0 c X)"
    using assms(1) by (simp add: A_healthy_components_iff H1_healthy_obs_iff)
  show "(assigns_ades x e ;;\<^sub>A\<^sub>D P) (ades_obs b s0 c X) \<longleftrightarrow>
      (b \<longrightarrow> P (ades_obs True (put\<^bsub>x\<^esub> s0 (e s0)) c X))"
    by (cases b; simp add: angelic_design_seq_def ex_bool_eq assigns_ades_obs un)
  show "(P ;;\<^sub>A\<^sub>D assigns_ades x e) (ades_obs b s0 c X) \<longleftrightarrow>
      (b \<longrightarrow> c \<and> P (ades_obs True s0 True {s1. put\<^bsub>x\<^esub> s1 (e s1) \<in> X}))"
    by (cases b; cases c; simp add: angelic_design_seq_def ex_bool_eq assigns_ades_obs un nd)
qed

(* The left premise of the laws says that P commutes with every assignment to a. *)
lemma ignores_lens_iff:
  fixes P :: "'s angelic_design"
  assumes lens: "vwb_lens a" and a: "P is A" "P is NDAD"
  shows "(\<forall>s0 t X. P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
            P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})) \<longleftrightarrow>
         (\<forall>v. assigns_ades a (\<lambda>_. v) ;;\<^sub>A\<^sub>D P = P ;;\<^sub>A\<^sub>D assigns_ades a (\<lambda>_. v))"
proof
  assume p: "\<forall>s0 t X. P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
            P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
  have nd: "\<And>s0 X. \<not> P (ades_obs True s0 False X)"
    using a(2) unfolding NDAD_healthy_obs_iff by blast
  show "\<forall>v. assigns_ades a (\<lambda>_. v) ;;\<^sub>A\<^sub>D P = P ;;\<^sub>A\<^sub>D assigns_ades a (\<lambda>_. v)"
  proof (intro allI ades_obs_ext)
    fix v b s0 c X
    have "P (ades_obs True (put\<^bsub>a\<^esub> s0 v) True X) \<longleftrightarrow>
        P (ades_obs True s0 True {s1. put\<^bsub>a\<^esub> s1 v \<in> X})"
      using p[rule_format, of s0 "put\<^bsub>a\<^esub> s0 v" X] lens by (simp add: lens_override_def)
    then show "(assigns_ades a (\<lambda>_. v) ;;\<^sub>A\<^sub>D P) (ades_obs b s0 c X) =
        (P ;;\<^sub>A\<^sub>D assigns_ades a (\<lambda>_. v)) (ades_obs b s0 c X)"
      by (cases c; simp add: assigns_seq_eval[OF a] nd)
  qed
next
  assume e: "\<forall>v. assigns_ades a (\<lambda>_. v) ;;\<^sub>A\<^sub>D P = P ;;\<^sub>A\<^sub>D assigns_ades a (\<lambda>_. v)"
  show "\<forall>s0 t X. P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
            P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
  proof (intro allI)
    fix s0 t X
    have "(assigns_ades a (\<lambda>_. get\<^bsub>a\<^esub> t) ;;\<^sub>A\<^sub>D P) (ades_obs True s0 True X) =
        (P ;;\<^sub>A\<^sub>D assigns_ades a (\<lambda>_. get\<^bsub>a\<^esub> t)) (ades_obs True s0 True X)"
      by (simp only: e[rule_format])
    then show "P (ades_obs True (s0 \<oplus>\<^sub>L t on a) True X) \<longleftrightarrow>
            P (ades_obs True s0 True {s'. s' \<oplus>\<^sub>L t on a \<in> X})"
      by (simp add: assigns_seq_eval[OF a] lens_override_def)
  qed
qed

(* The right premise of the laws says that Q commutes with every assignment that keeps a. *)
lemma uses_only_lens_iff:
  fixes Q :: "'s angelic_design"
  assumes lens: "vwb_lens a" and a: "Q is A" "Q is NDAD"
  shows "(\<forall>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
            Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})) \<longleftrightarrow>
         (\<forall>t. assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q =
              Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a))"
proof -
  have nd: "\<And>s0 X. \<not> Q (ades_obs True s0 False X)"
    using a(2) unfolding NDAD_healthy_obs_iff by blast
  have "(\<forall>t. assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q =
              Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)) \<longleftrightarrow>
        (\<forall>t b s0 c X. (assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q) (ades_obs b s0 c X) =
              (Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)) (ades_obs b s0 c X))"
  proof
    assume "\<forall>t. assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q =
              Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)"
    then show "\<forall>t b s0 c X. (assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q) (ades_obs b s0 c X) =
              (Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)) (ades_obs b s0 c X)"
      by simp
  next
    assume "\<forall>t b s0 c X. (assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q) (ades_obs b s0 c X) =
              (Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)) (ades_obs b s0 c X)"
    then show "\<forall>t. assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q =
              Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)"
      by (intro allI ades_obs_ext) blast
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
            Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X}))"
  proof
    assume h: "\<forall>t b s0 c X. (assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q) (ades_obs b s0 c X) =
              (Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)) (ades_obs b s0 c X)"
    show "\<forall>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
            Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
    proof (intro allI)
      fix s0 t X
      from h[rule_format, of t True s0 True X]
      show "Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
            Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
        by (simp add: assigns_seq_eval[OF a] id_lens_def)
    qed
  next
    assume h: "\<forall>s0 t X. Q (ades_obs True (t \<oplus>\<^sub>L s0 on a) True X) \<longleftrightarrow>
            Q (ades_obs True s0 True {s'. t \<oplus>\<^sub>L s' on a \<in> X})"
    show "\<forall>t b s0 c X. (assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a) ;;\<^sub>A\<^sub>D Q) (ades_obs b s0 c X) =
              (Q ;;\<^sub>A\<^sub>D assigns_ades 1\<^sub>L (\<lambda>s. t \<oplus>\<^sub>L s on a)) (ades_obs b s0 c X)"
      using h nd by (intro allI; case_tac c; simp add: assigns_seq_eval[OF a] id_lens_def)
  qed
  finally show ?thesis by simp
qed

end
