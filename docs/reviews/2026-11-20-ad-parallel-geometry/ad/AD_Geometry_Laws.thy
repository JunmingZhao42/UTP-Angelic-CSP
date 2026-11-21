theory AD_Geometry_Laws
  imports AD_Geometry_Probe
begin

section \<open>Offered families and their operators\<close>

text \<open>We work with the families R s0 X that ad_of turns into angelic designs, so
  each law is first a statement about sets and then an AD refinement.\<close>

(* sequential composition: P offers the set of states from which Q offers Z *)
definition seqf :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "seqf RP RQ = (\<lambda>s0 Z. RP s0 {y. RQ y Z})"

(* frame-disjoint parallel: Z holds (fst p, snd q) for every offered pair *)
definition parfd ::
  "('a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool) \<Rightarrow>
   'a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" where
  "parfd RP RQ = (\<lambda>s0 Z. \<exists>XL XR. RP s0 XL \<and> RQ s0 XR \<and> (\<forall>p\<in>XL. \<forall>q\<in>XR. (fst p, snd q) \<in> Z))"

(* blocker: the sets G that meet every offered set, i.e. the guaranteed postconditions *)
definition blk :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "blk R = (\<lambda>s0 G. \<forall>X. R s0 X \<longrightarrow> X \<inter> G \<noteq> {})"

(* blind product: the AD product taken on the angel's side of the duality *)
definition blindfd ::
  "('a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool) \<Rightarrow>
   'a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" where
  "blindfd RP RQ = blk (parfd (blk RP) (blk RQ))"

definition upcl :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> bool" where
  "upcl R \<longleftrightarrow> (\<forall>s0 X Y. R s0 X \<longrightarrow> X \<subseteq> Y \<longrightarrow> R s0 Y)"

(* no angelic choice: every offered set contains an offered singleton *)
definition a2f :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> bool" where
  "a2f R \<longleftrightarrow> (\<forall>s0 X. R s0 X \<longleftrightarrow> (\<exists>y\<in>X. R s0 {y}))"

(* no demonic choice: one least offered set *)
definition angf :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> bool" where
  "angf R \<longleftrightarrow> (\<forall>s0. \<exists>A. \<forall>X. R s0 X \<longleftrightarrow> A \<subseteq> X)"

definition fref :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>f" 50) where
  "R1 \<sqsubseteq>\<^sub>f R2 \<longleftrightarrow> (\<forall>s0 Z. R2 s0 Z \<longrightarrow> R1 s0 Z)"

lemma fref_ad_of: "R1 \<sqsubseteq>\<^sub>f R2 \<Longrightarrow> ad_of R1 \<sqsubseteq> ad_of R2"
  unfolding fref_def by (rule ad_of_refine) blast

subsection \<open>Link to the AD operators\<close>

lemma ad_seq_seqf:
  assumes "\<And>s0 X. RP s0 X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of RP ;;\<^sub>D\<^sub>A ad_of RQ = ad_of (seqf RP RQ)"
  unfolding seqf_def by (rule ad_seq_ad_of[where RP=RP and RQ=RQ], fact assms)

lemma ad_par_parfd:
  assumes "\<And>s0 X. RP s0 X \<Longrightarrow> X \<noteq> {}" "\<And>s0 X. RQ s0 X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of RQ = ad_of (parfd RP RQ)"
proof -
  have "ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of RQ = ad_of (\<lambda>s Z. \<exists>XL XR. RP s XL \<and> RQ s XR \<and>
      (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd s sL sR s'))"
    by (rule ad_par_ad_of[where RP=RP and RQ=RQ and j=jfd], fact assms(1), fact assms(2))
  also have "\<dots> = ad_of (parfd RP RQ)"
    by (rule arg_cong[where f=ad_of]) (simp add: parfd_def fun_eq_iff)
  finally show ?thesis .
qed

lemma a2fD: "a2f R \<Longrightarrow> R s0 X = (\<exists>y\<in>X. R s0 {y})"
  unfolding a2f_def by (erule allE)+

lemma upclD: "upcl R \<Longrightarrow> R s0 X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> R s0 Y"
  unfolding upcl_def by (erule allE)+ (erule impE, assumption)+

lemma angfE:
  assumes "angf R"
  obtains A where "\<And>X. R s0 X = (A \<subseteq> X)"
proof -
  from assms obtain A where "\<forall>X. R s0 X = (A \<subseteq> X)" unfolding angf_def by blast
  then show thesis using that by blast
qed

lemma a2f_ne: "a2f U \<Longrightarrow> U t X \<Longrightarrow> X \<noteq> {}"
  by (subst (asm) a2fD) auto

lemma ad_of_A2:
  assumes "a2f R"
  shows "ad_of R is A2"
  unfolding Healthy_def
proof (rule ades_obs_ext)
  fix b s0 c X
  have e: "R s0 {} = False" using a2f_ne[OF assms] by blast
  have x: "R s0 X = (\<exists>y\<in>X. R s0 {y})" by (rule a2fD[OF assms])
  show "A2 (ad_of R) (ades_obs b s0 c X) = ad_of R (ades_obs b s0 c X)"
    unfolding A2_obs ad_of_obs e x by auto
qed

lemma lftL_ne': "(\<And>t X. U t X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow> (\<And>s0 X. lftL U s0 X \<Longrightarrow> X \<noteq> {})"
  unfolding lftL_def by fastforce

lemma lftR_ne': "(\<And>t X. V t X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow> (\<And>s0 X. lftR V s0 X \<Longrightarrow> X \<noteq> {})"
  unfolding lftR_def by fastforce

lemma lftL_img: "U (fst s0) X1 \<Longrightarrow> lftL U s0 ((\<lambda>a. (a, snd s0)) ` X1)"
  unfolding lftL_def by (rule exI[where x=X1]) auto

lemma lftR_img: "V (snd s0) X2 \<Longrightarrow> lftR V s0 ((\<lambda>b. (fst s0, b)) ` X2)"
  unfolding lftR_def by (rule exI[where x=X2]) auto

lemma blkD: "blk R s0 G \<Longrightarrow> R s0 X \<Longrightarrow> X \<inter> G \<noteq> {}"
  unfolding blk_def by (erule allE) (erule impE)

lemma a2f_lftL:
  assumes A: "a2f U"
  shows "a2f (lftL U)"
  unfolding a2f_def
proof (intro allI iffI)
  fix s0 and X
  {
    assume "lftL U s0 X"
    then obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. (a, snd s0) \<in> X"
      unfolding lftL_def by blast
    obtain x where x: "x \<in> X1" "U (fst s0) {x}" using X1(1) a2fD[OF A] by blast
    have "lftL U s0 {(x, snd s0)}" using lftL_img[of U s0 "{x}", OF x(2)] by simp
    then show "\<exists>y\<in>X. lftL U s0 {y}" using X1(2) x(1) by blast
  next
    assume "\<exists>y\<in>X. lftL U s0 {y}"
    then obtain y X1 where y: "y \<in> X" and X1: "U (fst s0) X1" "\<forall>a\<in>X1. (a, snd s0) \<in> {y}"
      unfolding lftL_def by blast
    show "lftL U s0 X" unfolding lftL_def using y X1 by (intro exI[where x=X1]) auto
  }
qed

section \<open>Duality\<close>

(* the blocker of the blocker of an up-closed family is the family itself *)
lemma blk_blk:
  assumes up: "upcl R"
  shows "blk (blk R) = R"
proof (intro ext iffI)
  fix s0 Z
  assume B: "blk (blk R) s0 Z"
  show "R s0 Z"
  proof (rule ccontr)
    assume nR: "\<not> R s0 Z"
    have "blk R s0 (- Z)"
      unfolding blk_def
    proof (intro allI impI notI)
      fix X assume RX: "R s0 X" and "X \<inter> - Z = {}"
      then have "X \<subseteq> Z" by blast
      with nR show False using upclD[OF up RX] by blast
    qed
    from blkD[OF B this] show False by blast
  qed
next
  fix s0 Z assume RZ: "R s0 Z"
  show "blk (blk R) s0 Z"
    unfolding blk_def[of "blk R"]
  proof (intro allI impI)
    fix G assume "blk R s0 G"
    from blkD[of R s0 G Z, OF this RZ] show "G \<inter> Z \<noteq> {}" by (simp add: Int_commute)
  qed
qed

lemma est_ad_of_blk: "est (ad_of R) s0 \<psi> \<longleftrightarrow> blk R s0 \<psi>"
  by (simp add: est_ad_of blk_def)

section \<open>Blind product below both sequential orders\<close>

lemma blind_fref_seq_LR: "blindfd (lftL U) (lftR V) \<sqsubseteq>\<^sub>f seqf (lftL U) (lftR V)"
  unfolding fref_def
proof (intro allI impI)
  fix s0 and Z
  assume "seqf (lftL U) (lftR V) s0 Z"
  then obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. lftR V (a, snd s0) Z"
    unfolding seqf_def lftL_def by auto
  show "blindfd (lftL U) (lftR V) s0 Z"
    unfolding blindfd_def blk_def[of "parfd _ _"]
  proof (intro allI impI)
    fix G assume "parfd (blk (lftL U)) (blk (lftR V)) s0 G"
    then obtain A B where A: "blk (lftL U) s0 A" and B: "blk (lftR V) s0 B"
      and AB: "\<forall>p\<in>A. \<forall>q\<in>B. (fst p, snd q) \<in> G" unfolding parfd_def by blast
    from blkD[OF A lftL_img[of U s0 X1, OF X1(1)]]
    obtain a where a: "a \<in> X1" "(a, snd s0) \<in> A" by blast
    then obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. (a, b) \<in> Z"
      using X1(2) unfolding lftR_def by auto
    from blkD[OF B lftR_img[of V s0 X2, OF X2(1)]]
    obtain b where b: "b \<in> X2" "(fst s0, b) \<in> B" by blast
    have "(a, b) \<in> G" using bspec[OF bspec[OF AB a(2)] b(2)] by simp
    moreover have "(a, b) \<in> Z" using bspec[OF X2(2) b(1)] .
    ultimately show "G \<inter> Z \<noteq> {}" by blast
  qed
qed

lemma blind_fref_seq_RL: "blindfd (lftL U) (lftR V) \<sqsubseteq>\<^sub>f seqf (lftR V) (lftL U)"
  unfolding fref_def
proof (intro allI impI)
  fix s0 and Z
  assume "seqf (lftR V) (lftL U) s0 Z"
  then obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. lftL U (fst s0, b) Z"
    unfolding seqf_def lftR_def by auto
  show "blindfd (lftL U) (lftR V) s0 Z"
    unfolding blindfd_def blk_def[of "parfd _ _"]
  proof (intro allI impI)
    fix G assume "parfd (blk (lftL U)) (blk (lftR V)) s0 G"
    then obtain A B where A: "blk (lftL U) s0 A" and B: "blk (lftR V) s0 B"
      and AB: "\<forall>p\<in>A. \<forall>q\<in>B. (fst p, snd q) \<in> G" unfolding parfd_def by blast
    from blkD[OF B lftR_img[of V s0 X2, OF X2(1)]]
    obtain b where b: "b \<in> X2" "(fst s0, b) \<in> B" by blast
    then obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. (a, b) \<in> Z"
      using X2(2) unfolding lftL_def by auto
    from blkD[OF A lftL_img[of U s0 X1, OF X1(1)]]
    obtain a where a: "a \<in> X1" "(a, snd s0) \<in> A" by blast
    have "(a, b) \<in> G" using bspec[OF bspec[OF AB a(2)] b(2)] by simp
    moreover have "(a, b) \<in> Z" using bspec[OF X1(2) a(1)] .
    ultimately show "G \<inter> Z \<noteq> {}" by blast
  qed
qed


section \<open>Parallel against sequential composition\<close>

lemma seq_fref_par_LR: "seqf (lftL U) (lftR V) \<sqsubseteq>\<^sub>f parfd (lftL U) (lftR V)"
  unfolding fref_def
proof (intro allI impI)
  fix s0 and Z
  assume "parfd (lftL U) (lftR V) s0 Z"
  then obtain XL XR where L: "lftL U s0 XL" and R: "lftR V s0 XR"
    and M: "\<forall>p\<in>XL. \<forall>q\<in>XR. (fst p, snd q) \<in> Z" unfolding parfd_def by blast
  obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. (a, snd s0) \<in> XL" using L unfolding lftL_def by blast
  obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. (fst s0, b) \<in> XR" using R unfolding lftR_def by blast
  have H: "lftR V (a, snd s0) Z" if a: "a \<in> X1" for a
    unfolding lftR_def
  proof (rule exI[where x=X2], intro conjI ballI)
    show "V (snd (a, snd s0)) X2" using X2(1) by simp
    fix b assume b: "b \<in> X2"
    show "(fst (a, snd s0), b) \<in> Z"
      using bspec[OF bspec[OF M bspec[OF X1(2) a]] bspec[OF X2(2) b]] by simp
  qed
  show "seqf (lftL U) (lftR V) s0 Z"
    unfolding seqf_def lftL_def
  proof (rule exI[where x=X1], intro conjI ballI)
    show "U (fst s0) X1" by (fact X1(1))
    fix a assume "a \<in> X1" then show "(a, snd s0) \<in> {y. lftR V y Z}" using H by simp
  qed
qed

lemma seq_fref_par_RL: "seqf (lftR V) (lftL U) \<sqsubseteq>\<^sub>f parfd (lftL U) (lftR V)"
  unfolding fref_def
proof (intro allI impI)
  fix s0 and Z
  assume "parfd (lftL U) (lftR V) s0 Z"
  then obtain XL XR where L: "lftL U s0 XL" and R: "lftR V s0 XR"
    and M: "\<forall>p\<in>XL. \<forall>q\<in>XR. (fst p, snd q) \<in> Z" unfolding parfd_def by blast
  obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. (a, snd s0) \<in> XL" using L unfolding lftL_def by blast
  obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. (fst s0, b) \<in> XR" using R unfolding lftR_def by blast
  have H: "lftL U (fst s0, b) Z" if b: "b \<in> X2" for b
    unfolding lftL_def
  proof (rule exI[where x=X1], intro conjI ballI)
    show "U (fst (fst s0, b)) X1" using X1(1) by simp
    fix a assume a: "a \<in> X1"
    show "(a, snd (fst s0, b)) \<in> Z"
      using bspec[OF bspec[OF M bspec[OF X1(2) a]] bspec[OF X2(2) b]] by simp
  qed
  show "seqf (lftR V) (lftL U) s0 Z"
    unfolding seqf_def lftR_def
  proof (rule exI[where x=X2], intro conjI ballI)
    show "V (snd s0) X2" by (fact X2(1))
    fix b assume "b \<in> X2" then show "(fst s0, b) \<in> {y. lftL U y Z}" using H by simp
  qed
qed

lemma fref_antisym: "R1 \<sqsubseteq>\<^sub>f R2 \<Longrightarrow> R2 \<sqsubseteq>\<^sub>f R1 \<Longrightarrow> R1 = R2"
  unfolding fref_def by (intro ext) blast

(* a branch without angelic choice can be scheduled first *)
lemma par_eq_seq_a2_LR:
  assumes A: "a2f U"
  shows "parfd (lftL U) (lftR V) = seqf (lftL U) (lftR V)"
proof (rule fref_antisym[OF _ seq_fref_par_LR], unfold fref_def, intro allI impI)
  fix s0 and Z
  assume "seqf (lftL U) (lftR V) s0 Z"
  then obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. lftR V (a, snd s0) Z"
    unfolding seqf_def lftL_def by auto
  obtain x where x: "x \<in> X1" "U (fst s0) {x}" using X1(1) a2fD[OF A] by blast
  obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. (x, b) \<in> Z"
    using bspec[OF X1(2) x(1)] unfolding lftR_def by auto
  show "parfd (lftL U) (lftR V) s0 Z"
    unfolding parfd_def
  proof (intro exI conjI)
    show "lftL U s0 {(x, snd s0)}" using lftL_img[of U s0 "{x}", OF x(2)] by simp
    show "lftR V s0 (Pair (fst s0) ` X2)" using lftR_img[of V s0 X2, OF X2(1)] by simp
    show "\<forall>p\<in>{(x, snd s0)}. \<forall>q\<in>Pair (fst s0) ` X2. (fst p, snd q) \<in> Z" using X2(2) by auto
  qed
qed

lemma par_eq_seq_a2_RL:
  assumes A: "a2f V"
  shows "parfd (lftL U) (lftR V) = seqf (lftR V) (lftL U)"
proof (rule fref_antisym[OF _ seq_fref_par_RL], unfold fref_def, intro allI impI)
  fix s0 and Z
  assume "seqf (lftR V) (lftL U) s0 Z"
  then obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. lftL U (fst s0, b) Z"
    unfolding seqf_def lftR_def by auto
  obtain y where y: "y \<in> X2" "V (snd s0) {y}" using X2(1) a2fD[OF A] by blast
  obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. (a, y) \<in> Z"
    using bspec[OF X2(2) y(1)] unfolding lftL_def by auto
  show "parfd (lftL U) (lftR V) s0 Z"
    unfolding parfd_def
  proof (intro exI conjI)
    show "lftL U s0 ((\<lambda>a. (a, snd s0)) ` X1)" by (rule lftL_img[of U s0 X1, OF X1(1)])
    show "lftR V s0 {(fst s0, y)}" using lftR_img[of V s0 "{y}", OF y(2)] by simp
    show "\<forall>p\<in>(\<lambda>a. (a, snd s0)) ` X1. \<forall>q\<in>{(fst s0, y)}. (fst p, snd q) \<in> Z" using X1(2) by auto
  qed
qed

(* a branch without demonic choice can be scheduled last *)
lemma par_eq_seq_ang_RL:
  assumes A: "angf U"
  shows "parfd (lftL U) (lftR V) = seqf (lftR V) (lftL U)"
proof (rule fref_antisym[OF _ seq_fref_par_RL], unfold fref_def, intro allI impI)
  fix s0 and Z
  assume "seqf (lftR V) (lftL U) s0 Z"
  then obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. lftL U (fst s0, b) Z"
    unfolding seqf_def lftR_def by auto
  obtain A0 where A0: "\<And>X. U (fst s0) X = (A0 \<subseteq> X)" using angfE[OF A] by blast
  have AZ: "(a, b) \<in> Z" if ab: "a \<in> A0" "b \<in> X2" for a b
  proof -
    obtain X1 where "U (fst s0) X1" "\<forall>a\<in>X1. (a, b) \<in> Z"
      using bspec[OF X2(2) ab(2)] unfolding lftL_def by auto
    then show ?thesis using A0 ab(1) by blast
  qed
  show "parfd (lftL U) (lftR V) s0 Z"
    unfolding parfd_def
  proof (intro exI conjI)
    show "lftL U s0 ((\<lambda>a. (a, snd s0)) ` A0)" by (rule lftL_img) (simp add: A0)
    show "lftR V s0 (Pair (fst s0) ` X2)" by (rule lftR_img[of V s0 X2, OF X2(1)])
    show "\<forall>p\<in>(\<lambda>a. (a, snd s0)) ` A0. \<forall>q\<in>Pair (fst s0) ` X2. (fst p, snd q) \<in> Z" using AZ by auto
  qed
qed

lemma par_eq_seq_ang_LR:
  assumes A: "angf V"
  shows "parfd (lftL U) (lftR V) = seqf (lftL U) (lftR V)"
proof (rule fref_antisym[OF _ seq_fref_par_LR], unfold fref_def, intro allI impI)
  fix s0 and Z
  assume "seqf (lftL U) (lftR V) s0 Z"
  then obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. lftR V (a, snd s0) Z"
    unfolding seqf_def lftL_def by auto
  obtain B0 where B0: "\<And>X. V (snd s0) X = (B0 \<subseteq> X)" using angfE[OF A] by blast
  have AZ: "(a, b) \<in> Z" if ab: "a \<in> X1" "b \<in> B0" for a b
  proof -
    obtain X2 where "V (snd s0) X2" "\<forall>b\<in>X2. (a, b) \<in> Z"
      using bspec[OF X1(2) ab(1)] unfolding lftR_def by auto
    then show ?thesis using B0 ab(2) by blast
  qed
  show "parfd (lftL U) (lftR V) s0 Z"
    unfolding parfd_def
  proof (intro exI conjI)
    show "lftL U s0 ((\<lambda>a. (a, snd s0)) ` X1)" by (rule lftL_img[of U s0 X1, OF X1(1)])
    show "lftR V s0 (Pair (fst s0) ` B0)" by (rule lftR_img) (simp add: B0)
    show "\<forall>p\<in>(\<lambda>a. (a, snd s0)) ` X1. \<forall>q\<in>Pair (fst s0) ` B0. (fst p, snd q) \<in> Z" using AZ by auto
  qed
qed

(* with no angelic choice on either side, the blind and clairvoyant products agree *)
lemma blind_eq_par_a2:
  assumes AU: "a2f U" and AV: "a2f V"
  shows "blindfd (lftL U) (lftR V) = parfd (lftL U) (lftR V)"
proof (rule fref_antisym)
  show "blindfd (lftL U) (lftR V) \<sqsubseteq>\<^sub>f parfd (lftL U) (lftR V)"
    using blind_fref_seq_LR par_eq_seq_a2_LR[OF AU] by metis
  show "parfd (lftL U) (lftR V) \<sqsubseteq>\<^sub>f blindfd (lftL U) (lftR V)"
    unfolding fref_def
  proof (intro allI impI)
    fix s0 and Z
    assume blind: "blindfd (lftL U) (lftR V) s0 Z"
    show "parfd (lftL U) (lftR V) s0 Z"
    proof (rule ccontr)
      assume np: "\<not> parfd (lftL U) (lftR V) s0 Z"
      let ?D1 = "{a. U (fst s0) {a}}" and ?D2 = "{b. V (snd s0) {b}}"
      have bA: "blk (lftL U) s0 ((\<lambda>a. (a, snd s0)) ` ?D1)"
        unfolding blk_def
      proof (intro allI impI)
        fix X assume "lftL U s0 X"
        then obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. (a, snd s0) \<in> X" unfolding lftL_def by blast
        obtain x where "x \<in> X1" "U (fst s0) {x}" using X1(1) a2fD[OF AU] by blast
        then show "X \<inter> (\<lambda>a. (a, snd s0)) ` ?D1 \<noteq> {}" using X1(2) by blast
      qed
      have bB: "blk (lftR V) s0 (Pair (fst s0) ` ?D2)"
        unfolding blk_def
      proof (intro allI impI)
        fix X assume "lftR V s0 X"
        then obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. (fst s0, b) \<in> X" unfolding lftR_def by blast
        obtain y where "y \<in> X2" "V (snd s0) {y}" using X2(1) a2fD[OF AV] by blast
        then show "X \<inter> Pair (fst s0) ` ?D2 \<noteq> {}" using X2(2) by blast
      qed
      have pairs: "(a, b) \<notin> Z" if "a \<in> ?D1" "b \<in> ?D2" for a b
      proof
        assume ab: "(a, b) \<in> Z"
        have "parfd (lftL U) (lftR V) s0 Z"
          unfolding parfd_def
        proof (intro exI conjI)
          show "lftL U s0 {(a, snd s0)}" using lftL_img[of U s0 "{a}"] that(1) by simp
          show "lftR V s0 {(fst s0, b)}" using lftR_img[of V s0 "{b}"] that(2) by simp
          show "\<forall>p\<in>{(a, snd s0)}. \<forall>q\<in>{(fst s0, b)}. (fst p, snd q) \<in> Z" using ab by simp
        qed
        with np show False by blast
      qed
      have "parfd (blk (lftL U)) (blk (lftR V)) s0 (- Z)"
        unfolding parfd_def
      proof (intro exI conjI)
        show "blk (lftL U) s0 ((\<lambda>a. (a, snd s0)) ` ?D1)" by (fact bA)
        show "blk (lftR V) s0 (Pair (fst s0) ` ?D2)" by (fact bB)
        show "\<forall>p\<in>(\<lambda>a. (a, snd s0)) ` ?D1. \<forall>q\<in>Pair (fst s0) ` ?D2. (fst p, snd q) \<in> - Z"
          using pairs by auto
      qed
      from blkD[OF blind[unfolded blindfd_def] this] show False by blast
    qed
  qed
qed

section \<open>Angelic choice with a purely angelic partner\<close>

definition parj :: "('s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow>
    ('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "parj j RP RQ = (\<lambda>s0 Z. \<exists>XL XR. RP s0 XL \<and> RQ s0 XR \<and> (\<forall>a\<in>XL. \<forall>b\<in>XR. \<exists>z\<in>Z. j s0 a b z))"

lemma ad_par_parj:
  assumes "\<And>s0 X. RP s0 X \<Longrightarrow> X \<noteq> {}" "\<And>s0 X. RQ s0 X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of RQ = ad_of (parj (\<lambda>s0 a b z. merge_eval j s0 a b z) RP RQ)"
  unfolding parj_def by (rule ad_par_ad_of[where RP=RP and RQ=RQ and j=j], fact assms(1), fact assms(2))

lemma parj_angelic_dist:
  assumes u1: "upcl P1" and u2: "upcl P2" and q: "angf Q"
  shows "parj j (\<lambda>s0 X. P1 s0 X \<and> P2 s0 X) Q = (\<lambda>s0 Z. parj j P1 Q s0 Z \<and> parj j P2 Q s0 Z)"
proof (intro ext iffI)
  fix s0 Z
  assume "parj j (\<lambda>s0 X. P1 s0 X \<and> P2 s0 X) Q s0 Z"
  then show "parj j P1 Q s0 Z \<and> parj j P2 Q s0 Z" unfolding parj_def by blast
next
  fix s0 Z
  assume "parj j P1 Q s0 Z \<and> parj j P2 Q s0 Z"
  then obtain X1 Y1 X2 Y2 where 1: "P1 s0 X1" "Q s0 Y1" "\<forall>a\<in>X1. \<forall>b\<in>Y1. \<exists>z\<in>Z. j s0 a b z"
    and 2: "P2 s0 X2" "Q s0 Y2" "\<forall>a\<in>X2. \<forall>b\<in>Y2. \<exists>z\<in>Z. j s0 a b z"
    unfolding parj_def by blast
  obtain B where B: "\<And>X. Q s0 X = (B \<subseteq> X)" using angfE[OF q] by blast
  have BY: "B \<subseteq> Y1" "B \<subseteq> Y2" using 1(2) 2(2) B by blast+
  show "parj j (\<lambda>s0 X. P1 s0 X \<and> P2 s0 X) Q s0 Z"
    unfolding parj_def
  proof (intro exI conjI)
    show "P1 s0 (X1 \<union> X2)" by (rule upclD[OF u1 1(1)]) blast
    show "P2 s0 (X1 \<union> X2)" by (rule upclD[OF u2 2(1)]) blast
    show "Q s0 B" using B by blast
    show "\<forall>a\<in>X1 \<union> X2. \<forall>b\<in>B. \<exists>z\<in>Z. j s0 a b z" using 1(3) 2(3) BY by blast
  qed
qed

lemma ades_par_angelic_dist_eq:
  assumes n1: "\<And>s0 X. P1 s0 X \<Longrightarrow> X \<noteq> {}" and n2: "\<And>s0 X. P2 s0 X \<Longrightarrow> X \<noteq> {}"
    and nq: "\<And>s0 X. Q s0 X \<Longrightarrow> X \<noteq> {}"
    and u1: "upcl P1" and u2: "upcl P2" and q: "angf Q"
  shows "(ad_of P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of Q) \<squnion>\<^sub>D\<^sub>A (ad_of P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of Q) =
         (ad_of P1 \<squnion>\<^sub>D\<^sub>A ad_of P2) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of Q"
proof -
  have n12: "\<And>s0 X. P1 s0 X \<and> P2 s0 X \<Longrightarrow> X \<noteq> {}" using n1 by blast
  have e1: "ad_of P1 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of Q = ad_of (parj (\<lambda>s0 a b z. merge_eval j s0 a b z) P1 Q)"
    by (rule ad_par_parj) (fact n1, fact nq)
  have e2: "ad_of P2 \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of Q = ad_of (parj (\<lambda>s0 a b z. merge_eval j s0 a b z) P2 Q)"
    by (rule ad_par_parj) (fact n2, fact nq)
  have e3: "ad_of (\<lambda>s0 X. P1 s0 X \<and> P2 s0 X) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of Q =
      ad_of (parj (\<lambda>s0 a b z. merge_eval j s0 a b z) (\<lambda>s0 X. P1 s0 X \<and> P2 s0 X) Q)"
    by (rule ad_par_parj) (fact n12, fact nq)
  show ?thesis
    unfolding e1 e2 ad_of_angelic e3 parj_angelic_dist[OF u1 u2 q] ..
qed

section \<open>Exchange law for frame-disjoint branches\<close>

lemma seqf_ne:
  "(\<And>s0 X. RP s0 X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow> (\<And>s0 X. RQ s0 X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow>
   (\<And>s0 X. seqf RP RQ s0 X \<Longrightarrow> X \<noteq> {})"
  unfolding seqf_def by fastforce

lemma parfd_ne:
  "(\<And>s0 X. RP s0 X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow> (\<And>s0 X. RQ s0 X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow>
   (\<And>s0 X. parfd RP RQ s0 X \<Longrightarrow> X \<noteq> {})"
  unfolding parfd_def by fastforce

lemma exchange_fref:
  "seqf (parfd (lftL U) (lftR V)) (parfd (lftL U') (lftR V')) \<sqsubseteq>\<^sub>f
   parfd (seqf (lftL U) (lftL U')) (seqf (lftR V) (lftR V'))"
  unfolding fref_def
proof (intro allI impI)
  fix s0 and Z
  assume "parfd (seqf (lftL U) (lftL U')) (seqf (lftR V) (lftR V')) s0 Z"
  then obtain XL XR where SL: "seqf (lftL U) (lftL U') s0 XL" and SR: "seqf (lftR V) (lftR V') s0 XR"
    and M: "\<forall>p\<in>XL. \<forall>q\<in>XR. (fst p, snd q) \<in> Z" unfolding parfd_def by blast
  obtain X1 where X1: "U (fst s0) X1" "\<forall>a\<in>X1. lftL U' (a, snd s0) XL"
    using SL unfolding seqf_def lftL_def[of U] by auto
  obtain X2 where X2: "V (snd s0) X2" "\<forall>b\<in>X2. lftR V' (fst s0, b) XR"
    using SR unfolding seqf_def lftR_def[of V] by auto
  have mid: "parfd (lftL U') (lftR V') (a, b) Z" if a: "a \<in> X1" and b: "b \<in> X2" for a b
  proof -
    obtain X1' where X1': "U' a X1'" "\<forall>a'\<in>X1'. (a', snd s0) \<in> XL"
      using bspec[OF X1(2) a] unfolding lftL_def by auto
    obtain X2' where X2': "V' b X2'" "\<forall>b'\<in>X2'. (fst s0, b') \<in> XR"
      using bspec[OF X2(2) b] unfolding lftR_def by auto
    show ?thesis
      unfolding parfd_def
    proof (intro exI conjI)
      show "lftL U' (a, b) ((\<lambda>a'. (a', b)) ` X1')"
        using lftL_img[of U' "(a, b)" X1'] X1'(1) by simp
      show "lftR V' (a, b) (Pair a ` X2')"
        using lftR_img[of V' "(a, b)" X2'] X2'(1) by simp
      show "\<forall>p\<in>(\<lambda>a'. (a', b)) ` X1'. \<forall>q\<in>Pair a ` X2'. (fst p, snd q) \<in> Z"
      proof (intro ballI)
        fix p q assume p: "p \<in> (\<lambda>a'. (a', b)) ` X1'" and q: "q \<in> Pair a ` X2'"
        then obtain a' b' where pq: "p = (a', b)" "a' \<in> X1'" "q = (a, b')" "b' \<in> X2'" by blast
        show "(fst p, snd q) \<in> Z"
          using bspec[OF bspec[OF M bspec[OF X1'(2) pq(2)]] bspec[OF X2'(2) pq(4)]] pq by simp
      qed
    qed
  qed
  show "seqf (parfd (lftL U) (lftR V)) (parfd (lftL U') (lftR V')) s0 Z"
    unfolding seqf_def parfd_def[of "lftL U"]
  proof (intro exI conjI)
    show "lftL U s0 ((\<lambda>a. (a, snd s0)) ` X1)" by (rule lftL_img[of U s0 X1, OF X1(1)])
    show "lftR V s0 (Pair (fst s0) ` X2)" by (rule lftR_img[of V s0 X2, OF X2(1)])
    show "\<forall>p\<in>(\<lambda>a. (a, snd s0)) ` X1. \<forall>q\<in>Pair (fst s0) ` X2.
            (fst p, snd q) \<in> {y. parfd (lftL U') (lftR V') y Z}"
      using mid by auto
  qed
qed

lemma ades_exchange:
  assumes nU: "\<And>t X. U t X \<Longrightarrow> X \<noteq> {}" and nU': "\<And>t X. U' t X \<Longrightarrow> X \<noteq> {}"
    and nV: "\<And>t X. V t X \<Longrightarrow> X \<noteq> {}" and nV': "\<And>t X. V' t X \<Longrightarrow> X \<noteq> {}"
  shows "(ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V)) ;;\<^sub>D\<^sub>A (ad_of (lftL U') \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V'))
         \<sqsubseteq> (ad_of (lftL U) ;;\<^sub>D\<^sub>A ad_of (lftL U')) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> (ad_of (lftR V) ;;\<^sub>D\<^sub>A ad_of (lftR V'))"
proof -
  have nL: "\<And>s0 X. lftL U s0 X \<Longrightarrow> X \<noteq> {}" using nU unfolding lftL_def by fastforce
  have nL': "\<And>s0 X. lftL U' s0 X \<Longrightarrow> X \<noteq> {}" using nU' unfolding lftL_def by fastforce
  have nR: "\<And>s0 X. lftR V s0 X \<Longrightarrow> X \<noteq> {}" using nV unfolding lftR_def by fastforce
  have nR': "\<And>s0 X. lftR V' s0 X \<Longrightarrow> X \<noteq> {}" using nV' unfolding lftR_def by fastforce
  have p1: "ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V) = ad_of (parfd (lftL U) (lftR V))"
    by (rule ad_par_parfd) (fact nL, fact nR)
  have p2: "ad_of (lftL U') \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V') = ad_of (parfd (lftL U') (lftR V'))"
    by (rule ad_par_parfd) (fact nL', fact nR')
  have s1: "ad_of (parfd (lftL U) (lftR V)) ;;\<^sub>D\<^sub>A ad_of (parfd (lftL U') (lftR V')) =
      ad_of (seqf (parfd (lftL U) (lftR V)) (parfd (lftL U') (lftR V')))"
    by (rule ad_seq_seqf) (rule parfd_ne[OF nL nR])
  have s2: "ad_of (lftL U) ;;\<^sub>D\<^sub>A ad_of (lftL U') = ad_of (seqf (lftL U) (lftL U'))"
    by (rule ad_seq_seqf) (fact nL)
  have s3: "ad_of (lftR V) ;;\<^sub>D\<^sub>A ad_of (lftR V') = ad_of (seqf (lftR V) (lftR V'))"
    by (rule ad_seq_seqf) (fact nR)
  have p3: "ad_of (seqf (lftL U) (lftL U')) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (seqf (lftR V) (lftR V')) =
      ad_of (parfd (seqf (lftL U) (lftL U')) (seqf (lftR V) (lftR V')))"
  proof (rule ad_par_parfd)
    fix s0 X assume "seqf (lftL U) (lftL U') s0 X"
    then have "{y. lftL U' y X} \<noteq> {}" unfolding seqf_def by (rule nL)
    then obtain y where "lftL U' y X" by blast
    then show "X \<noteq> {}" by (rule nL')
  next
    fix s0 X assume "seqf (lftR V) (lftR V') s0 X"
    then have "{y. lftR V' y X} \<noteq> {}" unfolding seqf_def by (rule nR)
    then obtain y where "lftR V' y X" by blast
    then show "X \<noteq> {}" by (rule nR')
  qed
  show ?thesis
    unfolding p1 p2 s1 s2 s3 p3 by (rule fref_ad_of[OF exchange_fref])
qed

section \<open>AD-level forms of the scheduling laws\<close>

lemma ades_par_eq_seq_a2:
  assumes A: "a2f U" and nV: "\<And>t X. V t X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V) = ad_of (lftL U) ;;\<^sub>D\<^sub>A ad_of (lftR V)"
proof -
  have nL: "\<And>s0 X. lftL U s0 X \<Longrightarrow> X \<noteq> {}" using a2f_ne[OF A] unfolding lftL_def by fastforce
  have nR: "\<And>s0 X. lftR V s0 X \<Longrightarrow> X \<noteq> {}" using nV unfolding lftR_def by fastforce
  have p: "ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V) = ad_of (parfd (lftL U) (lftR V))"
    by (rule ad_par_parfd) (fact nL, fact nR)
  have s: "ad_of (lftL U) ;;\<^sub>D\<^sub>A ad_of (lftR V) = ad_of (seqf (lftL U) (lftR V))"
    by (rule ad_seq_seqf) (fact nL)
  show ?thesis unfolding p s par_eq_seq_a2_LR[OF A] ..
qed

lemma ades_par_eq_seq_ang:
  assumes A: "angf U" and nU: "\<And>t X. U t X \<Longrightarrow> X \<noteq> {}" and nV: "\<And>t X. V t X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V) = ad_of (lftR V) ;;\<^sub>D\<^sub>A ad_of (lftL U)"
proof -
  have nL: "\<And>s0 X. lftL U s0 X \<Longrightarrow> X \<noteq> {}" using nU unfolding lftL_def by fastforce
  have nR: "\<And>s0 X. lftR V s0 X \<Longrightarrow> X \<noteq> {}" using nV unfolding lftR_def by fastforce
  have p: "ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V) = ad_of (parfd (lftL U) (lftR V))"
    by (rule ad_par_parfd) (fact nL, fact nR)
  have s: "ad_of (lftR V) ;;\<^sub>D\<^sub>A ad_of (lftL U) = ad_of (seqf (lftR V) (lftL U))"
    by (rule ad_seq_seqf) (fact nR)
  show ?thesis unfolding p s par_eq_seq_ang_RL[OF A] ..
qed

section \<open>Bottleneck duality on a finite state space\<close>

(* threshold form: wp reaches t iff the level set {\<beta> \<ge> t} meets every offered set *)
lemma minmax_threshold:
  fixes \<beta> :: "'a::finite \<Rightarrow> 'b::linorder" and U :: "'a set set"
  assumes ne: "U \<noteq> {}" and nemp: "{} \<notin> U"
  shows "t \<le> Min ((\<lambda>X. Max (\<beta> ` X)) ` U) \<longleftrightarrow> (\<forall>X\<in>U. X \<inter> {x. t \<le> \<beta> x} \<noteq> {})"
proof -
  have "t \<le> Min ((\<lambda>X. Max (\<beta> ` X)) ` U) \<longleftrightarrow> (\<forall>m\<in>(\<lambda>X. Max (\<beta> ` X)) ` U. t \<le> m)"
    by (rule Min_ge_iff) (simp_all add: ne)
  also have "\<dots> \<longleftrightarrow> (\<forall>X\<in>U. t \<le> Max (\<beta> ` X))" by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>X\<in>U. X \<inter> {x. t \<le> \<beta> x} \<noteq> {})"
  proof (rule ball_cong[OF refl])
    fix X assume "X \<in> U"
    then have Xne: "X \<noteq> {}" using nemp by blast
    have "t \<le> Max (\<beta> ` X) \<longleftrightarrow> (\<exists>m\<in>\<beta> ` X. t \<le> m)"
      by (rule Max_ge_iff) (simp_all add: Xne)
    also have "\<dots> \<longleftrightarrow> X \<inter> {x. t \<le> \<beta> x} \<noteq> {}" by blast
    finally show "t \<le> Max (\<beta> ` X) \<longleftrightarrow> X \<inter> {x. t \<le> \<beta> x} \<noteq> {}" .
  qed
  finally show ?thesis .
qed

(* Edmonds-Fulkerson: min over offered sets of max = max over blocking sets of min *)
lemma bottleneck_minmax:
  fixes \<beta> :: "'a::finite \<Rightarrow> 'b::linorder" and U :: "'a set set"
  assumes ne: "U \<noteq> {}" and nemp: "{} \<notin> U"
  shows "Min ((\<lambda>X. Max (\<beta> ` X)) ` U) =
         Max ((\<lambda>G. Min (\<beta> ` G)) ` {G. G \<noteq> {} \<and> (\<forall>X\<in>U. X \<inter> G \<noteq> {})})"
proof -
  let ?v = "Min ((\<lambda>X. Max (\<beta> ` X)) ` U)"
  let ?B = "{G. G \<noteq> {} \<and> (\<forall>X\<in>U. X \<inter> G \<noteq> {})}"
  have "?v \<in> (\<lambda>X. Max (\<beta> ` X)) ` U" by (rule Min_in) (simp_all add: ne)
  then obtain X0 where X0: "X0 \<in> U" "?v = Max (\<beta> ` X0)" by (rule imageE)
  let ?G = "{x. ?v \<le> \<beta> x}"
  have meet: "\<forall>X\<in>U. X \<inter> ?G \<noteq> {}"
    by (rule minmax_threshold[where \<beta>=\<beta> and U=U and t="Min ((\<lambda>X. Max (\<beta> ` X)) ` U)",
          OF ne nemp, THEN iffD1]) (rule order_refl)
  have Gne: "?G \<noteq> {}" using bspec[OF meet X0(1)] by blast
  have GB: "?G \<in> ?B" unfolding mem_Collect_eq by (intro conjI Gne meet)
  have ge: "?v \<le> Max ((\<lambda>G. Min (\<beta> ` G)) ` ?B)"
  proof -
    have "?v \<le> Min (\<beta> ` ?G)"
    proof (rule Min.boundedI)
      show "finite (\<beta> ` ?G)" by simp
      show "\<beta> ` ?G \<noteq> {}" using Gne by blast
      fix a assume "a \<in> \<beta> ` ?G"
      then obtain x where "x \<in> ?G" "a = \<beta> x" by (rule imageE)
      then show "?v \<le> a" by simp
    qed
    also have "\<dots> \<le> Max ((\<lambda>G. Min (\<beta> ` G)) ` ?B)" by (rule Max_ge) (simp, rule imageI[OF GB])
    finally show ?thesis .
  qed
  have le: "Max ((\<lambda>G. Min (\<beta> ` G)) ` ?B) \<le> ?v"
  proof (rule Max.boundedI)
    show "finite ((\<lambda>G. Min (\<beta> ` G)) ` ?B)" by simp
    have "Min (\<beta> ` ?G) \<in> (\<lambda>G. Min (\<beta> ` G)) ` ?B" by (rule imageI[OF GB])
    then show "(\<lambda>G. Min (\<beta> ` G)) ` ?B \<noteq> {}" by (metis empty_iff)
    fix m assume "m \<in> (\<lambda>G. Min (\<beta> ` G)) ` ?B"
    then obtain G where G: "G \<in> ?B" "m = Min (\<beta> ` G)" by (rule imageE)
    from G(1) have "\<forall>X\<in>U. X \<inter> G \<noteq> {}" unfolding mem_Collect_eq by (rule conjunct2)
    from bspec[OF this X0(1)] obtain x where x: "x \<in> G" "x \<in> X0" by blast
    have "m \<le> \<beta> x" unfolding G(2) by (rule Min_le) (simp_all add: x(1))
    also have "\<dots> \<le> Max (\<beta> ` X0)" by (rule Max_ge) (simp_all add: x(2))
    finally show "m \<le> ?v" by (simp only: X0(2))
  qed
  show ?thesis using ge le by (rule antisym)
qed

section \<open>Partial merges: an angelic alternative the partner cannot match is infeasible\<close>

(* merge only equal branch states *)
definition jeq :: "'s merge" where
  "jeq = (\<lambda>(m, z). mrg_left\<^sub>v m = mrg_right\<^sub>v m \<and> z = mrg_left\<^sub>v m)"

lemma jeq_eval [simp]: "merge_eval jeq s0 p q z \<longleftrightarrow> p = q \<and> z = p"
  by (simp add: jeq_def)

(* x := v1 in parallel with an angelic choice of v1 and v2: no started observation *)
lemma ades_par_eq_angelic_miracle:
  assumes "v1 \<noteq> v2"
  shows "\<not> (ad_of (\<lambda>s X. v1 \<in> X) \<parallel>\<^sub>A\<^sub>D\<^bsub>jeq\<^esub> (ad_of (\<lambda>s X. v1 \<in> X) \<squnion>\<^sub>D\<^sub>A ad_of (\<lambda>s X. v2 \<in> X)))
           (ades_obs True s0 c Z)"
proof -
  have e: "ad_of (\<lambda>s X. v1 \<in> X) \<parallel>\<^sub>A\<^sub>D\<^bsub>jeq\<^esub> ad_of (\<lambda>s X. v1 \<in> X \<and> v2 \<in> X) =
      ad_of (\<lambda>s Z. \<exists>XL XR. v1 \<in> XL \<and> (v1 \<in> XR \<and> v2 \<in> XR) \<and>
        (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jeq s sL sR s'))"
    by (rule ad_par_ad_of[where RP="\<lambda>s X. v1 \<in> X" and RQ="\<lambda>s X. v1 \<in> X \<and> v2 \<in> X" and j=jeq]) auto
  have "\<not> (\<exists>XL XR. v1 \<in> XL \<and> (v1 \<in> XR \<and> v2 \<in> XR) \<and>
        (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jeq s0 sL sR s'))"
  proof
    assume "\<exists>XL XR. v1 \<in> XL \<and> (v1 \<in> XR \<and> v2 \<in> XR) \<and>
        (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jeq s0 sL sR s')"
    then obtain XL XR where "v1 \<in> XL" "v2 \<in> XR"
      and M: "\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jeq s0 sL sR s'" by blast
    from bspec[OF bspec[OF M this(1)] this(2)] have "v1 = v2" by simp
    with assms show False by blast
  qed
  then show ?thesis unfolding ad_of_angelic e by simp
qed

(* while x := v1 in parallel with itself terminates in v1 *)
lemma ades_par_eq_same:
  "(ad_of (\<lambda>s X. v1 \<in> X) \<parallel>\<^sub>A\<^sub>D\<^bsub>jeq\<^esub> ad_of (\<lambda>s X. v1 \<in> X)) (ades_obs True s0 True {v1})"
proof -
  have e: "ad_of (\<lambda>s X. v1 \<in> X) \<parallel>\<^sub>A\<^sub>D\<^bsub>jeq\<^esub> ad_of (\<lambda>s X. v1 \<in> X) =
      ad_of (\<lambda>s Z. \<exists>XL XR. v1 \<in> XL \<and> v1 \<in> XR \<and>
        (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jeq s sL sR s'))"
    by (rule ad_par_ad_of[where RP="\<lambda>s X. v1 \<in> X" and RQ="\<lambda>s X. v1 \<in> X" and j=jeq]) auto
  show ?thesis unfolding e ad_of_obs
    by (simp only: simp_thms) (rule exI[where x="{v1}"], rule exI[where x="{v1}"], simp)
qed

end
