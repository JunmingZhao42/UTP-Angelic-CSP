theory AD_Geometry_Probe
  imports "UTP-Angelic-Designs.utp_ades"
begin

section \<open>Angelic designs given by offered families\<close>

(* ad_of R: true precondition; from s the demon may offer any X with R s X *)
definition ad_of :: "('s \<Rightarrow> 's set \<Rightarrow> bool) \<Rightarrow> 's angelic_design" where
  "ad_of R = arel_to_ades (\<lambda>(s0, ac'). R (astate.s\<^sub>v s0) (achoices.ac\<^sub>v ac'))"

lemma ad_of_obs [simp]:
  "ad_of R (ades_obs b s0 c X) \<longleftrightarrow> (b \<longrightarrow> c \<and> R s0 X)"
  by (simp add: ad_of_def arel_to_ades_def; pred_auto)

(* P establishes \<psi> from s0: no divergence, and every offered set meets \<psi> *)
definition est :: "'s angelic_design \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "est P s0 \<psi> \<longleftrightarrow> (\<forall>c X. P (ades_obs True s0 c X) \<longrightarrow> c \<and> X \<inter> \<psi> \<noteq> {})"

lemma est_ad_of: "est (ad_of R) s0 \<psi> \<longleftrightarrow> (\<forall>X. R s0 X \<longrightarrow> X \<inter> \<psi> \<noteq> {})"
  by (auto simp: est_def)

subsection \<open>Operators on offered families\<close>

lemma ad_of_demonic: "ad_of R1 \<sqinter>\<^sub>A\<^sub>D ad_of R2 = ad_of (\<lambda>s X. R1 s X \<or> R2 s X)"
  by (rule ades_obs_ext) (simp add: sup_fun_def sup_bool_def; blast)

lemma ad_of_angelic: "ad_of R1 \<squnion>\<^sub>A\<^sub>D ad_of R2 = ad_of (\<lambda>s X. R1 s X \<and> R2 s X)"
  by (rule ades_obs_ext) (simp add: inf_fun_def inf_bool_def; blast)

lemma Skip_AD_obs: "Skip_AD (ades_obs b s0 c X) \<longleftrightarrow> (b \<longrightarrow> c \<and> s0 \<in> X)"
  by (simp add: Skip_AD_def arel_to_ades_def; pred_auto)

lemma Skip_AD_ad_of: "Skip_AD = ad_of (\<lambda>s X. s \<in> X)"
  by (rule ades_obs_ext) (simp add: Skip_AD_obs)

(* sequential composition substitutes the intermediate states that let Q offer Z *)
lemma ad_seq_ad_of:
  assumes "\<And>s X. RP s X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of RP ;;\<^sub>A\<^sub>D ad_of RQ = ad_of (\<lambda>s Z. RP s {s1. RQ s1 Z})"
proof (rule ades_obs_ext)
  fix b s0 c X
  show "(ad_of RP ;;\<^sub>A\<^sub>D ad_of RQ) (ades_obs b s0 c X) =
        ad_of (\<lambda>s Z. RP s {s1. RQ s1 Z}) (ades_obs b s0 c X)"
    using assms[of s0 "{}"] by (cases c; cases b; auto simp: angelic_design_seq_def ex_bool_eq)
qed

(* parallel: the demon offers XL, XR; Z must hold a merge of every pair *)
lemma ad_par_ad_of:
  assumes "\<And>s X. RP s X \<Longrightarrow> X \<noteq> {}" "\<And>s X. RQ s X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of RQ =
    ad_of (\<lambda>s Z. \<exists>XL XR. RP s XL \<and> RQ s XR \<and>
      (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval j s sL sR s'))"
proof (rule ades_obs_ext)
  fix b s0 c X
  show "(ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of RQ) (ades_obs b s0 c X) =
        ad_of (\<lambda>s Z. \<exists>XL XR. RP s XL \<and> RQ s XR \<and>
          (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval j s sL sR s')) (ades_obs b s0 c X)"
    using assms
    by (cases b; simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified] ex_bool_eq;
        blast)
qed


lemma ad_of_refine:
  assumes "\<And>s X. R2 s X \<Longrightarrow> R1 s X"
  shows "ad_of R1 \<sqsubseteq> ad_of R2"
  using assms by (simp add: pred_refine_iff ad_of_def arel_to_ades_def; pred_auto)

lemma est_seq:
  assumes "\<And>s X. RP s X \<Longrightarrow> X \<noteq> {}"
  shows "est (ad_of RP ;;\<^sub>A\<^sub>D ad_of RQ) s0 \<psi> \<longleftrightarrow>
    (\<forall>Z. RP s0 {s1. RQ s1 Z} \<longrightarrow> Z \<inter> \<psi> \<noteq> {})"
  by (simp add: ad_seq_ad_of[OF assms] est_ad_of)

(* for a functional merge f, P \<parallel> Q establishes \<psi> iff for all offered XL, XR
   the angel can pick a pair whose merge lies in \<psi> *)
lemma est_par_fun:
  assumes "\<And>s X. RP s X \<Longrightarrow> X \<noteq> {}" "\<And>s X. RQ s X \<Longrightarrow> X \<noteq> {}"
    and j: "\<And>sL sR s'. merge_eval j s0 sL sR s' \<longleftrightarrow> s' = f sL sR"
  shows "est (ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ad_of RQ) s0 \<psi> \<longleftrightarrow>
    (\<forall>XL XR. RP s0 XL \<longrightarrow> RQ s0 XR \<longrightarrow> (\<exists>a\<in>XL. \<exists>b\<in>XR. f a b \<in> \<psi>))"
proof -
  have "(\<forall>Z. (\<exists>XL XR. RP s0 XL \<and> RQ s0 XR \<and> (\<forall>a\<in>XL. \<forall>b\<in>XR. f a b \<in> Z))
            \<longrightarrow> Z \<inter> \<psi> \<noteq> {}) \<longleftrightarrow>
        (\<forall>XL XR. RP s0 XL \<longrightarrow> RQ s0 XR \<longrightarrow> (\<exists>a\<in>XL. \<exists>b\<in>XR. f a b \<in> \<psi>))"
    (is "?L \<longleftrightarrow> ?R")
  proof
    assume L: ?L
    show ?R
    proof (intro allI impI)
      fix XL XR assume XL: "RP s0 XL" and XR: "RQ s0 XR"
      have "{f a b | a b. a \<in> XL \<and> b \<in> XR} \<inter> \<psi> \<noteq> {}"
        using L[rule_format, of "{f a b | a b. a \<in> XL \<and> b \<in> XR}"] XL XR by blast
      then show "\<exists>a\<in>XL. \<exists>b\<in>XR. f a b \<in> \<psi>" by blast
    qed
  next
    assume ?R
    then show ?L by blast
  qed
  then show ?thesis
    by (simp add: ad_par_ad_of[OF assms(1,2)] est_ad_of j)
qed

section \<open>Concrete probes on two Boolean variables\<close>

type_synonym st = "bool \<times> bool"

(* frame-disjoint merge: the left branch owns fst, the right branch owns snd *)
definition jfd :: "('a \<times> 'b) merge" where
  "jfd = (\<lambda>(m, z). z = (fst (mrg_left\<^sub>v m), snd (mrg_right\<^sub>v m)))"

lemma jfd_eval [simp]: "merge_eval jfd s0 p q z \<longleftrightarrow> z = (fst p, snd q)"
  by (simp add: jfd_def)

abbreviation dem1 :: "st angelic_design" where "dem1 \<equiv> ad_of (\<lambda>s X. \<exists>a. (a, snd s) \<in> X)"
abbreviation dem2 :: "st angelic_design" where "dem2 \<equiv> ad_of (\<lambda>s X. \<exists>b. (fst s, b) \<in> X)"
abbreviation ang1 :: "st angelic_design" where "ang1 \<equiv> ad_of (\<lambda>s X. \<forall>a. (a, snd s) \<in> X)"
abbreviation ang2 :: "st angelic_design" where "ang2 \<equiv> ad_of (\<lambda>s X. \<forall>b. (fst s, b) \<in> X)"
abbreviation set1 :: "bool \<Rightarrow> st angelic_design" where "set1 a \<equiv> ad_of (\<lambda>s X. (a, snd s) \<in> X)"

abbreviation Eq :: "st set" where "Eq \<equiv> {x. fst x = snd x}"
abbreviation Neq :: "st set" where "Neq \<equiv> {x. fst x \<noteq> snd x}"

(* the angel in the right branch sees the demon in the left branch *)
lemma probe_par_clairvoyant: "est (dem1 \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ang2) s0 Eq"
proof -
  have H: "\<forall>XL XR. (\<exists>a. (a, snd s0) \<in> XL) \<longrightarrow> (\<forall>b. (fst s0, b) \<in> XR) \<longrightarrow>
             (\<exists>x\<in>XL. \<exists>y\<in>XR. (fst x, snd y) \<in> Eq)"
  proof (intro allI impI)
    fix XL XR :: "st set"
    assume "\<exists>a. (a, snd s0) \<in> XL" "\<forall>b. (fst s0, b) \<in> XR"
    then obtain a where "(a, snd s0) \<in> XL" "(fst s0, a) \<in> XR" by blast
    then show "\<exists>x\<in>XL. \<exists>y\<in>XR. (fst x, snd y) \<in> Eq" by force
  qed
  show ?thesis
    by (subst est_par_fun[where f="\<lambda>a b. (fst a, snd b)"]) (use H in auto)
qed

lemma probe_seq_dem_ang: "est (dem1 ;;\<^sub>A\<^sub>D ang2) s0 Eq"
  by (subst est_seq) auto

lemma probe_seq_ang_dem: "\<not> est (ang2 ;;\<^sub>A\<^sub>D dem1) s0 Eq"
proof
  have eqS: "ang2 ;;\<^sub>A\<^sub>D dem1 = ad_of (\<lambda>s Z. \<forall>b. (fst s, b) \<in> {s1. \<exists>a. (a, snd s1) \<in> Z})"
    by (rule ad_seq_ad_of[where RP="\<lambda>s X. \<forall>b. (fst s, b) \<in> X" and RQ="\<lambda>s X. \<exists>a. (a, snd s) \<in> X"])
       blast
  have W: "\<forall>b. (fst s0, b) \<in> {s1. \<exists>a. (a, snd s1) \<in> Neq}" by (simp add: ex_bool_eq)
  then have obs: "(ang2 ;;\<^sub>A\<^sub>D dem1) (ades_obs True s0 True Neq)"
    unfolding eqS ad_of_obs by simp
  assume E: "est (ang2 ;;\<^sub>A\<^sub>D dem1) s0 Eq"
  from E[unfolded est_def, rule_format, OF obs] show False by auto
qed

(* parallel only sub-distributes over angelic choice *)
lemma probe_par_angelic_left: "est ((set1 False \<squnion>\<^sub>A\<^sub>D set1 True) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) s0 Eq"
proof -
  have H: "\<forall>XL XR. ((False, snd s0) \<in> XL \<and> (True, snd s0) \<in> XL) \<longrightarrow> (\<exists>b. (fst s0, b) \<in> XR) \<longrightarrow>
             (\<exists>x\<in>XL. \<exists>y\<in>XR. (fst x, snd y) \<in> Eq)"
  proof (intro allI impI)
    fix XL XR :: "st set"
    assume A: "(False, snd s0) \<in> XL \<and> (True, snd s0) \<in> XL" and "\<exists>b. (fst s0, b) \<in> XR"
    then obtain b where "(fst s0, b) \<in> XR" by blast
    moreover have "(b, snd s0) \<in> XL" using A by (cases b) auto
    ultimately show "\<exists>x\<in>XL. \<exists>y\<in>XR. (fst x, snd y) \<in> Eq" by force
  qed
  show ?thesis
    unfolding ad_of_angelic
    by (subst est_par_fun[where f="\<lambda>a b. (fst a, snd b)"]) (use H in auto)
qed

lemma probe_par_angelic_right:
  "\<not> est ((set1 False \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) \<squnion>\<^sub>A\<^sub>D (set1 True \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2)) s0 Eq"
proof -
  let ?Z = "{(False, True), (True, False)}"
  have E: "set1 a \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2 = ad_of (\<lambda>x Z. \<exists>XL XR. (a, snd x) \<in> XL \<and>
      (\<exists>b. (fst x, b) \<in> XR) \<and> (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd x sL sR s'))" for a
    by (rule ad_par_ad_of[where RP="\<lambda>s X. (a, snd s) \<in> X" and RQ="\<lambda>s X. \<exists>b. (fst s, b) \<in> X"
          and j=jfd]) auto
  have "(set1 False \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) (ades_obs True s0 True ?Z)"
    apply (simp only: E ad_of_obs simp_thms)
    apply (rule exI[of _ "{(False, snd s0)}"])
    apply (rule exI[of _ "{(fst s0, True)}"])
    apply auto
    done
  moreover have "(set1 True \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) (ades_obs True s0 True ?Z)"
    apply (simp only: E ad_of_obs simp_thms)
    apply (rule exI[of _ "{(True, snd s0)}"])
    apply (rule exI[of _ "{(fst s0, False)}"])
    apply auto
    done
  ultimately have "((set1 False \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) \<squnion>\<^sub>A\<^sub>D (set1 True \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2))
      (ades_obs True s0 True ?Z)"
    by (simp add: inf_fun_def)
  then show ?thesis
  proof (intro notI)
    assume obs: "((set1 False \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) \<squnion>\<^sub>A\<^sub>D (set1 True \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2))
      (ades_obs True s0 True ?Z)"
      and "est ((set1 False \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) \<squnion>\<^sub>A\<^sub>D (set1 True \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2)) s0 Eq"
    from this(2)[unfolded est_def, rule_format, OF obs] show False by auto
  qed
qed

(* one-way exchange law: sequencing the two rounds lets the demon see the angel *)
lemma probe_exchange_par: "est (ang1 \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2) s0 Neq"
proof -
  have H: "\<forall>XL XR. (\<forall>a. (a, snd s0) \<in> XL) \<longrightarrow> (\<exists>b. (fst s0, b) \<in> XR) \<longrightarrow>
             (\<exists>x\<in>XL. \<exists>y\<in>XR. (fst x, snd y) \<in> Neq)"
  proof (intro allI impI)
    fix XL XR :: "st set"
    assume "\<forall>a. (a, snd s0) \<in> XL" "\<exists>b. (fst s0, b) \<in> XR"
    then obtain b where "(\<not> b, snd s0) \<in> XL" "(fst s0, b) \<in> XR" by blast
    then show "\<exists>x\<in>XL. \<exists>y\<in>XR. (fst x, snd y) \<in> Neq" by force
  qed
  show ?thesis
    by (subst est_par_fun[where f="\<lambda>a b. (fst a, snd b)"]) (use H in auto)
qed

lemma probe_exchange_seq:
  "\<not> est ((ang1 \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Skip_AD) ;;\<^sub>A\<^sub>D (Skip_AD \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2)) s0 Neq"
proof -
  define RA where "RA = (\<lambda>(s::st) Z. \<exists>XL XR. (\<forall>a. (a, snd s) \<in> XL) \<and> s \<in> XR \<and>
      (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd s sL sR s'))"
  define RB where "RB = (\<lambda>(s::st) Z. \<exists>XL XR. s \<in> XL \<and> (\<exists>b. (fst s, b) \<in> XR) \<and>
      (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd s sL sR s'))"
  have A: "ang1 \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Skip_AD = ad_of RA"
    unfolding Skip_AD_ad_of RA_def
    by (rule ad_par_ad_of[where RP="\<lambda>s X. \<forall>a. (a, snd s) \<in> X" and RQ="\<lambda>s X. s \<in> X" and j=jfd]) auto
  have B: "Skip_AD \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> dem2 = ad_of RB"
    unfolding Skip_AD_ad_of RB_def
    by (rule ad_par_ad_of[where RP="\<lambda>s X. s \<in> X" and RQ="\<lambda>s X. \<exists>b. (fst s, b) \<in> X" and j=jfd]) auto
  have neA: "\<And>s X. RA s X \<Longrightarrow> X \<noteq> {}"
    unfolding RA_def by fastforce
  have RB_Eq: "RB s1 Eq" for s1
    unfolding RB_def
    by (rule exI[of _ "{s1}"], rule exI[of _ "{(fst s1, fst s1)}"]) auto
  have RA_UNIV: "RA s0 UNIV"
    unfolding RA_def by (rule exI[of _ UNIV], rule exI[of _ UNIV]) auto
  have "(ad_of RA ;;\<^sub>A\<^sub>D ad_of RB) (ades_obs True s0 True Eq)"
    using RB_Eq RA_UNIV by (simp add: ad_seq_ad_of[OF neA])
  then show ?thesis
    unfolding A B est_def by auto
qed

section \<open>General laws on offered families\<close>

subsection \<open>Frame-disjoint sandwich: P;;Q \<sqsubseteq> P \<parallel> Q and Q;;P \<sqsubseteq> P \<parallel> Q\<close>

(* lift a family on one component to the product state, keeping the other component *)
definition lftL :: "('a \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" where
  "lftL U s0 X \<longleftrightarrow> (\<exists>X1. U (fst s0) X1 \<and> (\<forall>a\<in>X1. (a, snd s0) \<in> X))"

definition lftR :: "('b \<Rightarrow> 'b set \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" where
  "lftR V s0 X \<longleftrightarrow> (\<exists>X2. V (snd s0) X2 \<and> (\<forall>b\<in>X2. (fst s0, b) \<in> X))"

lemma lftL_ne: "(\<And>t X. U t X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow> lftL U s0 X \<Longrightarrow> X \<noteq> {}"
  unfolding lftL_def by fastforce

lemma lftR_ne: "(\<And>t X. V t X \<Longrightarrow> X \<noteq> {}) \<Longrightarrow> lftR V s0 X \<Longrightarrow> X \<noteq> {}"
  unfolding lftR_def by fastforce

lemma par_refines_seq_LR:
  assumes U: "\<And>t X. U t X \<Longrightarrow> X \<noteq> {}" and V: "\<And>t X. V t X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of (lftL U) ;;\<^sub>A\<^sub>D ad_of (lftR V) \<sqsubseteq> ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V)"
proof -
  have H: "lftL U s {s1. lftR V s1 Z}"
    if L: "lftL U s XL" and R: "lftR V s XR"
      and M0: "\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd s sL sR s'" for s XL XR Z
  proof -
    have M: "\<forall>sL\<in>XL. \<forall>sR\<in>XR. (fst sL, snd sR) \<in> Z" using M0 by simp
    obtain X1 where X1: "U (fst s) X1" "\<forall>a\<in>X1. (a, snd s) \<in> XL"
      using L unfolding lftL_def by blast
    obtain X2 where X2: "V (snd s) X2" "\<forall>b\<in>X2. (fst s, b) \<in> XR"
      using R unfolding lftR_def by blast
    have "lftR V (a, snd s) Z" if "a \<in> X1" for a
    proof -
      have "\<forall>b\<in>X2. (a, b) \<in> Z"
      proof
        fix b assume "b \<in> X2"
        then have "(a, snd s) \<in> XL" "(fst s, b) \<in> XR" using X1(2) X2(2) that by auto
        from M[rule_format, OF this] show "(a, b) \<in> Z" by simp
      qed
      with X2(1) show ?thesis unfolding lftR_def by auto
    qed
    with X1(1) show ?thesis unfolding lftL_def by auto
  qed
  have neL: "\<And>s X. lftL U s X \<Longrightarrow> X \<noteq> {}"
    using U unfolding lftL_def by fastforce
  have neR: "\<And>s X. lftR V s X \<Longrightarrow> X \<noteq> {}"
    using V unfolding lftR_def by fastforce
  have eqS: "ad_of (lftL U) ;;\<^sub>A\<^sub>D ad_of (lftR V) = ad_of (\<lambda>s Z. lftL U s {s1. lftR V s1 Z})"
    by (rule ad_seq_ad_of[where RP="lftL U" and RQ="lftR V"], fact neL)
  have eqP: "ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V) = ad_of (\<lambda>s Z. \<exists>XL XR. lftL U s XL \<and> lftR V s XR \<and>
      (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd s sL sR s'))"
    by (rule ad_par_ad_of[where RP="lftL U" and RQ="lftR V" and j=jfd], fact neL, fact neR)
  show ?thesis
    unfolding eqS eqP
    apply (rule ad_of_refine)
    apply (elim exE conjE)
    apply (rule H)
      apply assumption+
    done
qed

lemma par_refines_seq_RL:
  assumes U: "\<And>t X. U t X \<Longrightarrow> X \<noteq> {}" and V: "\<And>t X. V t X \<Longrightarrow> X \<noteq> {}"
  shows "ad_of (lftR V) ;;\<^sub>A\<^sub>D ad_of (lftL U) \<sqsubseteq> ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V)"
proof -
  have H: "lftR V s {s1. lftL U s1 Z}"
    if L: "lftL U s XL" and R: "lftR V s XR"
      and M0: "\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd s sL sR s'" for s XL XR Z
  proof -
    have M: "\<forall>sL\<in>XL. \<forall>sR\<in>XR. (fst sL, snd sR) \<in> Z" using M0 by simp
    obtain X1 where X1: "U (fst s) X1" "\<forall>a\<in>X1. (a, snd s) \<in> XL"
      using L unfolding lftL_def by blast
    obtain X2 where X2: "V (snd s) X2" "\<forall>b\<in>X2. (fst s, b) \<in> XR"
      using R unfolding lftR_def by blast
    have "lftL U (fst s, b) Z" if "b \<in> X2" for b
    proof -
      have "\<forall>a\<in>X1. (a, b) \<in> Z"
      proof
        fix a assume "a \<in> X1"
        then have "(a, snd s) \<in> XL" "(fst s, b) \<in> XR" using X1(2) X2(2) that by auto
        from M[rule_format, OF this] show "(a, b) \<in> Z" by simp
      qed
      with X1(1) show ?thesis unfolding lftL_def by auto
    qed
    with X2(1) show ?thesis unfolding lftR_def by auto
  qed
  have neL: "\<And>s X. lftL U s X \<Longrightarrow> X \<noteq> {}"
    using U unfolding lftL_def by fastforce
  have neR: "\<And>s X. lftR V s X \<Longrightarrow> X \<noteq> {}"
    using V unfolding lftR_def by fastforce
  have eqS: "ad_of (lftR V) ;;\<^sub>A\<^sub>D ad_of (lftL U) = ad_of (\<lambda>s Z. lftR V s {s1. lftL U s1 Z})"
    by (rule ad_seq_ad_of[where RP="lftR V" and RQ="lftL U"], fact neR)
  have eqP: "ad_of (lftL U) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> ad_of (lftR V) = ad_of (\<lambda>s Z. \<exists>XL XR. lftL U s XL \<and> lftR V s XR \<and>
      (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jfd s sL sR s'))"
    by (rule ad_par_ad_of[where RP="lftL U" and RQ="lftR V" and j=jfd], fact neL, fact neR)
  show ?thesis
    unfolding eqS eqP
    apply (rule ad_of_refine)
    apply (elim exE conjE)
    apply (rule H)
      apply assumption+
    done
qed

subsection \<open>Keep-either merge gives demonic choice\<close>

definition jeither :: "'s merge" where
  "jeither = (\<lambda>(m, z). z = mrg_left\<^sub>v m \<or> z = mrg_right\<^sub>v m)"

lemma jeither_eval [simp]: "merge_eval jeither s0 p q z \<longleftrightarrow> z = p \<or> z = q"
  by (simp add: jeither_def)

lemma par_either_demonic:
  assumes ne: "\<And>s X. RP s X \<Longrightarrow> X \<noteq> {}" "\<And>s X. RQ s X \<Longrightarrow> X \<noteq> {}"
    and up: "\<And>s X Y. RP s X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> RP s Y" "\<And>s X Y. RQ s X \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> RQ s Y"
    and fe: "\<And>s. \<exists>X. RP s X" "\<And>s. \<exists>X. RQ s X"
  shows "ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>jeither\<^esub> ad_of RQ = ad_of RP \<sqinter>\<^sub>A\<^sub>D ad_of RQ"
proof -
  have H: "(\<exists>XL XR. RP s XL \<and> RQ s XR \<and> (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. s' = sL \<or> s' = sR))
           = (RP s Z \<or> RQ s Z)" for s Z
  proof
    assume "\<exists>XL XR. RP s XL \<and> RQ s XR \<and> (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. s' = sL \<or> s' = sR)"
    then obtain XL XR where L: "RP s XL" and R: "RQ s XR"
      and M: "\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. s' = sL \<or> s' = sR" by blast
    show "RP s Z \<or> RQ s Z"
    proof (cases "XL \<subseteq> Z")
      case True then show ?thesis using up(1) L by blast
    next
      case False
      then obtain a where a: "a \<in> XL" "a \<notin> Z" by blast
      have "XR \<subseteq> Z" using M a by blast
      then show ?thesis using up(2) R by blast
    qed
  next
    assume "RP s Z \<or> RQ s Z"
    then show "\<exists>XL XR. RP s XL \<and> RQ s XR \<and> (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. s' = sL \<or> s' = sR)"
    proof
      assume P: "RP s Z"
      obtain Y where Y: "RQ s Y" using fe(2) by blast
      show ?thesis
        apply (rule exI[where x=Z], rule exI[where x=Y])
        using P Y by auto
    next
      assume Q: "RQ s Z"
      obtain Y where Y: "RP s Y" using fe(1) by blast
      show ?thesis
        apply (rule exI[where x=Y], rule exI[where x=Z])
        using Q Y by auto
    qed
  qed
  have eqP: "ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>jeither\<^esub> ad_of RQ = ad_of (\<lambda>s Z. \<exists>XL XR. RP s XL \<and> RQ s XR \<and>
      (\<forall>sL\<in>XL. \<forall>sR\<in>XR. \<exists>s'\<in>Z. merge_eval jeither s sL sR s'))"
    by (rule ad_par_ad_of[where RP=RP and RQ=RQ and j=jeither], fact ne(1), fact ne(2))
  show ?thesis
  proof (rule ades_obs_ext)
    fix b s0 c X
    show "(ad_of RP \<parallel>\<^sub>A\<^sub>D\<^bsub>jeither\<^esub> ad_of RQ) (ades_obs b s0 c X) =
          (ad_of RP \<sqinter>\<^sub>A\<^sub>D ad_of RQ) (ades_obs b s0 c X)"
      unfolding eqP ad_of_demonic ad_of_obs jeither_eval H ..
  qed
qed

subsection \<open>Angelic choice: one-way distribution for any operands\<close>

lemma ades_par_angelic_subdist:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<sqsubseteq> (P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
proof -
  have "P \<sqsubseteq> P \<squnion>\<^sub>A\<^sub>D P'" "P' \<sqsubseteq> P \<squnion>\<^sub>A\<^sub>D P'" "Q \<sqsubseteq> Q"
    by (simp_all add: pred_refine_iff inf_fun_def)
  then have "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> (P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
       "P' \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> (P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
    by (simp_all add: ades_par_mono)
  then show ?thesis
    by (simp add: pred_refine_iff inf_fun_def)
qed

end
