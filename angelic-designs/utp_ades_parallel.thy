section \<open>Angelic Design Parallel-by-Merge\<close>

theory utp_ades_parallel
  imports utp_ades_designs
begin

subsection \<open>Choice-set Merge\<close>

type_synonym 's ades_mrg =
  "('s astate des_vars_ext, 's achoices des_vars_ext, 's achoices des_vars_ext) mrg"

type_synonym 's ades_merge_rel = "('s ades_mrg, 's achoices des_vars_ext) urel"

abbreviation ades_merge_eval ::
  "'s ades_merge_rel \<Rightarrow> 's astate des_vars_ext \<Rightarrow>
   's achoices des_vars_ext \<Rightarrow> 's achoices des_vars_ext \<Rightarrow>
   's achoices des_vars_ext \<Rightarrow> bool"
where
"ades_merge_eval M s0 p q out \<equiv>
  M ((\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>
      :: 's ades_mrg), out)"

text \<open>
  The abbreviation ades_merge_eval hides the merge record that packages an
  initial observation, the two branch results, and a proposed merged result.

  A state merge j relates the prior state and one result from each parallel
  branch to a merged result.  The definition ades_merge_image lifts this
  relation pointwise to the two branches' choice sets.

  The exact lifting merge_ades then packages that image as a complete
  angelic-design observation.  Its output termination flag is the conjunction
  of the two branch flags, and its choice set is exactly the merged image.
  The lifting merge_ades_up replaces this equality by inclusion, giving the
  @{const PBMH_ades}-healthy upward-closed form used by the public parallel
  operator.
\<close>

(* ades_merge_image j s X Y \<equiv>
   {z | \<exists>x \<in> X. \<exists>y \<in> Y. j(s, x, y, z)}. *)
definition ades_merge_image ::
  "'s merge \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow> 's set" where
"ades_merge_image j s0 X Y =
  {z. \<exists>x \<in> X. \<exists>y \<in> Y.
    j ((\<lparr>mrg_prior\<^sub>v = s0, mrg_left\<^sub>v = x, mrg_right\<^sub>v = y, \<dots> = ()\<rparr> :: ('s, 's, 's) mrg), z)}"

(* M\<^sub>A\<^sub>D(j) \<equiv> (ok' = ok\<^sub>0 \<and> ok\<^sub>1) \<and>
   ac' = ades_merge_image j s ac\<^sub>0 ac\<^sub>1. *)
definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" ("M\<^sub>A\<^sub>D'(_')") where
"merge_ades j = (\<lambda> (m, out).
  des_vars.ok\<^sub>v out = (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  achoices.ac\<^sub>v (des_vars.more out) =
    ades_merge_image j
      (astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m)))
      (achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)))
      (achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m))))"

(* M\<^sub>A\<^sub>D\<^sup>\<up>(j) \<equiv> (ok' = ok\<^sub>0 \<and> ok\<^sub>1) \<and>
   ades_merge_image j s ac\<^sub>0 ac\<^sub>1 \<subseteq> ac'. *)
definition merge_ades_up :: "'s merge \<Rightarrow> 's ades_merge_rel" ("M\<^sub>A\<^sub>D\<^sup>\<up>'(_')") where
"merge_ades_up j = (\<lambda> (m, out).
  des_vars.ok\<^sub>v out = (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  ades_merge_image j
    (astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m)))
    (achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)))
    (achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m)))
    \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"

lemma ades_merge_image_mono:
  fixes s :: "'s"
  assumes "X \<subseteq> X'" "Y \<subseteq> Y'"
  shows "ades_merge_image j s X Y \<subseteq> ades_merge_image j s X' Y'"
  using assms by (auto simp: ades_merge_image_def)

lemma ades_merge_image_assoc:
  fixes s :: "'s"
  assumes "swap\<^sub>m ;; j = j" "AssocMerge j"
  shows "ades_merge_image j s (ades_merge_image j s X Y) Z =
    ades_merge_image j s X (ades_merge_image j s Y Z)"
proof -
  have rotate: "\<And>x y z out.
      (\<exists>u. merge_eval j s x y u \<and> merge_eval j s u z out) =
      (\<exists>u. merge_eval j s y z u \<and> merge_eval j s u x out)"
    using assms(2)
    by (simp add: AssocMerge_def ThreeWayMerge_def fun_eq_iff;
        pred_auto)
  have swap: "\<And>u x out.
      merge_eval j s u x out = merge_eval j s x u out"
    using assms(1)
    by (simp add: fun_eq_iff; pred_auto)
  show ?thesis
    apply (rule Set.set_eqI)
    unfolding ades_merge_image_def
    using rotate swap
    by blast
qed

lemma merge_ades_swap:
  fixes j :: "'s merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; M\<^sub>A\<^sub>D(j) = M\<^sub>A\<^sub>D(j)"
  using assms
  by (simp add: merge_ades_def ades_merge_image_def fun_eq_iff; pred_auto; blast)

lemma merge_ades_up_swap:
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; M\<^sub>A\<^sub>D\<^sup>\<up>(j) = M\<^sub>A\<^sub>D\<^sup>\<up>(j)"
  using assms
  by (simp add: merge_ades_up_def ades_merge_image_def fun_eq_iff;
      pred_auto; blast)

lemma achoices_upward_chain:
  fixes A :: "'s set" and F :: "'s set \<Rightarrow> 's set"
    and K :: "bool \<Rightarrow> bool" and out :: "'s achoices des_vars_ext"
  assumes mono: "\<And>X. A \<subseteq> X \<Longrightarrow> F A \<subseteq> F X"
  shows "(\<exists>u :: 's achoices des_vars_ext.
      (des_vars.ok\<^sub>v u = b \<and>
       A \<subseteq> achoices.ac\<^sub>v (des_vars.more u)) \<and>
      (des_vars.ok\<^sub>v out = K (des_vars.ok\<^sub>v u) \<and>
       F (achoices.ac\<^sub>v (des_vars.more u))
         \<subseteq> achoices.ac\<^sub>v (des_vars.more out))) =
    (des_vars.ok\<^sub>v out = K b \<and>
      F A \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"
  apply (rule iffI)
   apply (elim exE conjE)
   apply (rule conjI)
    apply simp
   apply (drule mono)
   apply blast
  apply (elim conjE)
  apply (rule exI[where x=
      "\<lparr>ok\<^sub>v = b, ac\<^sub>v = A, \<dots> = ()\<rparr>"])
  by simp

lemma merge_ades_up_eval:
  fixes j :: "'s merge" and s0 :: "'s astate des_vars_ext"
    and p q out :: "'s achoices des_vars_ext"
  shows "ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 p q out =
    (des_vars.ok\<^sub>v out =
        (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<and>
      ades_merge_image j (astate.s\<^sub>v (des_vars.more s0))
        (achoices.ac\<^sub>v (des_vars.more p))
        (achoices.ac\<^sub>v (des_vars.more q))
      \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"
  by (simp add: merge_ades_up_def ades_merge_image_def)

lemma merge_ades_up_chain_left_eval:
  fixes j :: "'s merge"
    and s0 :: "'s astate des_vars_ext"
    and p q r out :: "'s achoices des_vars_ext"
  shows "(\<exists>u.
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 p q u \<and>
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 u r out) =
         (des_vars.ok\<^sub>v out =
            ((des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<and> des_vars.ok\<^sub>v r) \<and>
          ades_merge_image j (astate.s\<^sub>v (des_vars.more s0))
            (ades_merge_image j (astate.s\<^sub>v (des_vars.more s0))
              (achoices.ac\<^sub>v (des_vars.more p))
              (achoices.ac\<^sub>v (des_vars.more q)))
            (achoices.ac\<^sub>v (des_vars.more r))
          \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"
  apply (simp only: merge_ades_up_eval)
  apply (rule achoices_upward_chain)
  apply (rule ades_merge_image_mono)
   apply assumption
  by (rule subset_refl)

lemma merge_ades_up_chain_right_eval:
  fixes j :: "'s merge"
    and s0 :: "'s astate des_vars_ext"
    and p q r out :: "'s achoices des_vars_ext"
  shows "(\<exists>u.
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 q r u \<and>
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 p u out) =
         (des_vars.ok\<^sub>v out =
            (des_vars.ok\<^sub>v p \<and> (des_vars.ok\<^sub>v q \<and> des_vars.ok\<^sub>v r)) \<and>
          ades_merge_image j (astate.s\<^sub>v (des_vars.more s0))
            (achoices.ac\<^sub>v (des_vars.more p))
            (ades_merge_image j (astate.s\<^sub>v (des_vars.more s0))
              (achoices.ac\<^sub>v (des_vars.more q))
              (achoices.ac\<^sub>v (des_vars.more r)))
          \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"
  apply (simp only: merge_ades_up_eval)
  apply (rule achoices_upward_chain)
  apply (rule ades_merge_image_mono)
   apply (rule subset_refl)
  by assumption

lemma merge_ades_up_assoc:
  fixes j :: "'s merge"
    and s0 :: "'s astate des_vars_ext"
    and p q r out :: "'s achoices des_vars_ext"
  assumes "swap\<^sub>m ;; j = j" "AssocMerge j"
  shows "(\<exists>u.
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 p q u \<and>
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 u r out) =
         (\<exists>u.
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 q r u \<and>
           ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 p u out)"
  by (simp only: merge_ades_up_chain_left_eval
      merge_ades_up_chain_right_eval
      ades_merge_image_assoc[OF assms] conj_assoc)

lemma PBMH_ades_par_raw:
  "PBMH_ades (P \<parallel>\<^bsub>M\<^sub>A\<^sub>D(j)\<^esub> Q) = P \<parallel>\<^bsub>M\<^sub>A\<^sub>D\<^sup>\<up>(j)\<^esub> Q"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def
      par_by_merge_def par_sep_def merge_ades_def merge_ades_up_def
      ades_merge_image_def fun_eq_iff; pred_auto; blast)

subsection \<open>Parallel Composition\<close>

abbreviation ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow>
   's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^bsub>M\<^sub>A\<^sub>D\<^sup>\<up>(j)\<^esub> Q"

(* (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)(s\<^sub>0, out) \<longleftrightarrow> (\<exists>p q. P(s\<^sub>0, p) \<and> Q(s\<^sub>0, q) \<and> M\<^sub>A\<^sub>D\<^sup>\<up>(j)(\<langle>s\<^sub>0, p, q\<rangle>, out)). *)
lemma ades_par_eval':
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (s0, out) \<longleftrightarrow>
   (\<exists>p q. P (s0, p) \<and> Q (s0, q) \<and>
     ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(j) s0 p q out)"
  by (cases s0; cases out;
      simp add: par_by_merge_def par_sep_def;
      pred_auto; blast)

(* (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q)(s\<^sub>0, out) \<longleftrightarrow>
   (\<exists>p q. P(s\<^sub>0, p) \<and> Q(s\<^sub>0, q) \<and> out.ok = (p.ok \<and> q.ok) \<and>
     {z | \<exists>x \<in> p.ac. \<exists>y \<in> q.ac. j(s\<^sub>0.s, x, y, z)} \<subseteq> out.ac). *)
lemma ades_par_eval:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (s0, out) \<longleftrightarrow>
   (\<exists>p q. P (s0, p) \<and> Q (s0, q) \<and>
     des_vars.ok\<^sub>v out = (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<and>
     {z. \<exists>x \<in> achoices.ac\<^sub>v (des_vars.more p).
         \<exists>y \<in> achoices.ac\<^sub>v (des_vars.more q).
           j (\<lparr>mrg_prior\<^sub>v = astate.s\<^sub>v (des_vars.more s0),
               mrg_left\<^sub>v = x, mrg_right\<^sub>v = y, \<dots> = ()\<rparr>, z)}
       \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"
  by (simp only: ades_par_eval' merge_ades_up_eval ades_merge_image_def)

subsection \<open>Merge Conditions\<close>

text \<open>
  Conditions on the state-level merge are named after the healthiness
  condition whose parallel closure they support, in the style of the
  reactive R1m family: A0j (totality) for @{const A0},
  A2j (functionality) for @{const A2}, and A3j (an excluded singleton
  image at every prior state) for @{const A3}.  These are boolean
  side conditions rather than healthiness operators.
\<close>

(* A0j means every pair of branch results has some merged result. *)
(* A0j(j) \<equiv> (\<forall>s p q. \<exists>z. j(\<langle>s, p, q\<rangle>, z)). *)
definition A0j :: "'s merge \<Rightarrow> bool" where
"A0j j \<equiv> (\<forall>s p q. \<exists>z. j (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z))"

(* A2j means every pair of branch results has at most one merged result. *)
(* A2j(j) \<equiv> (\<forall>s p q z\<^sub>1 z\<^sub>2.
     j(\<langle>s, p, q\<rangle>, z\<^sub>1) \<and> j(\<langle>s, p, q\<rangle>, z\<^sub>2) \<longrightarrow> z\<^sub>1 = z\<^sub>2). *)
definition A2j :: "'s merge \<Rightarrow> bool" where
"A2j j \<equiv>
  (\<forall>s p q z1 z2.
    j (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z1) \<longrightarrow>
    j (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z2) \<longrightarrow> z1 = z2)"

(* A3j means every prior state has a singleton that is never an exact merge image. *)
(* A3j(j) \<equiv> (\<forall>s. \<exists>z. \<forall>X Y. ades_merge_image j s X Y \<noteq> {z}). *)
definition A3j :: "'s merge \<Rightarrow> bool" where
"A3j j \<equiv> (\<forall>s. \<exists>z. \<forall>X Y. ades_merge_image j s X Y \<noteq> {z})"

(* A0j(j) \<and> X \<noteq> {} \<and> Y \<noteq> {} \<Longrightarrow> ades_merge_image j s X Y \<noteq> {}. *)
lemma ades_merge_image_nonempty:
  fixes s :: "'s"
  assumes "A0j j" "X \<noteq> {}" "Y \<noteq> {}"
  shows "ades_merge_image j s X Y \<noteq> {}"
proof -
  obtain x where x: "x \<in> X" using assms(2) by blast
  obtain y where y: "y \<in> Y" using assms(3) by blast
  have "\<exists>z. merge_eval j s x y z"
    using assms(1) by (simp add: A0j_def)
  then obtain z where "merge_eval j s x y z" by blast
  then show ?thesis
    using x y by (auto simp: ades_merge_image_def)
qed

text \<open>
  Totality survives enlarging a merge, while functionality survives
  shrinking one.  Singleton-image exclusion need not survive shrinking:
  a larger image can become a singleton.  The canonical @{term skip\<^sub>m}
  merge satisfies @{const A3j} whenever the state space has at least two elements.
\<close>

lemma A0j_enlarge: "\<lbrakk> A0j j1; j2 \<sqsubseteq> j1 \<rbrakk> \<Longrightarrow> A0j j2"
  by (simp add: A0j_def pred_refine_iff; blast)

lemma A2j_restrict: "\<lbrakk> A2j j2; j2 \<sqsubseteq> j1 \<rbrakk> \<Longrightarrow> A2j j1"
  by (simp add: A2j_def pred_refine_iff; blast)

lemma skip_merge_eval:
  fixes s p q z :: "'s"
  shows "skip\<^sub>m (\<lparr>mrg_prior\<^sub>v = s, mrg_left\<^sub>v = p, mrg_right\<^sub>v = q, \<dots> = ()\<rparr>, z) \<longleftrightarrow> z = s"
  by pred_auto

lemma skip_merge_A0j [simp]: "A0j skip\<^sub>m"
  by (simp add: A0j_def skip_merge_eval)

lemma skip_merge_A2j: "A2j skip\<^sub>m"
  by (simp add: A2j_def skip_merge_eval)

lemma skip_merge_A3j:
  assumes "\<exists>(a::'s) b. a \<noteq> b"
  shows "A3j (skip\<^sub>m :: 's merge)"
proof (unfold A3j_def, rule allI)
  fix s :: 's
  obtain a b where ab: "(a::'s) \<noteq> b" using assms by blast
  have "(if s = a then b else a) \<noteq> s" using ab by auto
  then have "\<And>X Y. (if s = a then b else a) \<notin> ades_merge_image skip\<^sub>m s X Y"
    by (simp add: ades_merge_image_def skip_merge_eval)
  then show "\<exists>z. \<forall>X Y. ades_merge_image skip\<^sub>m s X Y \<noteq> {z}"
    by blast
qed

subsection \<open>Merge Healthiness by Including Skip\<close>

text \<open>
  The healthiness operator H0 adds the prior state as a permitted merge
  result for every pair of branch results.  Its fixed points satisfy a
  stronger condition than @{const A0j}: they always permit this particular
  result, whereas totality only requires some result.  Other merged results
  remain permitted.  If functionality @{const A2j} is also required, however,
  the prior state must be the only result, so the merge is @{term skip\<^sub>m}.
\<close>

definition H0 :: "'s merge \<Rightarrow> 's merge" where
  [pred]: "H0 j = (j \<or> skip\<^sub>m)"

lemma H0_eval:
  fixes j :: "'s merge" and s p q z :: 's
  shows "merge_eval (H0 j) s p q z \<longleftrightarrow>
    (merge_eval j s p q z \<or> z = s)"
  by (simp add: H0_def disj_pred_def skip_merge_eval)

lemma H0_idem: "H0 (H0 j) = H0 j"
  by (simp add: H0_def disj_pred_def sup_assoc)

lemma H0_Idempotent [closure]: "Idempotent H0"
  by (simp add: Idempotent_def H0_idem)

lemma H0_mono: "j \<sqsubseteq> k \<Longrightarrow> H0 j \<sqsubseteq> H0 k"
  by (simp add: H0_def pred_refine_iff disj_pred_def; blast)

lemma H0_Monotonic [closure]: "Monotonic H0"
  by (rule MonotonicI, rule H0_mono)

lemma H0_healthy [closure]: "H0 j is H0"
  by (rule Healthy_Idempotent[OF H0_Idempotent])

lemma H0_healthy_iff:
  fixes j :: "'s merge"
  shows "j is H0 \<longleftrightarrow> (\<forall>s p q. merge_eval j s p q s)"
  by (simp add: Healthy_def H0_def fun_eq_iff; pred_auto; blast)

lemma skip_merge_is_H0 [closure]: "skip\<^sub>m is H0"
  by (simp add: Healthy_def H0_def disj_pred_def)

lemma H0_A0j: "A0j (H0 j)"
  by (simp add: A0j_def H0_eval; blast)

lemma H0_healthy_A0j:
  assumes "j is H0"
  shows "A0j j"
  using H0_A0j[of j] by (simp only: Healthy_if[OF assms])

subsection \<open>Healthiness Closure\<close>

text \<open>
  The composition is unconditionally @{const PBMH_ades}-healthy and
  preserves the design and angelic healthiness conditions under the
  operand and merge assumptions below.  @{const A2} and @{const A3}
  closure are developed in the following subsections.
\<close>

lemma ades_par_is_PBMH_ades [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is PBMH_ades"
  by (simp only: Healthy_def' PBMH_ades_par_raw[symmetric]
      PBMH_ades_idem)

(* Compatibility with the pending RAD parallel development. *)
lemmas ades_par_PBMH_ades = ades_par_is_PBMH_ades

lemma ades_par_H1_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
  using assms
  by (simp add: Healthy_def' H1_def par_by_merge_def par_sep_def
      merge_ades_up_def ades_merge_image_def fun_eq_iff;
      pred_auto; blast)

lemma ades_par_H2_closure [closure]:
  assumes "P is H2" "Q is H2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H2"
  using assms
  apply (simp add: H2_equiv pred_refine_iff par_by_merge_def par_sep_def
      merge_ades_up_def ades_merge_image_def)
  apply pred_auto
  subgoal for ok s ac ok\<^sub>v'' ac\<^sub>v' ok\<^sub>v''' ac\<^sub>v''
    apply (rule exI[where x=ok])
    apply (rule exI[where x=s])
    apply (rule exI[where x=True])
    apply (rule exI[where x=ac\<^sub>v'])
    apply (rule conjI)
     apply blast
    apply (rule exI[where x=True])
    apply (rule exI[where x=ac\<^sub>v''])
    by (cases ok\<^sub>v'''; auto)
  subgoal for ok s ac ok\<^sub>v'' ac\<^sub>v' ok\<^sub>v''' ac\<^sub>v''
    apply (rule exI[where x=ok])
    apply (rule exI[where x=s])
    apply (rule exI[where x=True])
    apply (rule exI[where x=ac\<^sub>v'])
    apply (rule conjI)
     apply (cases ok\<^sub>v''; auto)
    apply (rule exI[where x=True])
    apply (rule exI[where x=ac\<^sub>v''])
    by blast
  done

lemma ades_par_H_closure [closure]:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>H"
  using ades_par_H1_closure[OF H_implies_H1[OF assms(1)] H_implies_H1[OF assms(2)]]
    ades_par_H2_closure[OF H_implies_H2[OF assms(1)] H_implies_H2[OF assms(2)]]
  by (simp add: Healthy_def' H1_H2_comp)

text \<open>
  Totality is needed only for @{const A0}: once both successful branch
  choice sets are known to be non-empty, it supplies a merged state and so
  rules out an empty combined choice set.
\<close>

lemma ades_par_A0_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes "P is A0" "Q is A0" "A0j j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0"
  apply (rule Healthy_intro)
  apply (simp add: A0_def fun_eq_iff)
  apply (pred_auto add: merge_ades_up_def)
   apply blast
  subgoal for ok s bp X bq Y
    using A0_healthy_non_empty[OF assms(1), of
        "\<lparr>ok\<^sub>v = True, s\<^sub>v = s, \<dots> = ()\<rparr>"
        "\<lparr>ok\<^sub>v = True, ac\<^sub>v = X, \<dots> = ()\<rparr>"]
      A0_healthy_non_empty[OF assms(2), of
        "\<lparr>ok\<^sub>v = True, s\<^sub>v = s, \<dots> = ()\<rparr>"
        "\<lparr>ok\<^sub>v = True, ac\<^sub>v = Y, \<dots> = ()\<rparr>"]
      ades_merge_image_nonempty[where s=s and X=X and Y=Y, OF assms(3)]
    by (simp; blast)
  done

text \<open>
  Conversely, totality is necessary for closure over all @{const A0}-healthy
  operands.  Successful singleton choices expose any input at which the
  merge has no output: their empty merge image permits successful termination
  with an empty choice set.  The singleton predicates below are local proof
  witnesses, so no additional process operator is needed.
\<close>

lemma ades_par_A0_closure_imp_A0j:
  fixes j :: "'s merge"
  assumes closed: "\<And>P Q. P is A0 \<Longrightarrow> Q is A0 \<Longrightarrow>
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0"
  shows "A0j j"
proof -
  let ?S = "\<lambda>x. (\<lambda>(s0, out).
    des_vars.ok\<^sub>v out \<and>
    achoices.ac\<^sub>v (des_vars.more out) = {x}) :: 's angelic_design"
  have singleton_A0: "?S x is A0" for x
    by (simp add: Healthy_def A0_def fun_eq_iff; pred_auto)
  show ?thesis
  proof (unfold A0j_def, intro allI)
    fix s p q :: 's
    show "\<exists>z. merge_eval j s p q z"
    proof (rule ccontr)
      assume missing: "\<not> (\<exists>z. merge_eval j s p q z)"
      let ?R = "?S p \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ?S q"
      let ?s0 = "(\<lparr>ok\<^sub>v = True, s\<^sub>v = s, \<dots> = ()\<rparr>
        :: 's astate des_vars_ext)"
      let ?out = "(\<lparr>ok\<^sub>v = True, ac\<^sub>v = {}, \<dots> = ()\<rparr>
        :: 's achoices des_vars_ext)"
      have healthy: "?R is A0"
        by (rule closed; rule singleton_A0)
      have accepted: "?R (?s0, ?out)"
        unfolding ades_par_eval
        apply (rule exI[where x="\<lparr>ok\<^sub>v = True, ac\<^sub>v = {p}, \<dots> = ()\<rparr>"])
        apply (rule exI[where x="\<lparr>ok\<^sub>v = True, ac\<^sub>v = {q}, \<dots> = ()\<rparr>"])
        using missing by auto
      have no_failure: "\<not> ?R (?s0, ok\<^sub>v_update (\<lambda>_. False) ?out)"
        by (auto simp: ades_par_eval)
      have "achoices.ac\<^sub>v (des_vars.more ?out) \<noteq> {}"
        by (rule A0_healthy_non_empty[OF healthy accepted _ no_failure]; simp)
      then show False by simp
    qed
  qed
qed

lemma ades_par_A0_closure_iff_A0j:
  fixes j :: "'s merge"
  shows "(\<forall>P Q. P is A0 \<longrightarrow> Q is A0 \<longrightarrow>
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0) \<longleftrightarrow> A0j j"
  using ades_par_A0_closure_imp_A0j[of j] ades_par_A0_closure[where j=j]
  by blast

text \<open>
  H0-healthiness supplies the totality premise of @{thm ades_par_A0_closure}.
  Applying H0 to any merge therefore gives @{const A0} closure as well.
\<close>

lemma ades_par_A0_closure_H0 [closure]:
  assumes "P is A0" "Q is A0" "j is H0"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0"
  by (rule ades_par_A0_closure[OF assms(1,2) H0_healthy_A0j[OF assms(3)]])

lemma ades_par_A0_closure_H0_image [closure]:
  assumes "P is A0" "Q is A0"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>H0 j\<^esub> Q) is A0"
  by (rule ades_par_A0_closure[OF assms H0_A0j])

lemma ades_par_A1_closure [closure]:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A1"
proof -
  have R_H: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>H"
    by (rule ades_par_H_closure[OF assms])
  show ?thesis
    by (simp add: Healthy_def' A1_eq_PBMH_ades[OF R_H]
        Healthy_if[OF ades_par_is_PBMH_ades])
qed

lemma ades_par_A_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes "P is A" "Q is A" "A0j j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
proof -
  have R0: "(A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) is A0"
    by (rule ades_par_A0_closure; simp add: Healthy_def' A_def A0_idem assms(3))
  have R1: "(A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q) is A1"
    by (rule ades_par_A1_closure; simp add: Healthy_def' A_is_H)
  show ?thesis
    using R0 R1
    by (simp only: Healthy_if[OF assms(1)] Healthy_if[OF assms(2)] Healthy_def';
        simp add: A_def)
qed

subsection \<open>A2 Closure at the Choice-set Level\<close>

text \<open>
  The following helper combines two choice-set relations through the state
  merge. It supports @{const A2} closure by fixing the outer control flags,
  and @{const A3} closure through the design precondition below.
\<close>

definition ades_par_rel ::
  "'s merge \<Rightarrow> 's angelic_rel \<Rightarrow> 's angelic_rel \<Rightarrow> 's angelic_rel" where
[pred]: "ades_par_rel j P Q = (\<lambda>(s0, out).
  \<exists>X Y.
    P (s0, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>) \<and>
    Q (s0, \<lparr>ac\<^sub>v = Y, \<dots> = ()\<rparr>) \<and>
    ades_merge_image j (astate.s\<^sub>v s0) X Y \<subseteq> achoices.ac\<^sub>v out)"

text \<open>
  A functional (single-valued) merge is what @{const A2_rel} closure needs:
  the merged image of one left choice and one right choice is then empty or
  a singleton, so the singleton reduction of the operands transports to the
  composition.  No totality is required.
\<close>

lemma ades_par_rel_A2_rel_closure [closure]:
  fixes P Q :: "'s angelic_rel" and j :: "'s merge"
  assumes "P is A2_rel" "Q is A2_rel" "A2j j"
  shows "ades_par_rel j P Q is A2_rel"
proof -
  let ?C = "ades_par_rel j P Q"
  have expand: "\<And>R s0 X. R is A2_rel \<Longrightarrow>
      R (s0, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>) \<Longrightarrow>
      R (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<or>
      (\<exists>x \<in> X. R (s0, \<lparr>ac\<^sub>v = {x}, \<dots> = ()\<rparr>))"
    apply (simp only: Healthy_def' A2_rel_eq_expanded)
    subgoal for R s0 X
      by (drule fun_cong[where x="(s0, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>)"];
          simp add: A2_rel_expanded_def)
    done
  show ?thesis
  proof (rule Healthy_intro, unfold A2_rel_eq_expanded, rule ext)
    fix w :: "'s astate \<times> 's achoices"
    obtain s0 out where w_eq [simp]: "w = (s0, out)" by (cases w)
    show "A2_rel_expanded ?C w = ?C w"
    proof
      assume "A2_rel_expanded ?C w"
      then show "?C w"
        by (simp add: A2_rel_expanded_def ades_par_rel_def; blast)
    next
      assume "?C w"
      then obtain X Y where
        PX: "P (s0, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>)" and
        QY: "Q (s0, \<lparr>ac\<^sub>v = Y, \<dots> = ()\<rparr>)" and
        img: "ades_merge_image j (astate.s\<^sub>v s0) X Y \<subseteq> achoices.ac\<^sub>v out"
        by (auto simp add: ades_par_rel_def)
      show "A2_rel_expanded ?C w"
      proof (cases "P (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<or>
          Q (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>)")
        case True
        then have "?C (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>)"
          using PX QY by (auto simp add: ades_par_rel_def ades_merge_image_def)
        then show ?thesis by (simp add: A2_rel_expanded_def; pred_auto)
      next
        case False
        then obtain x y where
          x: "x \<in> X" and Px: "P (s0, \<lparr>ac\<^sub>v = {x}, \<dots> = ()\<rparr>)" and
          y: "y \<in> Y" and Qy: "Q (s0, \<lparr>ac\<^sub>v = {y}, \<dots> = ()\<rparr>)"
          using expand[OF assms(1) PX] expand[OF assms(2) QY] by blast
        let ?I = "ades_merge_image j (astate.s\<^sub>v s0) {x} {y}"
        have "?I \<subseteq> achoices.ac\<^sub>v out"
          using x y img by (auto simp add: ades_merge_image_def)
        moreover have "\<And>z. z \<in> ?I \<Longrightarrow> ?I \<subseteq> {z}"
          using assms(3) by (auto simp add: ades_merge_image_def A2j_def)
        ultimately have "?I = {} \<or> (\<exists>z \<in> achoices.ac\<^sub>v out. ?I \<subseteq> {z})"
          by blast
        then show ?thesis using Px Qy
          by (simp add: A2_rel_expanded_def ades_par_rel_def; blast)
      qed
    qed
  qed
qed

text \<open>
  Functionality is not gratuitous: under the total but two-valued
  universal merge, the composition of two @{const A2_rel}-healthy
  relations accepts only the universal choice set and so cannot be
  reconstructed from empty and singleton choice sets.
\<close>

definition ades_univ_merge :: "'s merge" where
"ades_univ_merge = (\<lambda>(m, z). True)"

lemma ades_univ_merge_A0j: "A0j ades_univ_merge"
  by (simp add: A0j_def ades_univ_merge_def)

lemma ades_univ_merge_not_A2j: "\<not> A2j (ades_univ_merge :: bool merge)"
  by (simp add: A2j_def ades_univ_merge_def; blast)

lemma ades_par_rel_A2_rel_counterexample:
  fixes NE :: "bool angelic_rel"
  defines "NE \<equiv> (\<lambda>(s0, out). achoices.ac\<^sub>v out \<noteq> {})"
  shows "NE is A2_rel"
    and "\<not> (ades_par_rel ades_univ_merge NE NE is A2_rel)"
proof -
  show "NE is A2_rel"
    by (simp add: Healthy_def' A2_rel_eq_expanded A2_rel_expanded_def NE_def
        fun_eq_iff; pred_auto)
  have comp: "\<And>(s0 :: bool astate) out.
      ades_par_rel ades_univ_merge NE NE (s0, out) \<longleftrightarrow>
      achoices.ac\<^sub>v out = UNIV"
  proof
    fix s0 :: "bool astate" and out :: "bool achoices"
    assume "ades_par_rel ades_univ_merge NE NE (s0, out)"
    then obtain X Y where ne: "X \<noteq> {}" "Y \<noteq> {}" and
      img: "ades_merge_image ades_univ_merge (astate.s\<^sub>v s0) X Y \<subseteq> achoices.ac\<^sub>v out"
      by (auto simp add: ades_par_rel_def NE_def)
    have "ades_merge_image ades_univ_merge (astate.s\<^sub>v s0) X Y = UNIV"
      using ne by (auto simp add: ades_merge_image_def ades_univ_merge_def)
    then show "achoices.ac\<^sub>v out = UNIV" using img by auto
  next
    fix s0 :: "bool astate" and out :: "bool achoices"
    assume "achoices.ac\<^sub>v out = UNIV"
    then have "NE (s0, \<lparr>ac\<^sub>v = {True}, \<dots> = ()\<rparr>) \<and>
        ades_merge_image ades_univ_merge (astate.s\<^sub>v s0) {True} {True}
        \<subseteq> achoices.ac\<^sub>v out"
      by (simp add: NE_def ades_merge_image_def ades_univ_merge_def)
    then show "ades_par_rel ades_univ_merge NE NE (s0, out)"
      by (auto simp add: ades_par_rel_def)
  qed
  show "\<not> (ades_par_rel ades_univ_merge NE NE is A2_rel)"
  proof
    assume "ades_par_rel ades_univ_merge NE NE is A2_rel"
    then have e: "A2_rel_expanded (ades_par_rel ades_univ_merge NE NE) =
        ades_par_rel ades_univ_merge NE NE"
      by (simp add: Healthy_def' A2_rel_eq_expanded[symmetric])
    have Cw: "ades_par_rel ades_univ_merge NE NE
        (\<lparr>s\<^sub>v = True, \<dots> = ()\<rparr>, \<lparr>ac\<^sub>v = UNIV, \<dots> = ()\<rparr>)"
      by (simp add: comp)
    have nCw: "\<not> A2_rel_expanded (ades_par_rel ades_univ_merge NE NE)
        (\<lparr>s\<^sub>v = True, \<dots> = ()\<rparr>, \<lparr>ac\<^sub>v = UNIV, \<dots> = ()\<rparr>)"
      by (auto simp add: A2_rel_expanded_def comp UNIV_bool)
    show False using Cw nCw by (simp add: e)
  qed
qed

subsection \<open>A3 Closure at the Choice-set Level\<close>

text \<open>
  For @{const A3}, totality and functionality of the merge are not enough.
  With the right-projection merge the merged image of a failure is dictated
  entirely by the successful branch, so one branch failure floods every
  singleton choice set and the precondition of the composition
  loses the singleton-witness property, even though the merge is total and
  functional and the failing operand's precondition is @{const A3_rel}-healthy.
  The counterexample depends on every singleton being an exact merge image.
  @{const A3j} excludes some singleton image at every prior state; its
  element may still occur in larger images.  Under @{const A3j} the
  negated composition is @{const A3_rel}-healthy for arbitrary operands.
  An alternative is an operand-side restriction: a precondition that is
  independent of the output choice set (the normal, condition-precondition
  case), which makes @{const A3_rel} hold trivially for any merge.
\<close>

definition ades_right_merge :: "'s merge" where
"ades_right_merge = (\<lambda>(m, z). z = mrg_right\<^sub>v m)"

lemma ades_right_merge_A0j: "A0j ades_right_merge"
  by (simp add: A0j_def ades_right_merge_def)

lemma ades_right_merge_A2j:
  "A2j ades_right_merge"
  by (simp add: A2j_def ades_right_merge_def)

lemma ades_right_merge_not_A3j: "\<not> A3j (ades_right_merge :: 's merge)"
  apply (simp add: A3j_def)
  apply (rule exI[where x="undefined"])
  apply (intro allI)
  subgoal for z
    by (intro exI[where x="{z}"]; simp add: ades_merge_image_def ades_right_merge_def)
  done

lemma ades_par_rel_A3_rel_counterexample:
  fixes FailP AnyQ :: "bool angelic_rel"
  defines "FailP \<equiv> (\<lambda>(s0, out). True \<in> achoices.ac\<^sub>v out)"
    and "AnyQ \<equiv> (\<lambda>(s0, out). achoices.ac\<^sub>v out \<noteq> {})"
  shows "(\<not> FailP) is A3_rel"
    and "\<not> ((\<not> ades_par_rel ades_right_merge FailP AnyQ) is A3_rel)"
proof -
  show "(\<not> FailP) is A3_rel"
    by (simp add: A3_rel_healthy' FailP_def;
        pred_auto; rule exI[where x=False]; simp)
  have comp: "\<And>s0 out.
      ades_par_rel ades_right_merge FailP AnyQ (s0, out) \<longleftrightarrow>
      achoices.ac\<^sub>v out \<noteq> {}"
  proof
    fix s0 :: "bool astate" and out :: "bool achoices"
    assume "ades_par_rel ades_right_merge FailP AnyQ (s0, out)"
    then obtain X Y where
      "True \<in> X" "Y \<noteq> {}" and
      img: "ades_merge_image ades_right_merge (astate.s\<^sub>v s0) X Y
            \<subseteq> achoices.ac\<^sub>v out"
      by (auto simp add: ades_par_rel_def FailP_def AnyQ_def)
    then show "achoices.ac\<^sub>v out \<noteq> {}"
      by (auto simp add: ades_merge_image_def ades_right_merge_def)
  next
    fix s0 :: "bool astate" and out :: "bool achoices"
    assume ne: "achoices.ac\<^sub>v out \<noteq> {}"
    then obtain z where z: "z \<in> achoices.ac\<^sub>v out" by blast
    have "ades_merge_image ades_right_merge (astate.s\<^sub>v s0)
        {True} {z} \<subseteq> achoices.ac\<^sub>v out"
      using z
      by (auto simp add: ades_merge_image_def ades_right_merge_def)
    then show "ades_par_rel ades_right_merge FailP AnyQ (s0, out)"
      by (auto simp add: ades_par_rel_def FailP_def AnyQ_def)
  qed
  show "\<not> ((\<not> ades_par_rel ades_right_merge FailP AnyQ) is A3_rel)"
    by (simp add: A3_rel_healthy' arel_not_applied comp)
qed

text \<open>
  A singleton that is never an exact merge image serves any number of
  compositions at once: an image contained in that singleton must be empty.
  The same witness state therefore discharges both failure disjuncts of the
  design-level precondition below.
\<close>

lemma ades_par_rel_conj_A3_rel_closure [closure]:
  fixes P1 Q1 P2 Q2 :: "'s angelic_rel" and j :: "'s merge"
  assumes "A3j j"
  shows "(\<not> ades_par_rel j P1 Q1 \<and> \<not> ades_par_rel j P2 Q2) is A3_rel"
proof -
  have shrink: "\<And>(s0 :: 's astate) z P Q.
      (\<forall>X Y. ades_merge_image j (astate.s\<^sub>v s0) X Y \<noteq> {z}) \<Longrightarrow>
      ades_par_rel j P Q (s0, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>) \<Longrightarrow>
      ades_par_rel j P Q (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>)"
    by (auto simp add: ades_par_rel_def subset_singleton_iff)
  have key: "\<And>s0 :: 's astate.
      \<not> ades_par_rel j P1 Q1 (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<and>
      \<not> ades_par_rel j P2 Q2 (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>) \<Longrightarrow>
      \<exists>z. \<not> ades_par_rel j P1 Q1 (s0, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>) \<and>
          \<not> ades_par_rel j P2 Q2 (s0, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>)"
    using assms unfolding A3j_def by (blast dest: shrink)
  have conj_eval: "\<And>s0 acr.
      (\<not> ades_par_rel j P1 Q1 \<and> \<not> ades_par_rel j P2 Q2) (s0, acr) =
      (\<not> ades_par_rel j P1 Q1 (s0, acr) \<and>
       \<not> ades_par_rel j P2 Q2 (s0, acr))"
    by pred_auto
  show ?thesis
    using key by (simp add: A3_rel_healthy' conj_eval)
qed

subsection \<open>Design-Level Assembly\<close>

text \<open>
  For H-healthy operands the parallel composition has an explicit relational
  design normal form.  The postcondition composes the two commitments, and
  a failure pairs a failure of one branch with an arbitrary observation of
  the other, all through the @{const ades_par_rel} choice-set composition.
  The @{const A2} and @{const A3} closure theorems then follow from the
  choice-set-level lemmas by design calculus.
\<close>

lemma ades_par_rdesign_form:
  fixes P1 P2 Q1 Q2 :: "'s angelic_rel" and j :: "'s merge"
  shows "((P1 \<turnstile>\<^sub>r P2) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q1 \<turnstile>\<^sub>r Q2)) =
    ((\<not> (ades_par_rel j (\<not> P1) (\<not> Q1 \<or> Q2) \<or>
         ades_par_rel j (\<not> P1 \<or> P2) (\<not> Q1)))
     \<turnstile>\<^sub>r ades_par_rel j (\<not> P1 \<or> P2) (\<not> Q1 \<or> Q2))"
  apply (rule ext)
  apply (rename_tac w)
  apply (case_tac w)
  apply (simp only: ades_par_eval)
  apply (simp add: ades_par_rel_def ades_merge_image_def)
  apply pred_auto
  done

theorem ades_par_rdesign:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q =
    ((\<not> (ades_par_rel j (\<not> pre\<^sub>D P) (\<not> pre\<^sub>D Q \<or> post\<^sub>D Q) \<or>
         ades_par_rel j (\<not> pre\<^sub>D P \<or> post\<^sub>D P) (\<not> pre\<^sub>D Q)))
     \<turnstile>\<^sub>r ades_par_rel j (\<not> pre\<^sub>D P \<or> post\<^sub>D P)
                         (\<not> pre\<^sub>D Q \<or> post\<^sub>D Q))"
  using ades_par_rdesign_form[of "pre\<^sub>D P" "post\<^sub>D P" j
      "pre\<^sub>D Q" "post\<^sub>D Q"]
  by (simp only: H1_H2_eq_rdesign[of P, symmetric] H1_H2_eq_rdesign[of Q, symmetric]
      Healthy_if[OF assms(1)] Healthy_if[OF assms(2)])

lemma ades_par_A2_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes PA2: "P is A2" and QA2: "Q is A2" and jf: "A2j j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
proof -
  let ?slice = "\<lambda>(R :: 's angelic_design) b0 b. \<lambda>(s0, out).
    R (\<lparr>ok\<^sub>v = b0, \<dots> = s0\<rparr>, \<lparr>ok\<^sub>v = b, \<dots> = out\<rparr>)"
  have slice: "?slice R b0 b is A2_rel" if "R is A2" for R b0 b
    using arg_cong[OF Healthy_if[OF that], where f="\<lambda>R. ?slice R b0 b"]
    by (simp add: Healthy_def' A2_def A2_rel_eq_expanded
        A2_rel_expanded_def fun_eq_iff)
  have comp: "ades_par_rel j (?slice P b0 bp) (?slice Q b0 bq) is A2_rel"
    for b0 bp bq
    by (rule ades_par_rel_A2_rel_closure[OF slice[OF PA2] slice[OF QA2] jf])
  have eval: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (s0, out) =
      (\<exists>bp bq. des_vars.ok\<^sub>v out = (bp \<and> bq) \<and>
        ades_par_rel j (?slice P (des_vars.ok\<^sub>v s0) bp)
          (?slice Q (des_vars.ok\<^sub>v s0) bq)
          (des_vars.more s0, des_vars.more out))" for s0 out
    by (cases s0; cases out;
        simp add: ades_par_eval ades_par_rel_def ades_merge_image_def;
        pred_auto; blast)
  show ?thesis
  proof (rule Healthy_intro, rule ext)
    fix w :: "'s astate des_vars_ext \<times> 's achoices des_vars_ext"
    obtain s0 out where w: "w = (s0, out)" by (cases w)
    let ?C = "\<lambda>bp bq. ades_par_rel j (?slice P (des_vars.ok\<^sub>v s0) bp)
      (?slice Q (des_vars.ok\<^sub>v s0) bq)"
    let ?out = "\<lambda>X. achoices.ac\<^sub>v_update (\<lambda>_. X) (des_vars.more out)"
    have expand: "?C bp bq (des_vars.more s0, des_vars.more out) =
      (?C bp bq (des_vars.more s0, ?out {}) \<or>
       (\<exists>y\<in>achoices.ac\<^sub>v (des_vars.more out).
          ?C bp bq (des_vars.more s0, ?out {y})))" for bp bq
      using fun_cong[OF Healthy_if[OF comp[of "des_vars.ok\<^sub>v s0" bp bq]],
        where x="(des_vars.more s0, des_vars.more out)"]
      by (simp add: A2_rel_eq_expanded A2_rel_expanded_def)
    show "A2 (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) w =
        (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) w"
      using expand
      by (cases out; simp add: w A2_def eval ex_bool_eq
          bex_disj_distrib conj_disj_distribL conj_disj_distribR disj_ac)
  qed
qed

text \<open>
  A2 changes only the final choice set, so the proof fixes the control flags
  and reuses @{thm ades_par_rel_A2_rel_closure}. Neither H-healthiness of the
  operands nor totality of the merge is required.
\<close>

(* If every prior state has a singleton that is never an exact merge image,
   the parallel composition of H-healthy operands is A3-healthy. *)
lemma ades_par_A3_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes PH: "P is \<^bold>H" and QH: "Q is \<^bold>H"
    and jm: "A3j j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
proof (rule H_A3_intro, rule ades_par_H_closure[OF PH QH])
  let ?D1 = "ades_par_rel j (\<not> pre\<^sub>D P) (\<not> pre\<^sub>D Q \<or> post\<^sub>D Q)"
  let ?D2 = "ades_par_rel j (\<not> pre\<^sub>D P \<or> post\<^sub>D P) (\<not> pre\<^sub>D Q)"
  have pre_eq: "pre\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) =
      (\<not> ?D1 \<and> \<not> ?D2)"
    apply (simp only: ades_par_rdesign[OF PH QH] rdesign_pre)
    by pred_auto
  show "pre\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3_rel"
    by (simp only: pre_eq ades_par_rel_conj_A3_rel_closure[OF jm])
qed

(* For a total merge, excluding some singleton image at each initial state
   is necessary and sufficient for A3 of every parallel of H-healthy operands. *)
lemma ades_par_A3_closure_iff_A3j:
  fixes j :: "'s merge"
  assumes total: "A0j j"
  shows "(\<forall>P Q. P is \<^bold>H \<longrightarrow> Q is \<^bold>H \<longrightarrow>
      (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3) \<longleftrightarrow> A3j j"
proof (rule iffI)
  assume closure: "\<forall>P Q. P is \<^bold>H \<longrightarrow> Q is \<^bold>H \<longrightarrow>
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  let ?E = "(\<lambda>(s0, out). achoices.ac\<^sub>v out \<noteq> {}) :: 's angelic_rel"
  let ?P = "((\<not> ?E) \<turnstile>\<^sub>r false)"
  let ?Q = "(true \<turnstile>\<^sub>r ?E)"
  let ?R = "?P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> ?Q"
  let ?C = "ades_par_rel j ?E ?E"
  have pre_eq: "pre\<^sub>D ?R = (\<not> ?C)"
    apply (simp only: ades_par_rdesign_form rdesign_pre)
    by pred_auto
  have R3: "?R is A3"
    by (rule closure[rule_format]; simp add: rdesign_is_H1_H2)
  have pre_healthy: "(\<not> ?C) is A3_rel"
    using arg_cong[OF Healthy_if[OF R3], where f="pre\<^sub>D"]
    by (simp add: A3_def Healthy_def' pre_eq)
  show "A3j j"
  proof (unfold A3j_def, intro allI)
    fix s :: 's
    have no_empty: "\<not> ?C (StateII s, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>)"
      using ades_merge_image_nonempty[OF total]
      by (auto simp add: ades_par_rel_def)
    obtain z where z: "\<not> ?C (StateII s, \<lparr>ac\<^sub>v = {z}, \<dots> = ()\<rparr>)"
      using pre_healthy no_empty
      by (auto simp add: A3_rel_healthy' arel_not_applied)
    have ne: "\<And>X Y. ades_merge_image j s X Y = {z} \<Longrightarrow> X \<noteq> {} \<and> Y \<noteq> {}"
      by (auto simp add: ades_merge_image_def)
    show "\<exists>z. \<forall>X Y. ades_merge_image j s X Y \<noteq> {z}"
      using z
      by (intro exI[where x=z];
          simp only: ades_par_rel_def StateII_def prod.case achoices.select_convs astate.select_convs;
          blast dest: ne)
  qed
next
  assume "A3j j"
  then show "\<forall>P Q. P is \<^bold>H \<longrightarrow> Q is \<^bold>H \<longrightarrow>
    (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
    using ades_par_A3_closure by blast
qed

subsection \<open>Normal Operands\<close>

text \<open>
  A normal design has a precondition independent of the output choice
  set, and that independence transfers through the choice-set
  composition.  The parallel composition of normal operands is therefore
  @{const A3}-healthy for an arbitrary merge, and it is itself normal.
\<close>

lemma ades_par_rel_left_indep:
  fixes F C :: "'s angelic_rel" and s0 :: "'s astate" and a b :: "'s achoices"
  assumes ind: "\<And>s0 a b. F (s0, a) = F (s0, b)"
  shows "ades_par_rel j F C (s0, a) = ades_par_rel j F C (s0, b)"
proof -
  have dir: "\<And>a b :: 's achoices.
      ades_par_rel j F C (s0, a) \<Longrightarrow> ades_par_rel j F C (s0, b)"
  proof -
    fix a b :: "'s achoices"
    assume "ades_par_rel j F C (s0, a)"
    then obtain X Y where FX: "F (s0, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>)" and
      CY: "C (s0, \<lparr>ac\<^sub>v = Y, \<dots> = ()\<rparr>)"
      by (auto simp add: ades_par_rel_def)
    have F0: "F (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>)"
      using FX ind by blast
    have "ades_merge_image j (astate.s\<^sub>v s0) {} Y \<subseteq> achoices.ac\<^sub>v b"
      by (simp add: ades_merge_image_def)
    then show "ades_par_rel j F C (s0, b)"
      using F0 CY by (auto simp add: ades_par_rel_def)
  qed
  show ?thesis using dir[of a b] dir[of b a] by blast
qed

lemma ades_par_rel_right_indep:
  fixes F C :: "'s angelic_rel" and s0 :: "'s astate" and a b :: "'s achoices"
  assumes ind: "\<And>s0 a b. F (s0, a) = F (s0, b)"
  shows "ades_par_rel j C F (s0, a) = ades_par_rel j C F (s0, b)"
proof -
  have dir: "\<And>a b :: 's achoices.
      ades_par_rel j C F (s0, a) \<Longrightarrow> ades_par_rel j C F (s0, b)"
  proof -
    fix a b :: "'s achoices"
    assume "ades_par_rel j C F (s0, a)"
    then obtain X Y where CX: "C (s0, \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>)" and
      FY: "F (s0, \<lparr>ac\<^sub>v = Y, \<dots> = ()\<rparr>)"
      by (auto simp add: ades_par_rel_def)
    have F0: "F (s0, \<lparr>ac\<^sub>v = {}, \<dots> = ()\<rparr>)"
      using FY ind by blast
    have "ades_merge_image j (astate.s\<^sub>v s0) X {} \<subseteq> achoices.ac\<^sub>v b"
      by (simp add: ades_merge_image_def)
    then show "ades_par_rel j C F (s0, b)"
      using F0 CX by (auto simp add: ades_par_rel_def)
  qed
  show ?thesis using dir[of a b] dir[of b a] by blast
qed

lemma ades_par_normal_preD_indep:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
    and s0 :: "'s astate" and a b :: "'s achoices"
  assumes PN: "P is \<^bold>N" and QN: "Q is \<^bold>N"
  shows "pre\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (s0, a) =
         pre\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (s0, b)"
proof -
  let ?D1 = "ades_par_rel j (\<not> pre\<^sub>D P) (\<not> pre\<^sub>D Q \<or> post\<^sub>D Q)"
  let ?D2 = "ades_par_rel j (\<not> pre\<^sub>D P \<or> post\<^sub>D P) (\<not> pre\<^sub>D Q)"
  have pre_eq: "pre\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (\<not> (?D1 \<or> ?D2))"
    by (simp only: ades_par_rdesign[OF N_implies_H[OF PN]
        N_implies_H[OF QN]] rdesign_pre)
  have D1i: "?D1 (s0, a) = ?D1 (s0, b)"
    by (rule ades_par_rel_left_indep)
       (simp add: arel_not_applied N_preD_indep[OF PN])
  have D2i: "?D2 (s0, a) = ?D2 (s0, b)"
    by (rule ades_par_rel_right_indep)
       (simp add: arel_not_applied N_preD_indep[OF QN])
  show ?thesis
    using D1i D2i
    by (simp only: pre_eq arel_not_applied; pred_auto)
qed

theorem ades_par_normal_A3_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes PN: "P is \<^bold>N" and QN: "Q is \<^bold>N"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  by (rule H_A3_intro,
      rule ades_par_H_closure[OF N_implies_H[OF PN] N_implies_H[OF QN]],
      rule arel_indep_A3_rel,
      rule ades_par_normal_preD_indep[OF PN QN])

theorem ades_par_normal_H3_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes PN: "P is \<^bold>N" and QN: "Q is \<^bold>N"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H3"
proof -
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  have R_eq: "?R = (pre\<^sub>D ?R \<turnstile>\<^sub>r post\<^sub>D ?R)"
    using ades_par_H_closure[OF N_implies_H[OF PN] N_implies_H[OF QN]]
      H1_H2_eq_rdesign[of ?R]
    by (simp add: Healthy_def')
  have "H3 (pre\<^sub>D ?R \<turnstile>\<^sub>r post\<^sub>D ?R) = (pre\<^sub>D ?R \<turnstile>\<^sub>r post\<^sub>D ?R)"
    by (rule H3_rdesign_pre, rule arel_indep_out_unrest,
        rule ades_par_normal_preD_indep[OF PN QN])
  then show ?thesis
    by (simp add: Healthy_def' R_eq[symmetric])
qed

theorem ades_par_N_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes PN: "P is \<^bold>N" and QN: "Q is \<^bold>N"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>N"
  by (rule H1_H3_intro,
      rule ades_par_H_closure[OF N_implies_H[OF PN] N_implies_H[OF QN]],
      rule arel_indep_out_unrest,
      rule ades_par_normal_preD_indep[OF PN QN])

subsection \<open>Algebraic Laws\<close>

theorem ades_par_comm:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P"
  by (rule par_by_merge_comm, rule merge_ades_up_swap[OF assms])

theorem ades_par_assoc:
  fixes P Q R :: "'s angelic_design" and j :: "'s merge"
  assumes "swap\<^sub>m ;; j = j" "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R =
         P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> R)"
  apply (rule ext)
  apply (case_tac x)
  apply (simp only: ades_par_eval')
  using merge_ades_up_assoc[OF assms]
  by blast

subsection \<open>Examples\<close>

text \<open>
  We reuse two merges from above: @{term skip\<^sub>m} returns the prior state,
  while @{const ades_right_merge} returns the right branch's result.
  Both satisfy @{const A0j} and @{const A2j}. By @{thm skip_merge_A3j},
  the first also satisfies @{const A3j} on a state space with at least two
  elements; the second does not, by @{thm ades_right_merge_not_A3j}.
\<close>

(* Nonempty branch choice sets merge to the singleton containing the prior state. *)
lemma ades_merge_image_skip:
  fixes s :: 's
  shows "ades_merge_image skip\<^sub>m s X Y =
    (if X = {} \<or> Y = {} then {} else {s})"
  by (auto simp: ades_merge_image_def skip_merge_eval)

(* A nonempty left choice set lets every right choice appear in the image. *)
lemma ades_merge_image_right:
  fixes s :: 's
  shows "ades_merge_image ades_right_merge s X Y = (if X = {} then {} else Y)"
  by (auto simp: ades_merge_image_def ades_right_merge_def)

(* With the same prior state and branch choices, the two policies give different images. *)
lemma ades_merge_image_example:
  "ades_merge_image skip\<^sub>m (0 :: nat) {1, 2} {3, 4} = {0}"
  "ades_merge_image ades_right_merge (0 :: nat) {1, 2} {3, 4} = {3, 4}"
  by (simp_all add: ades_merge_image_skip ades_merge_image_right)

(* An additional final choice is accepted by the upward lift, but not the exact lift. *)
lemma ades_right_merge_lifting_example:
  fixes s0 :: "nat astate des_vars_ext"
  defines "p \<equiv> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {1, 2}, \<dots> = ()\<rparr>"
    and "q \<equiv> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {3, 4}, \<dots> = ()\<rparr>"
    and "out \<equiv> \<lparr>ok\<^sub>v = True, ac\<^sub>v = {3, 4, 99}, \<dots> = ()\<rparr>"
  shows "ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(ades_right_merge) s0 p q out"
    and "\<not> ades_merge_eval M\<^sub>A\<^sub>D(ades_right_merge) s0 p q out"
proof -
  have unequal: "({3, 4, 99} :: nat set) \<noteq> {3, 4}"
    by (intro notI; drule arg_cong[where f="\<lambda>X. 99 \<in> X"]; simp)
  show "ades_merge_eval M\<^sub>A\<^sub>D\<^sup>\<up>(ades_right_merge) s0 p q out"
    and "\<not> ades_merge_eval M\<^sub>A\<^sub>D(ades_right_merge) s0 p q out"
    using unequal
    by (simp_all add: p_def q_def out_def merge_ades_up_def
        merge_ades_def ades_merge_image_right)
qed

(* The skip merge discards both assignments' results and restores the prior state. *)
lemma ades_par_skip_assign_example:
  fixes x y :: 's
  shows "(assigns_ades 1\<^sub>L (\<lambda>_. x) \<parallel>\<^sub>A\<^sub>D\<^bsub>skip\<^sub>m\<^esub>
      assigns_ades 1\<^sub>L (\<lambda>_. y)) = Skip_AD"
  apply (simp add: assigns_ades_def Skip_AD_def arel_to_ades_def
      ades_par_rdesign_form ades_par_rel_def assign_arel_def
      ades_merge_image_skip lens_defs fun_eq_iff)
  by pred_auto

(* The right merge retains the right assignment's result. *)
lemma ades_par_right_assign_example:
  fixes x y :: 's
  shows "(assigns_ades 1\<^sub>L (\<lambda>_. x) \<parallel>\<^sub>A\<^sub>D\<^bsub>ades_right_merge\<^esub>
      assigns_ades 1\<^sub>L (\<lambda>_. y)) = assigns_ades 1\<^sub>L (\<lambda>_. y)"
  apply (simp add: assigns_ades_def arel_to_ades_def
      ades_par_rdesign_form ades_par_rel_def assign_arel_def
      ades_merge_image_right lens_defs fun_eq_iff)
  by pred_auto

text \<open>
  Although @{const ades_right_merge} fails @{const A3j}, the assignment
  operands are normal: @{thm ades_par_normal_A3_closure} therefore still
  gives A3 closure for this example, without a merge restriction.
\<close>

end
