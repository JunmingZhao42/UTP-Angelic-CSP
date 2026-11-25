theory Sync_Algebra
  imports "RAD_Geometry_Probe.RAD_Probe" "AD_Geometry_Probe.AD_Geometry_Probe"
begin

section \<open>Distributing over both choices is impossible\<close>

text \<open>We would like parallel to distribute over both choices. Applied in the two
  orders to (x := 0 \<squnion> x := 1) \<parallel> (y := 0 \<sqinter> y := 1), the two laws give
  the join over u of the meets over v of (x,y) := (u,v), and the meet over v of the
  joins over u. These differ for angelic designs.\<close>

(* par (X u) (Y v) = C u v, \<squnion> distributes on the left and \<sqinter> on the right *)
lemma dist_interchange:
  fixes par :: "'a::lattice \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes pts: "\<And>u v. par (X u) (Y v) = C u v"
    and angL: "\<And>P P' Q. par (P \<squnion> P') Q = par P Q \<squnion> par P' Q"
    and demR: "\<And>P Q Q'. par P (Q \<sqinter> Q') = par P Q \<sqinter> par P Q'"
  shows "(C False False \<sqinter> C False True) \<squnion> (C True False \<sqinter> C True True) =
         (C False False \<squnion> C True False) \<sqinter> (C False True \<squnion> C True True)"
proof -
  have "par (X False \<squnion> X True) (Y False \<sqinter> Y True) =
        (C False False \<sqinter> C False True) \<squnion> (C True False \<sqinter> C True True)"
    by (subst angL) (simp only: demR pts)
  moreover have "par (X False \<squnion> X True) (Y False \<sqinter> Y True) =
        (C False False \<squnion> C True False) \<sqinter> (C False True \<squnion> C True True)"
    by (subst demR) (simp only: angL pts)
  ultimately show ?thesis by simp
qed

lemma assigns_ades_eval:
  "assigns_ades x e (ades_obs b s0 c X) \<longleftrightarrow> (b \<longrightarrow> c \<and> put\<^bsub>x\<^esub> s0 (e s0) \<in> X)"
  by (simp add: assigns_ades_def assign_arel_def arel_to_ades_def; pred_auto)

(* the whole state becomes v *)
abbreviation cst :: "'s \<Rightarrow> 's angelic_design" where
  "cst v \<equiv> assigns_ades 1\<^sub>L (\<lambda>_. v)"

lemma cst_eval: "cst v (ades_obs b s0 c X) \<longleftrightarrow> (b \<longrightarrow> c \<and> v \<in> X)"
  by (simp add: assigns_ades_eval id_lens_def)

lemma ades_dchoice_eval: "(P \<sqinter>\<^sub>A\<^sub>D Q) x \<longleftrightarrow> P x \<or> Q x"
  by (simp only: sup_fun_def sup_bool_def)

lemma ades_achoice_eval: "(P \<squnion>\<^sub>A\<^sub>D Q) x \<longleftrightarrow> P x \<and> Q x"
  by (simp only: inf_fun_def inf_bool_def)

(* the angel choosing first is weaker than the demon choosing first *)
lemma ades_angel_first_ne_demon_first:
  "(cst (False, False) \<sqinter>\<^sub>A\<^sub>D cst (False, True)) \<squnion>\<^sub>A\<^sub>D (cst (True, False) \<sqinter>\<^sub>A\<^sub>D cst (True, True)) \<noteq>
   (cst (False, False) \<squnion>\<^sub>A\<^sub>D cst (True, False)) \<sqinter>\<^sub>A\<^sub>D (cst (False, True) \<squnion>\<^sub>A\<^sub>D cst (True, True))"
  (is "?L \<noteq> ?R")
proof
  let ?x = "ades_obs True (False, False) True {(False, False), (True, True)}"
  have "?L ?x" by (simp only: ades_dchoice_eval ades_achoice_eval cst_eval) simp
  moreover have "\<not> ?R ?x" by (simp only: ades_dchoice_eval ades_achoice_eval cst_eval) simp
  moreover assume "?L = ?R"
  ultimately show False by simp
qed

(* x := u on the left and y := v on the right merge to (x,y) := (u,v) *)
lemma ades_par_jfd_assigns:
  "assigns_ades fst\<^sub>L (\<lambda>_. u) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> assigns_ades snd\<^sub>L (\<lambda>_. v) = cst (u, v)"
proof (rule ades_obs_ext)
  fix ok0 s0 ok' ac'
  show "(assigns_ades fst\<^sub>L (\<lambda>_. u) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> assigns_ades snd\<^sub>L (\<lambda>_. v)) (ades_obs ok0 s0 ok' ac') =
        cst (u, v) (ades_obs ok0 s0 ok' ac')"
  proof (cases ok0)
    case True
    show ?thesis
    proof
      assume "(assigns_ades fst\<^sub>L (\<lambda>_. u) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> assigns_ades snd\<^sub>L (\<lambda>_. v)) (ades_obs ok0 s0 ok' ac')"
      then show "cst (u, v) (ades_obs ok0 s0 ok' ac')"
        using True by (auto simp: ades_par_eval assigns_ades_eval lens_defs prod.case_eq_if)
          (metis fst_conv snd_conv)
    next
      assume "cst (u, v) (ades_obs ok0 s0 ok' ac')"
      then have r: "ok'" "(u, v) \<in> ac'"
        using True by (simp_all add: assigns_ades_eval lens_defs prod.case_eq_if)
      show "(assigns_ades fst\<^sub>L (\<lambda>_. u) \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> assigns_ades snd\<^sub>L (\<lambda>_. v)) (ades_obs ok0 s0 ok' ac')"
        unfolding ades_par_eval
        apply (rule exI[where x=True], rule exI[where x="{(u, snd s0)}"])
        apply (rule exI[where x=True], rule exI[where x="{(fst s0, v)}"])
        using r True by (simp add: assigns_ades_eval lens_defs prod.case_eq_if)
    qed
  next
    case False
    then show ?thesis by (simp add: ades_par_eval assigns_ades_eval)
  qed
qed

(* no operator that agrees with these assignments distributes over both choices *)
theorem no_par_dist_both:
  fixes par :: "(bool \<times> bool) angelic_design \<Rightarrow> (bool \<times> bool) angelic_design \<Rightarrow>
                (bool \<times> bool) angelic_design"
  assumes pts: "\<And>u v. par (assigns_ades fst\<^sub>L (\<lambda>_. u)) (assigns_ades snd\<^sub>L (\<lambda>_. v)) = cst (u, v)"
    and angL: "\<And>P P' Q. par (P \<squnion>\<^sub>A\<^sub>D P') Q = par P Q \<squnion>\<^sub>A\<^sub>D par P' Q"
    and demR: "\<And>P Q Q'. par P (Q \<sqinter>\<^sub>A\<^sub>D Q') = par P Q \<sqinter>\<^sub>A\<^sub>D par P Q'"
  shows False
  using dist_interchange[where par=par and X="\<lambda>u. assigns_ades fst\<^sub>L (\<lambda>_. u)"
      and Y="\<lambda>v. assigns_ades snd\<^sub>L (\<lambda>_. v)" and C="\<lambda>u v. cst (u, v)", OF pts angL demR]
    ades_angel_first_ne_demon_first
  by simp

(* AD parallel distributes over \<sqinter>, so it cannot distribute over \<squnion> *)
corollary ades_par_jfd_not_angelic_dist:
  "\<not> (\<forall>P P' Q :: (bool \<times> bool) angelic_design.
        (P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q = (P \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q))"
proof
  assume angL: "\<forall>P P' Q :: (bool \<times> bool) angelic_design.
        (P \<squnion>\<^sub>A\<^sub>D P') \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q = (P \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q) \<squnion>\<^sub>A\<^sub>D (P' \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q)"
  have demR: "P \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> (Q \<sqinter>\<^sub>A\<^sub>D Q') = (P \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q) \<sqinter>\<^sub>A\<^sub>D (P \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q')"
    for P Q Q' :: "(bool \<times> bool) angelic_design"
    by (simp only: ades_par_def angelic_design_demonic par_by_merge_disj_distl)
  show False
    by (rule no_par_dist_both[where par="\<lambda>P Q. P \<parallel>\<^sub>A\<^sub>D\<^bsub>jfd\<^esub> Q"])
       (use ades_par_jfd_assigns angL demR in auto)
qed


section \<open>Strong cooperation needs a choice that is not a join\<close>

text \<open>We would like a\<rightarrow>Skip \<parallel> (a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip) = a\<rightarrow>Skip, as with external choice.
  Angelic choice is a join, so b\<rightarrow>Skip \<sqsubseteq> a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip, and a monotone parallel gives
  a\<rightarrow>Skip \<parallel> b\<rightarrow>Skip \<sqsubseteq> a\<rightarrow>Skip \<parallel> (a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip). The left side never ends after a.\<close>

lemma rad_achoice_eval: "(P \<squnion>\<^sub>R\<^sub>A\<^sub>D Q) x \<longleftrightarrow> P x \<and> Q x"
  by (simp only: inf_fun_def inf_bool_def)

(* a \<rightarrow> Skip \<parallel> b \<rightarrow> Skip cannot terminate after a *)
lemma rad_sync_ab_not_done:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
  shows "\<not> (PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) (ades_obs True s0 True {done_a a s0})"
proof
  assume "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) (ades_obs True s0 True {done_a a s0})"
  then obtain okL acL okR acR
    where L: "PrefixSkip_RAD a (ades_obs True s0 okL acL)"
      and R: "PrefixSkip_RAD b (ades_obs True s0 okR acR)"
      and M: "\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>{done_a a s0}. merge_eval (merge_rdes jsync)
         \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr> \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = s'\<rparr>"
    unfolding rad_par_obs by blast
  from L obtain yL where yL: "yL \<in> acL" "pobs a s0 yL" and okL: okL
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  from R obtain yR where yR: "yR \<in> acR" "pobs b s0 yR" and okR: okR
    by (auto simp: PrefixSkip_RAD_obs[OF s0])
  have "merge_eval (merge_rdes jsync) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = yL\<rparr>
      \<lparr>ok\<^sub>v = True, \<dots> = yR\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = done_a a s0\<rparr>"
    using bspec[OF bspec[OF M yL(1)] yR(1)] okL okR by simp
  then have "rad_tr\<^sub>v (done_a a s0) = rad_tr\<^sub>v s0"
    by (rule sync_pair_stuck[OF s0 ab yL(2) yR(2)])
  then show False by simp
qed

(* a started, non-waiting prior *)
abbreviation s_start :: "('e list, 'e) rad_state" where
  "s_start \<equiv> rea_vars_ext False [] {}"

(* no monotone parallel that agrees with RAD parallel on a\<rightarrow>Skip and b\<rightarrow>Skip
   turns a\<rightarrow>Skip \<parallel> (a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip) into a\<rightarrow>Skip *)
theorem sync_no_strong_cooperation:
  fixes a b :: 'e and par :: "('e list, 'e) reactive_angelic_design \<Rightarrow> ('e list, 'e) reactive_angelic_design \<Rightarrow>
                ('e list, 'e) reactive_angelic_design"
  assumes ab: "a \<noteq> b"
    and mono: "\<And>Q Q'. Q \<sqsubseteq> Q' \<Longrightarrow> par (PrefixSkip_RAD a) Q \<sqsubseteq> par (PrefixSkip_RAD a) Q'"
    and agree: "par (PrefixSkip_RAD a) (PrefixSkip_RAD b) =
                PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b"
  shows "par (PrefixSkip_RAD a) (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) \<noteq> PrefixSkip_RAD a"
proof
  assume eq: "par (PrefixSkip_RAD a) (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) = PrefixSkip_RAD a"
  have "PrefixSkip_RAD b \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
    by (simp only: ref_by_pred_is_leq) (rule inf_le2)
  from mono[OF this]
  have ref: "PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b \<sqsubseteq> PrefixSkip_RAD a"
    by (simp only: agree eq)
  have w: "\<not> rad_wait\<^sub>v (s_start :: ('e list, 'e) rad_state)" by simp
  have "PrefixSkip_RAD a (ades_obs True s_start True {done_a a s_start})"
    using pobs_done[of a s_start] by (simp add: PrefixSkip_RAD_obs[OF w])
  from ref[unfolded pred_refine_iff, rule_format, OF this] rad_sync_ab_not_done[OF w ab]
  show False by contradiction
qed


section \<open>The lift does not distribute over angelic choice\<close>

text \<open>We want to compare a\<rightarrow>Skip \<parallel> (a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip) with the distributed form
  (a\<rightarrow>Skip \<parallel> a\<rightarrow>Skip) \<squnion> (a\<rightarrow>Skip \<parallel> b\<rightarrow>Skip). The lift is above it, and strictly:
  the distributed form can end after a.\<close>

(* (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R) *)
lemma rad_par_angelic_subdist:
  "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> R) \<sqsubseteq> P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> (Q \<squnion>\<^sub>R\<^sub>A\<^sub>D R)"
  by (simp only: RAD_angelic_choice par_by_merge_conj_subdistl)

(* waiting at the start, refusing a and b *)
abbreviation stop_ab :: "'e \<Rightarrow> 'e \<Rightarrow> ('e list, 'e) rad_state \<Rightarrow> ('e list, 'e) rad_state" where
  "stop_ab a b s0 \<equiv> rea_vars_ext True (rad_tr\<^sub>v s0) {a, b}"

(* waiting at the start, refusing only e *)
abbreviation wait_ref :: "'e \<Rightarrow> ('e list, 'e) rad_state \<Rightarrow> ('e list, 'e) rad_state" where
  "wait_ref e s0 \<equiv> rea_vars_ext True (rad_tr\<^sub>v s0) {e}"

lemma rad_sync_aa_obs:
  assumes s0: "\<not> rad_wait\<^sub>v s0"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a)
           (ades_obs True s0 True {done_a a s0, stop_ab a b s0})"
  unfolding rad_par_obs
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
  using pobs_done[of a s0] s0
  by (simp add: PrefixSkip_RAD_obs merge_rdes_started minus_list_def)

lemma rad_sync_ab_obs:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b)
           (ades_obs True s0 True {done_a a s0, stop_ab a b s0})"
  unfolding rad_par_obs
  apply (rule exI[where x=True], rule exI[where x="{wait_ref b s0}"])
  apply (rule exI[where x=True], rule exI[where x="{wait_ref a s0}"])
  using s0 ab
  by (simp add: PrefixSkip_RAD_obs[OF s0] pobs_def merge_rdes_started minus_list_def insert_commute)

theorem rad_par_not_angelic_dist:
  fixes a b :: 'e
  assumes ab: "a \<noteq> b"
  shows "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
           (PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) \<noteq>
         PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)"
proof
  assume eq: "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
           (PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b) =
         PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)"
  let ?Z = "{done_a a s_start, stop_ab a b s_start} :: ('e list, 'e) rad_state set"
  have w: "\<not> rad_wait\<^sub>v (s_start :: ('e list, 'e) rad_state)" by simp
  have "((PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD a) \<squnion>\<^sub>R\<^sub>A\<^sub>D
           (PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> PrefixSkip_RAD b)) (ades_obs True s_start True ?Z)"
    using rad_sync_aa_obs[OF w, of a b] rad_sync_ab_obs[OF w ab]
    by (simp add: rad_achoice_eval)
  then have "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
      (ades_obs True s_start True ?Z)"
    by (simp only: eq)
  then show False by (simp add: rad_sync_angelic_eval[OF w ab])
qed


section \<open>The least monotone parallel\<close>

text \<open>We want the parallel that agrees with RAD parallel on CSP processes (A2) and
  adds nothing else: the join of g \<parallel> h over CSP processes g \<sqsubseteq> P and h \<sqsubseteq> Q.\<close>

(* P \<parallel>F[j] Q = \<Squnion> {g \<parallel>RAD[j] h | g \<sqsubseteq> P, h \<sqsubseteq> Q, g and h RAD and A2} *)
definition rad_par_F ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t \<times> 'e set) merge \<Rightarrow>
   ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design" where
  "rad_par_F P j Q = (\<Squnion> {g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h | g h.
     (g is RAD) \<and> (g is A2) \<and> (h is RAD) \<and> (h is A2) \<and> g \<sqsubseteq> P \<and> h \<sqsubseteq> Q})"

lemma rad_par_F_eval:
  "rad_par_F P j Q x \<longleftrightarrow>
    (\<forall>g h. (g is RAD) \<longrightarrow> (g is A2) \<longrightarrow> (h is RAD) \<longrightarrow> (h is A2) \<longrightarrow>
       g \<sqsubseteq> P \<longrightarrow> h \<sqsubseteq> Q \<longrightarrow>
       (g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h) x)"
  unfolding rad_par_F_def Inf_fun_def by auto

lemma rad_par_mono2:
  "g \<sqsubseteq> P \<Longrightarrow> h \<sqsubseteq> Q \<Longrightarrow> g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h \<sqsubseteq> P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  by (rule ref_by_trans[OF par_by_merge_mono_left par_by_merge_mono_right])

(* on CSP processes it is RAD parallel *)
lemma rad_par_F_A2:
  assumes "P is RAD" "P is A2" "Q is RAD" "Q is A2"
  shows "rad_par_F P j Q = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
proof (rule ext)
  fix x
  show "rad_par_F P j Q x = (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) x"
  proof
    assume F: "rad_par_F P j Q x"
    have "P \<sqsubseteq> P" "Q \<sqsubseteq> Q" by (simp_all only: ref_by_pred_is_leq order_refl)
    with F assms show "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) x"
      unfolding rad_par_F_eval by blast
  next
    assume PQ: "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) x"
    show "rad_par_F P j Q x"
      unfolding rad_par_F_eval
    proof (intro allI impI)
      fix g h assume "g \<sqsubseteq> P" "h \<sqsubseteq> Q"
      from rad_par_mono2[OF this, unfolded pred_refine_iff, rule_format, OF PQ]
      show "(g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h) x" .
    qed
  qed
qed

lemma rad_par_F_mono:
  assumes "P \<sqsubseteq> P'" "Q \<sqsubseteq> Q'"
  shows "rad_par_F P j Q \<sqsubseteq> rad_par_F P' j Q'"
  unfolding pred_refine_iff[of "rad_par_F P j Q"]
proof (intro allI impI)
  fix x assume F: "rad_par_F P' j Q' x"
  show "rad_par_F P j Q x"
    unfolding rad_par_F_eval
  proof (intro allI impI)
    fix g h
    assume "g is RAD" "g is A2" "h is RAD" "h is A2" "g \<sqsubseteq> P" "h \<sqsubseteq> Q"
    moreover have "g \<sqsubseteq> P'" "h \<sqsubseteq> Q'"
      using ref_by_trans[OF \<open>g \<sqsubseteq> P\<close> assms(1)] ref_by_trans[OF \<open>h \<sqsubseteq> Q\<close> assms(2)] .
    ultimately show "(g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h) x"
      using F unfolding rad_par_F_eval by blast
  qed
qed

(* it lies below every monotone parallel that agrees on CSP processes *)
lemma rad_par_F_least:
  assumes mono: "\<And>P P' Q Q'. P \<sqsubseteq> P' \<Longrightarrow> Q \<sqsubseteq> Q' \<Longrightarrow> par P Q \<sqsubseteq> par P' Q'"
    and agree: "\<And>g h. g is RAD \<Longrightarrow> g is A2 \<Longrightarrow> h is RAD \<Longrightarrow> h is A2 \<Longrightarrow>
                  par g h = g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h"
  shows "rad_par_F P j Q \<sqsubseteq> par P Q"
  unfolding pred_refine_iff[of "rad_par_F P j Q"] rad_par_F_eval
proof (intro allI impI)
  fix x g h
  assume x: "par P Q x" and gh: "g is RAD" "g is A2" "h is RAD" "h is A2"
    and le: "g \<sqsubseteq> P" "h \<sqsubseteq> Q"
  have "g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h \<sqsubseteq> par P Q"
    using mono[OF le] by (simp only: agree[OF gh])
  from this[unfolded pred_refine_iff, rule_format, OF x]
  show "(g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> h) x" .
qed

lemma rad_par_F_below: "rad_par_F P j Q \<sqsubseteq> P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  by (rule rad_par_F_least[where par="\<lambda>P Q. P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"]) (simp_all add: rad_par_mono2)

(* a CSP process below a\<rightarrow>Skip \<squnion> b\<rightarrow>Skip offers one of the two singletons below *)
lemma A2_below_angelic_pick:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
    and h: "h is RAD" "h is A2" "h \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
  shows "h (ades_obs True s0 True {done_a a s0}) \<or> h (ades_obs True s0 True {wait_ref a s0})"
proof -
  have "(PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)
          (ades_obs True s0 True {done_a a s0, wait_ref a s0})"
    using pobs_done[of a s0] ab
    by (simp add: rad_achoice_eval
        PrefixSkip_RAD_obs[OF s0] pobs_def)
  from h(3)[unfolded pred_refine_iff, rule_format, OF this]
  have hZ: "h (ades_obs True s0 True {done_a a s0, wait_ref a s0})" .
  have pbmh: "h is PBMH_ades" by (rule RAD_is_PBMH_ades[OF h(1)])
  have up: "h (ades_obs True s0 True {}) \<Longrightarrow> h (ades_obs True s0 True {done_a a s0})"
    using PBMH_ades_obs[of h True s0 True "{done_a a s0}"]
    by (simp only: Healthy_if[OF pbmh]; blast)
  have a2: "h (ades_obs True s0 True {done_a a s0, wait_ref a s0}) \<longleftrightarrow>
      h (ades_obs True s0 True {}) \<or>
      (\<exists>z\<in>{done_a a s0, wait_ref a s0}. h (ades_obs True s0 True {z}))"
    using A2_obs[of h True s0 True "{done_a a s0, wait_ref a s0}"]
    by (simp only: Healthy_if[OF h(2)])
  from hZ a2 up show ?thesis by auto
qed

(* the least monotone parallel can end after a, where the lift cannot *)
lemma rad_par_F_sync_obs:
  assumes s0: "\<not> rad_wait\<^sub>v s0" and ab: "a \<noteq> b"
  shows "rad_par_F (PrefixSkip_RAD a) jsync (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)
           (ades_obs True s0 True {done_a a s0, stop_ab a b s0})"
  unfolding rad_par_F_eval
proof (intro allI impI)
  fix g h
  assume g: "g is RAD" "g is A2" "g \<sqsubseteq> PrefixSkip_RAD a"
    and h: "h is RAD" "h is A2" "h \<sqsubseteq> PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
  have "PrefixSkip_RAD a (ades_obs True s0 True {done_a a s0})"
    using pobs_done[of a s0] by (simp add: PrefixSkip_RAD_obs[OF s0])
  from g(3)[unfolded pred_refine_iff, rule_format, OF this]
  have g1: "g (ades_obs True s0 True {done_a a s0})" .
  have "PrefixSkip_RAD a (ades_obs True s0 True {wait_ref b s0})"
    using ab by (simp add: PrefixSkip_RAD_obs[OF s0] pobs_def)
  from g(3)[unfolded pred_refine_iff, rule_format, OF this]
  have g2: "g (ades_obs True s0 True {wait_ref b s0})" .
  from A2_below_angelic_pick[OF s0 ab h]
  show "(g \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> h) (ades_obs True s0 True {done_a a s0, stop_ab a b s0})"
  proof
    assume h1: "h (ades_obs True s0 True {done_a a s0})"
    show ?thesis
      unfolding rad_par_obs
      apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
      apply (rule exI[where x=True], rule exI[where x="{done_a a s0}"])
      using g1 h1 s0 by (simp add: merge_rdes_started minus_list_def)
  next
    assume h2: "h (ades_obs True s0 True {wait_ref a s0})"
    show ?thesis
      unfolding rad_par_obs
      apply (rule exI[where x=True], rule exI[where x="{wait_ref b s0}"])
      apply (rule exI[where x=True], rule exI[where x="{wait_ref a s0}"])
      using g2 h2 s0 by (simp add: merge_rdes_started minus_list_def insert_commute)
  qed
qed

theorem rad_par_F_cooperates:
  fixes a b :: 'e
  assumes ab: "a \<noteq> b"
  shows "rad_par_F (PrefixSkip_RAD a) jsync (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) \<noteq>
         PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)"
proof
  assume eq: "rad_par_F (PrefixSkip_RAD a) jsync (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b) =
         PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b)"
  have w: "\<not> rad_wait\<^sub>v (s_start :: ('e list, 'e) rad_state)" by simp
  from rad_par_F_sync_obs[OF w ab]
  have "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
      (ades_obs True s_start True {done_a a s_start, stop_ab a b s_start})"
    by (simp only: eq)
  then show False by (simp add: rad_sync_angelic_eval[OF w ab])
qed

end
