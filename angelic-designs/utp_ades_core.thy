section \<open>Angelic Design Core\<close>

theory utp_ades_core
  imports "UTP-Designs.utp_designs"
begin

subsection \<open>Alphabet (Paper Definition 16)\<close>

text \<open>
  Angelic designs package ordinary program variables into an initial state @{term s}, 
  and record possible final states as a set @{term ac}.
\<close>

alphabet 's astate =
  s :: 's

alphabet 's achoices =
  ac :: "'s set"

notation achoices.more\<^sub>L ("\<^bold>v\<^sub>A")

syntax
  "_svid_ades_alpha" :: "svid" ("\<^bold>v\<^sub>A")

translations
  "_svid_ades_alpha" => "CONST achoices.more\<^sub>L"

(* some shortcut to modify the angelic design fields *)
lemma astate_s_v_put [simp]:
  "astate.s\<^sub>v (put\<^bsub>s\<^esub> st v) = v"
  by (simp add: astate.s_def)

lemma achoices_ac_v_put [simp]:
  "achoices.ac\<^sub>v (put\<^bsub>ac\<^esub> c cs) = cs"
  by (simp add: achoices.ac_def)

(* Paper Definition 25. *)
(* Package the ordinary variables as the state observed by an angelic predicate. *)
definition StateII :: "'s \<Rightarrow> 's astate" where
[pred]: "StateII st = \<lparr>s\<^sub>v = st, \<dots> = ()\<rparr>"

type_synonym ('s, '\<alpha>) astate_ext       = "('s, '\<alpha>) astate_scheme"
type_synonym ('s, '\<alpha>) achoices_ext     = "('s, '\<alpha>) achoices_scheme"
type_synonym ('s, '\<alpha>, '\<beta>) angelic_rel_ext =
  "(('s, '\<alpha>) astate_ext, ('s, '\<beta>) achoices_ext) urel"
type_synonym ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext =
  "(('s, '\<alpha>) astate_ext, ('s, '\<beta>) achoices_ext) des_rel"

type_synonym 's angelic_rel = "('s, unit, unit) angelic_rel_ext"
type_synonym 's angelic_design = "('s, unit, unit) angelic_design_rel_ext"

abbreviation ades_started_input :: "'s astate \<Rightarrow> 's astate des_vars_ext" where
  "ades_started_input s0 \<equiv> \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>"

abbreviation ades_output :: "bool \<Rightarrow> 's set \<Rightarrow> 's achoices des_vars_ext" where
  "ades_output b X \<equiv>
    \<lparr>ok\<^sub>v = b, \<dots> = \<lparr>ac\<^sub>v = X, \<dots> = ()\<rparr>\<rparr>"

lemma choices_ex:
  "(\<exists>p :: 's achoices des_vars_ext. F p) \<longleftrightarrow>
   (\<exists>b X. F (ades_output b X))"
  by pred_auto

abbreviation ades_obs ::
  "bool \<Rightarrow> 's \<Rightarrow> bool \<Rightarrow> 's set \<Rightarrow>
   's astate des_vars_ext \<times> 's achoices des_vars_ext"
where
  "ades_obs b s0 c X \<equiv>
   (\<lparr>ok\<^sub>v = b, s\<^sub>v = s0, \<dots> = ()\<rparr>,
    \<lparr>ok\<^sub>v = c, ac\<^sub>v = X, \<dots> = ()\<rparr>)"

lemma ades_obs_ext:
  fixes P Q :: "'s angelic_design"
  assumes "\<And>b s0 c X. P (ades_obs b s0 c X) = Q (ades_obs b s0 c X)"
  shows "P = Q"
  using assms by (simp add: fun_eq_iff; pred_auto)

abbreviation arel_state_subst ::
  "('s, '\<alpha>) astate_ext subst \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_rel_ext"
where
  "arel_state_subst st_subst P \<equiv> (st_subst \<up>\<^sub>s \<^bold>v\<^sup><) \<dagger> P"

abbreviation ades_state_subst ::
  "('s, '\<alpha>) astate_ext subst \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext \<Rightarrow>
   ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext"
where
  "ades_state_subst st_subst P \<equiv> (st_subst \<up>\<^sub>s \<^bold>v\<^sub>D\<^sup><) \<dagger> P"

definition arel_to_ades ::
  "('s, '\<alpha>, '\<beta>) angelic_rel_ext \<Rightarrow> ('s, '\<alpha>, '\<beta>) angelic_design_rel_ext"
where
[pred]: "arel_to_ades P = (true \<turnstile>\<^sub>r P)"

text \<open>
  For example, @{term "arel_to_ades (($s\<^sup>< \<in> $ac\<^sup>>)\<^sub>e) :: 's angelic_design"}.
\<close>

subsection \<open>Design support laws\<close>

(* Negation reverses refinement.  Stated on opaque predicates: at the
   point of use the arguments are healthiness images, which pred_auto
   would otherwise unfold. *)
lemma not_refine:
  fixes P Q :: "'s pred"
  assumes "P \<sqsubseteq> Q"
  shows "(\<not> Q) \<sqsubseteq> (\<not> P)"
  using assms by pred_auto

lemma H1_obs:
  "H1 P (ades_obs b s0 c X) \<longleftrightarrow>
    (\<not> b \<or> P (ades_obs b s0 c X))"
  by (simp add: H1_def; pred_auto)

lemma H2_obs:
  "H2 P (ades_obs b s0 c X) \<longleftrightarrow>
    (P (ades_obs b s0 False X) \<or> (c \<and> P (ades_obs b s0 True X)))"
  by (simp add: H2_split; pred_auto)

lemma H1_healthy_obs_iff:
  fixes P :: "'s angelic_design"
  shows "P is H1 \<longleftrightarrow> (\<forall>s0 c X. P (ades_obs False s0 c X))"
proof
  assume h: "P is H1"
  show "\<forall>s0 c X. P (ades_obs False s0 c X)"
    using H1_obs[of P False] by (simp only: Healthy_if[OF h]; simp)
next
  assume h: "\<forall>s0 c X. P (ades_obs False s0 c X)"
  show "P is H1"
  proof (rule Healthy_intro, rule ades_obs_ext)
    fix b s0 c X
    show "H1 P (ades_obs b s0 c X) = P (ades_obs b s0 c X)"
      using h by (cases b; auto simp: H1_obs)
  qed
qed

subsection \<open>PBMH\<close>

(* ac \<subseteq> ac' \<and> v' = v. *)
definition pbmh_step :: "(('s, '\<alpha>) achoices_scheme, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "pbmh_step = (($ac\<^sup>< \<subseteq> $ac\<^sup>>) \<and> $\<^bold>v\<^sub>A\<^sup>> = $\<^bold>v\<^sub>A\<^sup><)\<^sub>e"

(* Paper Definition 15. *)
definition PBMH :: "('\<beta>, ('s, '\<alpha>) achoices_scheme) urel \<Rightarrow> ('\<beta>, ('s, '\<alpha>) achoices_scheme) urel" where
[pred]: "PBMH P = (P ;; pbmh_step)"


subsection \<open>Predicate Support Laws\<close>

lemma arel_not_not:
  "(\<not> (\<not> R)) = (R :: 's angelic_rel)"
  by pred_auto

lemma arel_not_applied:
  "(\<not> (R :: 's angelic_rel)) (s0, acr) \<longleftrightarrow> \<not> R (s0, acr)"
  by pred_auto

lemma arel_indep_out_unrest:
  fixes R :: "'s angelic_rel"
  assumes ind: "\<And>s0 a b. R (s0, a) = R (s0, b)"
  shows "out\<alpha> \<sharp> R"
  apply (simp add: out\<alpha>_def unrest_lens)
  apply (intro allI)
  subgoal for w v
    by (cases w; simp add: lens_defs ind)
  done

(* Conjunction absorption facts used to shape normal forms in the
   angelic process theories. *)

lemma conj_extra_absorb:
  fixes R X Y Z :: "'s angelic_design"
  assumes "(R \<and> (Y \<and> Z)) = (Y \<and> Z)"
  shows "(R \<and> ((X \<and> Y) \<and> Z)) = ((X \<and> Y) \<and> Z)"
  using assms by pred_auto

lemma neg_conj_absorb_false:
  fixes X Y :: "'s angelic_design"
  assumes "(X \<and> Y) = Y"
  shows "((\<not> X) \<and> Y) = false"
  using assms by pred_auto

(* A conjunct is absorbed when the remaining conjuncts contradict its
   negation. *)
lemma conj_absorb_by_agree:
  fixes X A B :: "'s angelic_design"
  assumes "((\<not> X) \<and> B) = ((\<not> X) \<and> A)"
  shows "(X \<and> ((\<not> A) \<and> B)) = ((\<not> A) \<and> B)"
  using assms by pred_auto

lemma achoices_ac_update_self [simp]:
  "achoices.ac\<^sub>v_update (\<lambda>_. achoices.ac\<^sub>v r) r = r"
  by (cases r) simp

lemma idem_fix_extract:
  assumes idem: "\<And>y. F (F y) = F y" and e: "F (G x) = x"
  shows "F x = x"
proof -
  have "F x = F (F (G x))" by (simp only: e)
  also have "... = F (G x)" by (rule idem)
  also have "... = x" by (rule e)
  finally show ?thesis .
qed

end
