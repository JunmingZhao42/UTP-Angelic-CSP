section \<open>Angelic Design Parallel-by-Merge\<close>

theory utp_ades_parallel
  imports utp_ades_designs
begin

subsection \<open>Choice-set Merge\<close>

type_synonym 's ades_merge_rel =
  "((('s astate des_vars_scheme, 's achoices des_vars_scheme,
      's achoices des_vars_scheme) mrg),
    's achoices des_vars_scheme) urel"

definition ades_merge_total :: "'s merge \<Rightarrow> bool" where
"ades_merge_total j \<longleftrightarrow>
  (\<forall>s p q. \<exists>z.
    j (\<lparr>mrg_prior\<^sub>v = s,
        mrg_left\<^sub>v = p,
        mrg_right\<^sub>v = q,
        \<dots> = ()\<rparr>, z))"

text \<open>
  This is the raw angelic-design lifting of a state-level merge.  The
  combined choice set contains every state obtained by merging one choice
  from each branch, and the combined computation terminates exactly when
  both branches terminate.

  The equality on the combined choice set gives the exact, unnormalised
  semantics.  The upward-closed lifting below is its @{const PBMH_ades}
  normal form and is used for the public angelic-design operator.
\<close>

definition merge_ades :: "'s merge \<Rightarrow> 's ades_merge_rel" ("M\<^sub>A\<^sub>D'(_')") where
"merge_ades j = (\<lambda> (m, out).
  des_vars.ok\<^sub>v out =
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
     des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  achoices.ac\<^sub>v (des_vars.more out) =
    {z. \<exists> p \<in> achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)).
        \<exists> q \<in> achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m)).
          j (\<lparr>mrg_prior\<^sub>v =
                astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m)),
              mrg_left\<^sub>v = p,
              mrg_right\<^sub>v = q,
              \<dots> = ()\<rparr>, z)})"

definition merge_ades_up :: "'s merge \<Rightarrow> 's ades_merge_rel"
  ("M\<^sub>A\<^sub>D\<^sup>\<up>'(_')") where
"merge_ades_up j = (\<lambda> (m, out).
  des_vars.ok\<^sub>v out =
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
     des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
  {z. \<exists> p \<in> achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m)).
      \<exists> q \<in> achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m)).
        j (\<lparr>mrg_prior\<^sub>v =
              astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m)),
            mrg_left\<^sub>v = p,
            mrg_right\<^sub>v = q,
            \<dots> = ()\<rparr>, z)}
    \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"

lemma merge_ades_swap:
  fixes j :: "'s merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; M\<^sub>A\<^sub>D(j) = M\<^sub>A\<^sub>D(j)"
  using assms
  by (simp add: merge_ades_def fun_eq_iff; pred_auto; blast)

lemma merge_ades_up_swap:
  fixes j :: "'s merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "swap\<^sub>m ;; M\<^sub>A\<^sub>D\<^sup>\<up>(j) = M\<^sub>A\<^sub>D\<^sup>\<up>(j)"
  using assms
  by (simp add: merge_ades_up_def fun_eq_iff; pred_auto; blast)

lemma PBMH_ades_par_by_merge_raw:
  "PBMH_ades (P \<parallel>\<^bsub>M\<^sub>A\<^sub>D(j)\<^esub> Q) =
   P \<parallel>\<^bsub>M\<^sub>A\<^sub>D\<^sup>\<up>(j)\<^esub> Q"
  by (simp add: PBMH_ades_def PBMH_def pbmh_step_def
      par_by_merge_def par_sep_def merge_ades_def merge_ades_up_def
      fun_eq_iff; pred_auto; blast)

subsection \<open>Parallel Composition\<close>

abbreviation ades_par_by_merge ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow>
   's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<equiv>
   P \<parallel>\<^bsub>M\<^sub>A\<^sub>D\<^sup>\<up>(j)\<^esub> Q"

lemma ades_par_by_merge_eval:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (s0, out) \<longleftrightarrow>
   (\<exists>p q. P (s0, p) \<and> Q (s0, q) \<and>
     des_vars.ok\<^sub>v out =
       (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q) \<and>
     {z. \<exists>x \<in> achoices.ac\<^sub>v (des_vars.more p).
         \<exists>y \<in> achoices.ac\<^sub>v (des_vars.more q).
           j (\<lparr>mrg_prior\<^sub>v = astate.s\<^sub>v (des_vars.more s0),
               mrg_left\<^sub>v = x,
               mrg_right\<^sub>v = y,
               \<dots> = ()\<rparr>, z)}
       \<subseteq> achoices.ac\<^sub>v (des_vars.more out))"
  by (cases s0; cases out;
      simp add: par_by_merge_def par_sep_def merge_ades_up_def;
      pred_auto; blast)

lemma ades_par_by_merge_PBMH_ades [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is PBMH_ades"
  by (simp only: Healthy_def' PBMH_ades_par_by_merge_raw[symmetric]
      PBMH_ades_idem)

lemma A0_healthy_non_empty:
  assumes "P is A0" "P (s0, out)"
    "des_vars.ok\<^sub>v s0"
    "\<not> P (s0, ok\<^sub>v_update (\<lambda>_. False) out)"
    "des_vars.ok\<^sub>v out"
  shows "achoices.ac\<^sub>v (des_vars.more out) \<noteq> {}"
proof -
  have fixed: "A0 P = P"
    using assms(1) by (simp add: Healthy_def')
  have fixed_at: "A0 P (s0, out) = P (s0, out)"
    by (simp only: fixed)
  show ?thesis
    using fixed_at assms(2-)
    by (cases s0; cases out; simp add: A0_def; pred_auto)
qed

lemma ades_par_by_merge_H1_closure:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
  using assms
  by (simp add: Healthy_def' H1_def par_by_merge_def par_sep_def
      merge_ades_up_def fun_eq_iff; pred_auto; blast)

lemma ades_par_by_merge_H2_closure:
  assumes "P is H2" "Q is H2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H2"
  using assms
  apply (simp add: H2_equiv pred_refine_iff par_by_merge_def par_sep_def
      merge_ades_up_def)
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

lemma ades_par_by_merge_H_closure:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is \<^bold>H"
proof -
  have HP: "\<^bold>H P = P" and HQ: "\<^bold>H Q = Q"
    using assms by (simp_all add: Healthy_def')
  have P_h1: "P is H1"
  proof -
    have "H1 P = H1 (\<^bold>H P)" by (simp only: HP)
    also have "... = \<^bold>H P" by (simp add: H1_idem)
    also have "... = P" by (rule HP)
    finally show ?thesis by (simp add: Healthy_def')
  qed
  have Q_h1: "Q is H1"
  proof -
    have "H1 Q = H1 (\<^bold>H Q)" by (simp only: HQ)
    also have "... = \<^bold>H Q" by (simp add: H1_idem)
    also have "... = Q" by (rule HQ)
    finally show ?thesis by (simp add: Healthy_def')
  qed
  have P_h2: "P is H2"
  proof -
    have "H2 P = H2 (\<^bold>H P)" by (simp only: HP)
    also have "... = \<^bold>H P"
      by (simp add: H1_H2_commute H2_idem)
    also have "... = P" by (rule HP)
    finally show ?thesis by (simp add: Healthy_def')
  qed
  have Q_h2: "Q is H2"
  proof -
    have "H2 Q = H2 (\<^bold>H Q)" by (simp only: HQ)
    also have "... = \<^bold>H Q"
      by (simp add: H1_H2_commute H2_idem)
    also have "... = Q" by (rule HQ)
    finally show ?thesis by (simp add: Healthy_def')
  qed
  have h1: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H1"
    by (rule ades_par_by_merge_H1_closure[OF P_h1 Q_h1])
  have h2: "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is H2"
    by (rule ades_par_by_merge_H2_closure[OF P_h2 Q_h2])
  show ?thesis
    using h1 h2 by (simp add: Healthy_def' H1_H2_comp)
qed

text \<open>
  Totality is needed only for @{const A0}: once both successful branch
  choice sets are known to be non-empty, it supplies a merged state and so
  rules out an empty combined choice set.
\<close>

lemma ades_par_by_merge_A0_closure:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes "P is A0" "Q is A0" "ades_merge_total j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0"
proof (rule Healthy_intro, rule ext)
  fix w :: "'s astate des_vars_ext \<times> 's achoices des_vars_ext"
  obtain s0 out where w_eq [simp]: "w = (s0, out)"
    by (cases w) auto
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  show "A0 ?R w = ?R w"
  proof
    assume "A0 ?R w"
    then show "?R w"
      by (simp add: A0_def; pred_auto)
  next
    assume R: "?R w"
    show "A0 ?R w"
      using R
      apply (simp add: A0_def)
      apply pred_auto
      subgoal premises prems for ok s ok\<^sub>p X ok\<^sub>q Y
      proof -
        let ?s0 = "\<lparr>ok\<^sub>v = True, s\<^sub>v = s, \<dots> = ()\<rparr>"
        let ?p = "\<lparr>ok\<^sub>v = ok\<^sub>p, ac\<^sub>v = X, \<dots> = ()\<rparr>"
        let ?q = "\<lparr>ok\<^sub>v = ok\<^sub>q, ac\<^sub>v = Y, \<dots> = ()\<rparr>"
        let ?p\<^sub>f = "ok\<^sub>v_update (\<lambda>_. False) ?p"
        let ?q\<^sub>f = "ok\<^sub>v_update (\<lambda>_. False) ?q"
        let ?out\<^sub>f = "ok\<^sub>v_update (\<lambda>_. False) out"
        have oks: "ok\<^sub>p" "ok\<^sub>q"
          using prems(3,6)
          by (simp_all add: merge_ades_up_def)
        have no_P_fail: "\<not> P (?s0, ?p\<^sub>f)"
        proof
          assume P_fail: "P (?s0, ?p\<^sub>f)"
          have no_merge:
              "\<not> M\<^sub>A\<^sub>D\<^sup>\<up>(j)
                (\<lparr>mrg_prior\<^sub>v = ?s0,
                   mrg_left\<^sub>v = ?p\<^sub>f,
                   mrg_right\<^sub>v = ?q,
                   \<dots> = ()\<rparr>, ?out\<^sub>f)"
            using prems(8) P_fail prems(2) by (simp; blast)
          have "M\<^sub>A\<^sub>D\<^sup>\<up>(j)
                (\<lparr>mrg_prior\<^sub>v = ?s0,
                   mrg_left\<^sub>v = ?p\<^sub>f,
                   mrg_right\<^sub>v = ?q,
                   \<dots> = ()\<rparr>, ?out\<^sub>f)"
            using prems(3) by (simp add: merge_ades_up_def)
          then show False using no_merge by contradiction
        qed
        have no_Q_fail: "\<not> Q (?s0, ?q\<^sub>f)"
        proof
          assume Q_fail: "Q (?s0, ?q\<^sub>f)"
          have no_merge:
              "\<not> M\<^sub>A\<^sub>D\<^sup>\<up>(j)
                (\<lparr>mrg_prior\<^sub>v = ?s0,
                   mrg_left\<^sub>v = ?p,
                   mrg_right\<^sub>v = ?q\<^sub>f,
                   \<dots> = ()\<rparr>, ?out\<^sub>f)"
            using prems(8) prems(1) Q_fail by (simp; blast)
          have "M\<^sub>A\<^sub>D\<^sup>\<up>(j)
                (\<lparr>mrg_prior\<^sub>v = ?s0,
                   mrg_left\<^sub>v = ?p,
                   mrg_right\<^sub>v = ?q\<^sub>f,
                   \<dots> = ()\<rparr>, ?out\<^sub>f)"
            using prems(3) by (simp add: merge_ades_up_def)
          then show False using no_merge by contradiction
        qed
        note P_non_empty =
          A0_healthy_non_empty[OF assms(1) prems(1)]
        have X_ne: "X \<noteq> {}"
          using P_non_empty no_P_fail oks(1) by simp
        note Q_non_empty =
          A0_healthy_non_empty[OF assms(2) prems(2)]
        have Y_ne: "Y \<noteq> {}"
          using Q_non_empty no_Q_fail oks(2) by simp
        obtain x where x: "x \<in> X" using X_ne by blast
        obtain y where y: "y \<in> Y" using Y_ne by blast
        have merge_exists:
            "\<exists>z. j (\<lparr>mrg_prior\<^sub>v = s,
                mrg_left\<^sub>v = x,
                mrg_right\<^sub>v = y,
                \<dots> = ()\<rparr>, z)"
          using assms(3) by (simp add: ades_merge_total_def)
        then obtain z where z:
            "j (\<lparr>mrg_prior\<^sub>v = s,
                mrg_left\<^sub>v = x,
                mrg_right\<^sub>v = y,
                \<dots> = ()\<rparr>, z)"
          by blast
        show False
          using prems(3,7) x y z
          by (simp add: merge_ades_up_def; blast)
      qed
      done
  qed
qed

lemma ades_par_by_merge_A1_closure:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A1"
proof -
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  have R_H: "?R is \<^bold>H"
    by (rule ades_par_by_merge_H_closure[OF assms])
  have R_PBMH: "?R is PBMH_ades"
    by (rule ades_par_by_merge_PBMH_ades)
  have "A1 ?R = PBMH_ades ?R"
    by (rule A1_eq_PBMH_ades[OF R_H])
  also have "... = ?R"
    using R_PBMH by (simp add: Healthy_def')
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma ades_par_by_merge_A_closure [closure]:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes "P is A" "Q is A" "ades_merge_total j"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
proof -
  have AP: "A P = P" and AQ: "A Q = Q"
    using assms(1,2) by (simp_all add: Healthy_def')
  have P_H: "P is \<^bold>H" and Q_H: "Q is \<^bold>H"
    using A_is_H[of P] A_is_H[of Q]
    by (simp_all add: AP AQ Healthy_def')
  have P_A0: "P is A0" and Q_A0: "Q is A0"
  proof -
    have "A0 (A P) = A P" "A0 (A Q) = A Q"
      by (simp_all add: A_def A0_idem)
    then show "P is A0" "Q is A0"
      by (simp_all add: AP AQ Healthy_def')
  qed
  let ?R = "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"
  have R_A0: "?R is A0"
    by (rule ades_par_by_merge_A0_closure[OF P_A0 Q_A0 assms(3)])
  have R_A1: "?R is A1"
    by (rule ades_par_by_merge_A1_closure[OF P_H Q_H])
  have "A ?R = A0 (A1 ?R)"
    by (simp only: A_def)
  also have "... = A0 ?R"
    by (simp only: Healthy_if[OF R_A1])
  also have "... = ?R"
    by (simp only: Healthy_if[OF R_A0])
  finally show ?thesis
    by (simp add: Healthy_def')
qed

theorem ades_par_by_merge_comm:
  fixes P Q :: "'s angelic_design" and j :: "'s merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> P"
  by (rule par_by_merge_comm, rule merge_ades_up_swap[OF assms])

end
