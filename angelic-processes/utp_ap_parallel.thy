section \<open>Angelic Process Parallel-by-Merge\<close>

theory utp_ap_parallel
  imports utp_ap_ops
begin

subsection \<open>AD Merge Specialisation\<close>

type_synonym 's ap_merge_rel = "'s ades_merge_rel"

text \<open>
  AP parallel reuses the upward-closed choice-set merge defined at the
  angelic-design layer.  The exact-image merge remains available there as
  @{const merge_ades}; no second AP semantic definition is introduced.
\<close>

abbreviation merge_AP :: "'s merge \<Rightarrow> 's ap_merge_rel" ("M\<^sub>A\<^sub>P'(_')") where
  "merge_AP j \<equiv> merge_ades_up j"

lemmas merge_AP_swap = merge_ades_up_swap

subsection \<open>Parallel Composition\<close>

abbreviation ap_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) rad_state merge \<Rightarrow>
   ('t, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>P\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q"

lemma ap_par_eval:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  shows
    "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) (s0, out) \<longleftrightarrow>
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
  by (rule ades_par_eval)

theorem ap_par_comm:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "swap\<^sub>m ;; j = j"
  shows "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P"
  by (rule ades_par_comm, rule assms)

subsection \<open>Healthiness Closure\<close>

lemma II_AP_ap_par_wait:
  fixes j :: "('t::trace, 'e) rad_state merge"
    and x :: "('t, 'e) rad_state astate des_vars_ext"
    and y :: "('t, 'e) rad_state achoices des_vars_ext"
  assumes jh: "j is RA3m"
    and wait: "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))"
  shows "(II_AP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> II_AP) (x, y) = II_AP (x, y)"
proof (cases "des_vars.ok\<^sub>v x")
  case False
  let ?p = "\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v y, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
  let ?q = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
  have Ip: "II_AP (x, ?p)" and Iq: "II_AP (x, ?q)"
    using False by (simp_all add: II_AP_eval)
  show ?thesis
    unfolding ap_par_eval
    apply (rule iffI)
     apply (simp add: II_AP_eval False)
    apply (rule exI[of _ ?p], rule exI[of _ ?q])
    using Ip Iq by auto
next
  case True
  let ?s = "astate.s\<^sub>v (des_vars.more x)"
  have jw: "\<And>a b z.
      j (\<lparr>mrg_prior\<^sub>v = ?s, mrg_left\<^sub>v = a,
          mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z) \<longleftrightarrow> z = ?s"
    by (simp add: RA3m_healthy_wait[OF jh] wait)
  show ?thesis
  proof (rule iffI)
    assume par: "(II_AP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> II_AP) (x, y)"
    from par[unfolded ap_par_eval] obtain p q where
      Ip: "II_AP (x, p)" and Iq: "II_AP (x, q)" and
      ok_eq: "des_vars.ok\<^sub>v y =
        (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q)" and
      img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
                  j (\<lparr>mrg_prior\<^sub>v = ?s, mrg_left\<^sub>v = a,
                      mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)}
            \<subseteq> achoices.ac\<^sub>v (des_vars.more y)"
      by blast
    have sp: "?s \<in> achoices.ac\<^sub>v (des_vars.more p)"
      and sq: "?s \<in> achoices.ac\<^sub>v (des_vars.more q)"
      and op: "des_vars.ok\<^sub>v p" and oq: "des_vars.ok\<^sub>v q"
      using Ip Iq True by (auto simp add: II_AP_eval)
    have sy: "?s \<in> achoices.ac\<^sub>v (des_vars.more y)"
      using sp sq img by (auto simp add: jw)
    show "II_AP (x, y)"
      using op oq sy True ok_eq by (simp add: II_AP_eval)
  next
    assume Iy: "II_AP (x, y)"
    let ?p = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s}, \<dots> = ()\<rparr>"
    let ?q = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s}, \<dots> = ()\<rparr>"
    have Ip: "II_AP (x, ?p)" and Iq: "II_AP (x, ?q)"
      using True by (simp_all add: II_AP_eval)
    show "(II_AP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> II_AP) (x, y)"
      unfolding ap_par_eval
      apply (rule exI[of _ ?p], rule exI[of _ ?q])
      using Ip Iq Iy True by (auto simp add: II_AP_eval jw)
  qed
qed

lemma RA3AP_ap_par:
  fixes j :: "('t::trace, 'e) rad_state merge"
  assumes jh: "j is RA3m"
  shows "RA3AP P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> RA3AP Q =
    RA3AP (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q)"
proof (rule ext)
  fix w :: "('t, 'e) rad_state astate des_vars_ext \<times>
            ('t, 'e) rad_state achoices des_vars_ext"
  obtain x y where w_eq [simp]: "w = (x, y)"
    by (cases w) auto
  show "(RA3AP P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> RA3AP Q) w =
      RA3AP (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) w"
  proof (cases "rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x))")
    case False
    then show ?thesis
      by (simp add: ap_par_eval RA3AP_eval)
  next
    case True
    have h: "(II_AP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> II_AP) (x, y) = II_AP (x, y)"
      by (rule II_AP_ap_par_wait[OF jh True])
    show ?thesis
      using h True by (simp add: ap_par_eval RA3AP_eval)
  qed
qed

text \<open>
  AP closure needs totality of the state merge through @{const A0j},
  together with the reactive merge healthiness @{const RADM}.  It does not
  require the additional angelic-design conditions @{const A2j} or
  @{const A3j}.
\<close>

lemma ap_par_AP_closure [closure]:
  fixes P Q :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is AP" "Q is AP" "j is RADM" "A0j j"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) is AP"
proof -
  let ?NP = "((\<not> (RA2 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>f)) \<turnstile>
    (RA2 \<circ> RA1 \<circ> PBMH_ades) ((P \<^sub>f)\<^sup>t))"
  let ?NQ = "((\<not> (RA2 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>f)) \<turnstile>
    (RA2 \<circ> RA1 \<circ> PBMH_ades) ((Q \<^sub>f)\<^sup>t))"
  have P_eq: "P = RA3AP ?NP"
    by (simp only: AP_RA3AP_design[symmetric] Healthy_if[OF assms(1)])
  have Q_eq: "Q = RA3AP ?NQ"
    by (simp only: AP_RA3AP_design[symmetric] Healthy_if[OF assms(2)])
  have j2: "j is RA2m"
    by (rule RADM_implies_RA2m[OF assms(3)])
  have j3: "j is RA3m"
    by (rule RADM_implies_RA3m[OF assms(3)])
  have body_A: "(?NP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> ?NQ) is A"
    by (rule ades_par_A_closure[OF AP_body_is_A AP_body_is_A assms(4)])
  have body_RA2: "(?NP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> ?NQ) is RA2"
    by (rule ades_par_RA2_closure[OF AP_body_is_RA2 AP_body_is_RA2 j2])
  have closed: "RA3AP (?NP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> ?NQ) is AP"
    by (rule RA3AP_AP_intro[OF body_A body_RA2])
  have form: "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q =
      RA3AP (?NP \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> ?NQ)"
    apply (subst P_eq)
    apply (subst Q_eq)
    by (rule RA3AP_ap_par[OF j3])
  show ?thesis
    using closed by (simp only: form)
qed

subsection \<open>Miracle\<close>

theorem top_AP_parallel_left_zero:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is AP" "j is RA3m"
  shows "\<^bold>\<top>\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>P"
proof -
  have P_eq: "P = AP P"
    using assms(1) by (simp add: Healthy_def')
  have j_eq: "j = RA3m j"
    using assms(2) by (simp add: Healthy_def')
  show ?thesis
    apply (subst P_eq)
    apply (subst j_eq)
    apply (simp add: fun_eq_iff ap_par_eval top_AP_design
        AP_wait_cond_design RA3m_def design_def)
    apply pred_auto
    done
qed

theorem top_AP_parallel_right_zero:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is AP" "j is RA3m"
  shows "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>P = \<^bold>\<top>\<^sub>A\<^sub>P"
proof -
  have P_eq: "P = AP P"
    using assms(1) by (simp add: Healthy_def')
  have j_eq: "j = RA3m j"
    using assms(2) by (simp add: Healthy_def')
  show ?thesis
    apply (subst P_eq)
    apply (subst j_eq)
    apply (simp add: fun_eq_iff ap_par_eval top_AP_design
        AP_wait_cond_design RA3m_def design_def)
    apply pred_auto
    done
qed

subsection \<open>Chaos\<close>

lemma Chaos_AP_eval:
  "Chaos\<^sub>A\<^sub>P (x, y) \<longleftrightarrow>
   (\<not> des_vars.ok\<^sub>v x \<or>
    \<not> rad_state.wait\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<or>
    (des_vars.ok\<^sub>v y \<and>
     astate.s\<^sub>v (des_vars.more x) \<in>
       achoices.ac\<^sub>v (des_vars.more y)))"
  by (simp add: Chaos_AP_design design_def; pred_auto)

theorem Chaos_AP_parallel_left_zero:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is AP" "AP_feasible P" "j is RA3m"
  shows "Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P"
proof (rule ext)
  fix w :: "('t, 'e) rad_state astate des_vars_ext \<times>
            ('t, 'e) rad_state achoices des_vars_ext"
  obtain x y where w_eq [simp]: "w = (x, y)"
    by (cases w) auto
  let ?s = "astate.s\<^sub>v (des_vars.more x)"
  let ?A = "achoices.ac\<^sub>v (des_vars.more y)"
  have P3: "P is RA3AP"
    by (rule AP_is_RA3AP[OF assms(1)])
  have target:
      "(Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P) (x, y) = Chaos\<^sub>A\<^sub>P (x, y)"
  proof (cases "des_vars.ok\<^sub>v x")
    case False
    let ?p = "\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v y, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
    let ?q = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
    have Cp: "Chaos\<^sub>A\<^sub>P (x, ?p)"
      using False by (simp add: Chaos_AP_eval)
    have Pq: "P (x, ?q)"
      by (rule AP_healthy_not_ok_eval[OF assms(1) False])
    show ?thesis
      unfolding ap_par_eval
      apply (rule iffI)
       apply (simp add: Chaos_AP_eval False)
      apply (rule exI[of _ ?p], rule exI[of _ ?q])
      using Cp Pq by auto
  next
    case True
    show ?thesis
    proof (cases "rad_state.wait\<^sub>v ?s")
      case False
      obtain q where Pq: "P (x, q)" and okq: "des_vars.ok\<^sub>v q"
        using AP_feasibleD[OF assms(2) True False] by blast
      let ?p = "\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v y, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
      have Cp: "Chaos\<^sub>A\<^sub>P (x, ?p)"
        using False by (simp add: Chaos_AP_eval)
      show ?thesis
        unfolding ap_par_eval
        apply (rule iffI)
         apply (simp add: Chaos_AP_eval False)
        apply (rule exI[of _ ?p], rule exI[of _ q])
        using Cp Pq okq by auto
    next
      case True_wait: True
      have jw: "\<And>a b z.
          j (\<lparr>mrg_prior\<^sub>v = ?s, mrg_left\<^sub>v = a,
              mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z) \<longleftrightarrow> z = ?s"
        by (simp add: RA3m_healthy_wait[OF assms(3)] True_wait)
      have Pw: "\<And>q. P (x, q) \<longleftrightarrow> II_AP (x, q)"
        by (rule RA3AP_healthy_wait_eval[OF P3 True_wait])
      show ?thesis
      proof (rule iffI)
        assume par: "(Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P) (x, y)"
        from par[unfolded ap_par_eval] obtain p q where
          Cp: "Chaos\<^sub>A\<^sub>P (x, p)" and Pq: "P (x, q)" and
          ok_eq: "des_vars.ok\<^sub>v y =
            (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q)" and
          img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                    \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
                  j (\<lparr>mrg_prior\<^sub>v = ?s, mrg_left\<^sub>v = a,
                      mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)} \<subseteq> ?A"
          by blast
        have IIq: "II_AP (x, q)"
          using Pq by (simp add: Pw)
        have sp: "?s \<in> achoices.ac\<^sub>v (des_vars.more p)"
          using Cp True True_wait by (auto simp add: Chaos_AP_eval)
        have sq: "?s \<in> achoices.ac\<^sub>v (des_vars.more q)"
          using IIq True by (auto simp add: II_AP_eval)
        have sy: "?s \<in> ?A"
          using sp sq img by (auto simp add: jw)
        have oky: "des_vars.ok\<^sub>v y"
          using Cp IIq True True_wait
          by (auto simp add: Chaos_AP_eval II_AP_eval ok_eq)
        show "Chaos\<^sub>A\<^sub>P (x, y)"
          using oky sy by (simp add: Chaos_AP_eval True True_wait)
      next
        assume Cy: "Chaos\<^sub>A\<^sub>P (x, y)"
        let ?p = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s}, \<dots> = ()\<rparr>"
        let ?q = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s}, \<dots> = ()\<rparr>"
        have Cp: "Chaos\<^sub>A\<^sub>P (x, ?p)"
          using True True_wait by (simp add: Chaos_AP_eval)
        have IIq: "II_AP (x, ?q)"
          using True by (simp add: II_AP_eval)
        have Pq: "P (x, ?q)"
          using IIq by (simp add: Pw)
        show "(Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P) (x, y)"
          unfolding ap_par_eval
          apply (rule exI[of _ ?p], rule exI[of _ ?q])
          using Cp Pq Cy True True_wait by (auto simp add: Chaos_AP_eval jw)
      qed
    qed
  qed
  show "(Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P) w = Chaos\<^sub>A\<^sub>P w"
    using target by (simp only: w_eq)
qed

theorem Chaos_AP_parallel_right_zero:
  fixes P :: "('t::trace, 'e) reactive_angelic_design"
    and j :: "('t, 'e) rad_state merge"
  assumes "P is AP" "AP_feasible P" "j is RA3m"
  shows "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P = Chaos\<^sub>A\<^sub>P"
proof (rule ext)
  fix w :: "('t, 'e) rad_state astate des_vars_ext \<times>
            ('t, 'e) rad_state achoices des_vars_ext"
  obtain x y where w_eq [simp]: "w = (x, y)"
    by (cases w) auto
  let ?s = "astate.s\<^sub>v (des_vars.more x)"
  let ?A = "achoices.ac\<^sub>v (des_vars.more y)"
  have P3: "P is RA3AP"
    by (rule AP_is_RA3AP[OF assms(1)])
  have target:
      "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P) (x, y) = Chaos\<^sub>A\<^sub>P (x, y)"
  proof (cases "des_vars.ok\<^sub>v x")
    case False
    let ?p = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
    let ?q = "\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v y, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
    have Pp: "P (x, ?p)"
      by (rule AP_healthy_not_ok_eval[OF assms(1) False])
    have Cq: "Chaos\<^sub>A\<^sub>P (x, ?q)"
      using False by (simp add: Chaos_AP_eval)
    show ?thesis
      unfolding ap_par_eval
      apply (rule iffI)
       apply (simp add: Chaos_AP_eval False)
      apply (rule exI[of _ ?p], rule exI[of _ ?q])
      using Pp Cq by auto
  next
    case True
    show ?thesis
    proof (cases "rad_state.wait\<^sub>v ?s")
      case False
      obtain p where Pp: "P (x, p)" and okp: "des_vars.ok\<^sub>v p"
        using AP_feasibleD[OF assms(2) True False] by blast
      let ?q = "\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v y, ac\<^sub>v = {}, \<dots> = ()\<rparr>"
      have Cq: "Chaos\<^sub>A\<^sub>P (x, ?q)"
        using False by (simp add: Chaos_AP_eval)
      show ?thesis
        unfolding ap_par_eval
        apply (rule iffI)
         apply (simp add: Chaos_AP_eval False)
        apply (rule exI[of _ p], rule exI[of _ ?q])
        using Pp okp Cq by auto
    next
      case True_wait: True
      have jw: "\<And>a b z.
          j (\<lparr>mrg_prior\<^sub>v = ?s, mrg_left\<^sub>v = a,
              mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z) \<longleftrightarrow> z = ?s"
        by (simp add: RA3m_healthy_wait[OF assms(3)] True_wait)
      have Pw: "\<And>p. P (x, p) \<longleftrightarrow> II_AP (x, p)"
        by (rule RA3AP_healthy_wait_eval[OF P3 True_wait])
      show ?thesis
      proof (rule iffI)
        assume par: "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P) (x, y)"
        from par[unfolded ap_par_eval] obtain p q where
          Pp: "P (x, p)" and Cq: "Chaos\<^sub>A\<^sub>P (x, q)" and
          ok_eq: "des_vars.ok\<^sub>v y =
            (des_vars.ok\<^sub>v p \<and> des_vars.ok\<^sub>v q)" and
          img: "{z. \<exists>a \<in> achoices.ac\<^sub>v (des_vars.more p).
                    \<exists>b \<in> achoices.ac\<^sub>v (des_vars.more q).
                  j (\<lparr>mrg_prior\<^sub>v = ?s, mrg_left\<^sub>v = a,
                      mrg_right\<^sub>v = b, \<dots> = ()\<rparr>, z)} \<subseteq> ?A"
          by blast
        have IIp: "II_AP (x, p)"
          using Pp by (simp add: Pw)
        have sp: "?s \<in> achoices.ac\<^sub>v (des_vars.more p)"
          using IIp True by (auto simp add: II_AP_eval)
        have sq: "?s \<in> achoices.ac\<^sub>v (des_vars.more q)"
          using Cq True True_wait by (auto simp add: Chaos_AP_eval)
        have sy: "?s \<in> ?A"
          using sp sq img by (auto simp add: jw)
        have oky: "des_vars.ok\<^sub>v y"
          using IIp Cq True True_wait
          by (auto simp add: II_AP_eval Chaos_AP_eval ok_eq)
        show "Chaos\<^sub>A\<^sub>P (x, y)"
          using oky sy by (simp add: Chaos_AP_eval True True_wait)
      next
        assume Cy: "Chaos\<^sub>A\<^sub>P (x, y)"
        let ?p = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s}, \<dots> = ()\<rparr>"
        let ?q = "\<lparr>ok\<^sub>v = True, ac\<^sub>v = {?s}, \<dots> = ()\<rparr>"
        have IIp: "II_AP (x, ?p)"
          using True by (simp add: II_AP_eval)
        have Pp: "P (x, ?p)"
          using IIp by (simp add: Pw)
        have Cq: "Chaos\<^sub>A\<^sub>P (x, ?q)"
          using True True_wait by (simp add: Chaos_AP_eval)
        show "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P) (x, y)"
          unfolding ap_par_eval
          apply (rule exI[of _ ?p], rule exI[of _ ?q])
          using Pp Cq Cy True True_wait by (auto simp add: Chaos_AP_eval jw)
      qed
    qed
  qed
  show "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P) w = Chaos\<^sub>A\<^sub>P w"
    using target by (simp only: w_eq)
qed

end
