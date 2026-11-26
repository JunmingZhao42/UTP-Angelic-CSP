section \<open>Angelic Process Parallel Algebra\<close>

theory utp_ap_parallel_algebra
  imports utp_ap_parallel_operator
begin

subsection \<open>Monotonicity and commutativity\<close>

lemma ap_par_mono:
  assumes "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  shows "P1 \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q1 \<sqsubseteq> P2 \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q2"
  by (rule par_by_merge_mono[OF assms]; simp)

lemma ap_par_comm:
  assumes "j is SymMerge"
  shows "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q = Q \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P"
  by (rule par_by_merge_comm[OF merge_ap_SymMerge[OF assms]])

subsection \<open>Choice\<close>

text \<open>Demonic choice is disjunction and angelic choice is conjunction, so the
  laws for any merge apply: P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R).\<close>

(* P \<parallel> (Q \<sqinter> R) = (P \<parallel> Q) \<sqinter> (P \<parallel> R) *)
lemma ap_par_demonic_distl:
  "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> (Q \<sqinter>\<^sub>A\<^sub>P R) = (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) \<sqinter>\<^sub>A\<^sub>P (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R)"
  by (simp only: AP_demonic_choice par_by_merge_disj_distl)

(* (P \<sqinter> Q) \<parallel> R = (P \<parallel> R) \<sqinter> (Q \<parallel> R) *)
lemma ap_par_demonic_distr:
  "(P \<sqinter>\<^sub>A\<^sub>P Q) \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R = (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R) \<sqinter>\<^sub>A\<^sub>P (Q \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R)"
  by (simp only: AP_demonic_choice par_by_merge_disj_distr)

(* (P \<parallel> Q) \<squnion> (P \<parallel> R) \<sqsubseteq> P \<parallel> (Q \<squnion> R) *)
lemma ap_par_angelic_subdistl:
  "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>P (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R) \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> (Q \<squnion>\<^sub>A\<^sub>P R)"
  by (simp only: AP_angelic_choice par_by_merge_conj_subdistl)

(* (P \<parallel> R) \<squnion> (Q \<parallel> R) \<sqsubseteq> (P \<squnion> Q) \<parallel> R *)
lemma ap_par_angelic_subdistr:
  "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R) \<squnion>\<^sub>A\<^sub>P (Q \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R) \<sqsubseteq> (P \<squnion>\<^sub>A\<^sub>P Q) \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R"
  by (simp only: AP_angelic_choice par_by_merge_conj_subdistr)

text \<open>For nondivergent operands, AP parallel is H1 of RAD parallel on the RA1
  images, so the RAD equality carries over: (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q.\<close>

(* (P \<parallel> Q) \<squnion> (P' \<parallel> Q) = (P \<squnion> P') \<parallel> Q *)
lemma ap_par_angelic_distr:
  fixes P P' Q :: "('t::trace, 'e) angelic_process"
  assumes ap: "P is AP" "P' is AP" "Q is AP" and nd: "P is NDAP" "P' is NDAP" "Q is NDAP"
    and q: "\<And>s0 Y Y'. Q (ades_obs True s0 True Y) \<Longrightarrow> Q (ades_obs True s0 True Y') \<Longrightarrow>
      Q (ades_obs True s0 True (Y \<inter> Y'))"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>P (P' \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) = (P \<squnion>\<^sub>A\<^sub>P P') \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q"
proof -
  have ndrad: "RA1 S is NDRAD" if "S is AP" "S is NDAP" for S :: "('t, 'e) angelic_process"
  proof -
    have "RA1 S = NDRAD (RAD S)"
      using RA1_NDAP_NDRAD[of S] by (simp only: comp_apply Healthy_if[OF that(1)] Healthy_if[OF that(2)])
    then show ?thesis by (simp add: Healthy_def NDRAD_idem)
  qed
  have h1: "(H1 S \<and> H1 T) = H1 (S \<and> T)" for S T :: "('t, 'e) angelic_process"
    by (simp add: H1_def; pred_auto)
  have ne: "rad_trace_extensions s0 \<inter> W \<noteq> {}" if "Q (ades_obs True s0 True W)" for s0 W
    using that AP_wait_obs[OF ap(3), of s0 True True W] NDAP_active_obs[OF nd(3), of s0 True W]
    by (cases "rad_wait\<^sub>v s0"; auto simp: rad_trace_extensions_def)
  have qr: "RA1 Q (ades_obs True s0 True (Y \<inter> Y'))"
    if "RA1 Q (ades_obs True s0 True Y)" "RA1 Q (ades_obs True s0 True Y')" for s0 Y Y'
  proof -
    let ?E = "rad_trace_extensions s0"
    have "Q (ades_obs True s0 True ((?E \<inter> Y) \<inter> (?E \<inter> Y')))"
      by (rule q) (use that in \<open>simp_all add: RA1_obs\<close>)
    moreover have "(?E \<inter> Y) \<inter> (?E \<inter> Y') = ?E \<inter> (Y \<inter> Y')" by blast
    ultimately have w: "Q (ades_obs True s0 True (?E \<inter> (Y \<inter> Y')))" by simp
    have "?E \<inter> (?E \<inter> (Y \<inter> Y')) \<noteq> {}" by (rule ne[OF w])
    then show ?thesis using w by (simp add: RA1_obs Int_assoc[symmetric])
  qed
  have pp: "(P \<squnion>\<^sub>A\<^sub>P P') is AP" "(P \<squnion>\<^sub>A\<^sub>P P') is NDAP"
    by (rule AP_angelic_closure[OF ap(1,2)],
        simp add: Healthy_def NDAP_angelic_closure[OF nd(1,2)])
  have rad: "RA1 P is RAD" "RA1 P' is RAD"
    by (simp_all add: RA1_AP_RAD_closure ap)
  have "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) \<squnion>\<^sub>A\<^sub>P (P' \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) =
      H1 ((RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q) \<squnion>\<^sub>R\<^sub>A\<^sub>D (RA1 P' \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q))"
    by (simp only: ap_par_rad_NDAP[OF ap(1,3) nd(1,3)] ap_par_rad_NDAP[OF ap(2,3) nd(2,3)]
        AP_angelic_choice angelic_design_angelic h1)
  also have "... = H1 ((RA1 P \<squnion>\<^sub>R\<^sub>A\<^sub>D RA1 P') \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q)"
    by (simp only: rad_par_angelic_distr[OF rad ndrad[OF ap(1) nd(1)]
          ndrad[OF ap(2) nd(2)] ndrad[OF ap(3) nd(3)] qr])
  also have "... = (P \<squnion>\<^sub>A\<^sub>P P') \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q"
    by (subst ap_par_rad_NDAP[OF pp(1) ap(3) pp(2) nd(3)])
       (simp only: AP_angelic_choice angelic_design_angelic RA1_conj)
  finally show ?thesis .
qed

subsection \<open>Zero laws\<close>

lemma ap_par_miracle:
  fixes P :: "('t::trace, 'e) angelic_process"
  assumes "P is AP"
  shows "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>P = \<^bold>\<top>\<^sub>A\<^sub>P" "\<^bold>\<top>\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>P"
proof -
  have top: "(\<^bold>\<top>\<^sub>A\<^sub>P :: ('t, 'e) angelic_process) (ades_obs ok0 s0 c Z) \<longleftrightarrow>
      (\<not> ok0 \<or> (rad_wait\<^sub>v s0 \<and> c \<and> s0 \<in> Z))" for ok0 s0 c Z
    by (simp add: top_AP_design; pred_auto)
  show "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> \<^bold>\<top>\<^sub>A\<^sub>P = \<^bold>\<top>\<^sub>A\<^sub>P" "\<^bold>\<top>\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = \<^bold>\<top>\<^sub>A\<^sub>P"
    by (rule ades_obs_ext;
        rename_tac ok0 s0 c Z; case_tac ok0; case_tac "rad_wait\<^sub>v s0";
        simp only: ades_par_by_merge_obs merge_ap_obs top AP_unstarted_obs[OF assms]
          AP_wait_obs[OF assms] if_True if_False simp_thms;
        blast)+
qed

text \<open>A divergent branch releases the output, so both Chaos processes absorb a
  partner with an observation at the prior trace, as for RAD, and the result is
  Chaos_AP: ChaosCSP_AP \<parallel> P = Chaos_AP.\<close>

lemma ap_par_chaos:
  fixes P :: "('t::trace, 'e) angelic_process" and j :: "('t \<times> 'e set) merge"
  assumes P: "P is AP"
    and act: "\<And>s0. \<not> rad_wait\<^sub>v s0 \<Longrightarrow> \<exists>c sR. P (ades_obs True s0 c {sR}) \<and> rad_tr\<^sub>v sR = rad_tr\<^sub>v s0"
    and empty: "\<And>s sL sR. \<exists>t e. merge_eval j (0, s) (0, sL) (0, sR) (t, e)"
  shows "Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P" "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P = Chaos\<^sub>A\<^sub>P"
    and "ChaosCSP\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P" "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> ChaosCSP\<^sub>A\<^sub>P = Chaos\<^sub>A\<^sub>P"
proof -
  have chaos: "Chaos\<^sub>A\<^sub>P (ades_obs ok0 s0 c Z) \<longleftrightarrow> (\<not> ok0 \<or> \<not> rad_wait\<^sub>v s0 \<or> (c \<and> s0 \<in> Z))"
    for ok0 s0 c Z
    by (simp add: Chaos_AP_design; pred_auto)
  (* a divergent output exists for the prior state and a state at the prior trace *)
  have mrg: "\<exists>s'. merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = a, \<dots> = sa\<rparr>
      \<lparr>ok\<^sub>v = b, \<dots> = sb\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = s'\<rparr>"
    if "\<not> rad_wait\<^sub>v s0" "\<not> (a \<and> b)" "rad_tr\<^sub>v sa = rad_tr\<^sub>v s0" "rad_tr\<^sub>v sb = rad_tr\<^sub>v s0"
    for s0 a b sa sb
  proof -
    obtain t e where e: "merge_eval j (0, rad_ref\<^sub>v s0) (0, rad_ref\<^sub>v sa) (0, rad_ref\<^sub>v sb) (t, e)"
      using empty by blast
    have "merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = a, \<dots> = sa\<rparr>
        \<lparr>ok\<^sub>v = b, \<dots> = sb\<rparr> \<lparr>ok\<^sub>v = False, \<dots> = rad_tr\<^sub>v_update (\<lambda>_. rad_tr\<^sub>v s0 + t) s0\<rparr>"
      using that e by (cases s0; cases sa; cases sb; simp add: merge_rdes_eval; blast intro: order_refl)
    then show ?thesis by blast
  qed
  (* any process that diverges with its prior state as the choice absorbs P *)
  have div: "D \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P \<and> P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> D = Chaos\<^sub>A\<^sub>P"
    if D: "D is AP" and d: "\<And>s0. \<not> rad_wait\<^sub>v s0 \<Longrightarrow> D (ades_obs True s0 False {s0})"
    for D :: "('t, 'e) angelic_process"
  proof -
    have lower: "(D \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P) (ades_obs True s0 c Z) \<and> (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> D) (ades_obs True s0 c Z)"
      if a: "\<not> rad_wait\<^sub>v s0" for s0 c Z
    proof -
      obtain cP sR where p: "P (ades_obs True s0 cP {sR})" "rad_tr\<^sub>v sR = rad_tr\<^sub>v s0"
        using act[OF a] by blast
      have m1: "ades_merge_obs (merge_ap j) True s0 False {s0} cP {sR} c Z"
        using mrg[OF a, of False cP s0 sR] p(2) a by (simp only: merge_ap_obs if_False simp_thms; simp)
      have m2: "ades_merge_obs (merge_ap j) True s0 cP {sR} False {s0} c Z"
        using mrg[OF a, of cP False sR s0] p(2) a by (simp only: merge_ap_obs if_False simp_thms; simp)
      show ?thesis
        unfolding ades_par_by_merge_obs using d[OF a] p(1) m1 m2 by blast
    qed
    have eq: "R = Chaos\<^sub>A\<^sub>P"
      if R: "R is AP" and low: "\<And>s0 c Z. \<not> rad_wait\<^sub>v s0 \<Longrightarrow> R (ades_obs True s0 c Z)" for R
    proof (rule ades_obs_ext)
      fix ok0 s0 c Z
      show "R (ades_obs ok0 s0 c Z) = Chaos\<^sub>A\<^sub>P (ades_obs ok0 s0 c Z)"
        by (cases ok0; cases "rad_wait\<^sub>v s0";
            simp add: chaos AP_unstarted_obs[OF R] AP_wait_obs[OF R] low)
    qed
    have "D \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P"
      by (rule eq[OF ap_par_AP[OF D P]]) (use lower in blast)
    moreover have "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> D = Chaos\<^sub>A\<^sub>P"
      by (rule eq[OF ap_par_AP[OF P D]]) (use lower in blast)
    ultimately show ?thesis ..
  qed
  have "Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P \<and> P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P = Chaos\<^sub>A\<^sub>P"
    by (rule div[OF Chaos_AP_is_AP]) (simp add: chaos)
  moreover have "ChaosCSP\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P \<and> P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> ChaosCSP\<^sub>A\<^sub>P = Chaos\<^sub>A\<^sub>P"
    by (rule div[OF ChaosCSP_AP_is_AP]) (simp add: ChaosCSP_AP_design RA1_obs; pred_auto)
  ultimately show "Chaos\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P" "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Chaos\<^sub>A\<^sub>P = Chaos\<^sub>A\<^sub>P"
    "ChaosCSP\<^sub>A\<^sub>P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> P = Chaos\<^sub>A\<^sub>P" "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> ChaosCSP\<^sub>A\<^sub>P = Chaos\<^sub>A\<^sub>P"
    by simp_all
qed

subsection \<open>Associativity\<close>

text \<open>We want nested parallel, so need associativity:
  (P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R).\<close>

theorem ap_par_assoc_det:
  assumes det: "Functional j" and tot: "mergeable j"
    and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R)"
  by (rule par_by_merge_assoc[OF merge_ap_SymMerge[OF sym] merge_ap_AssocMerge[OF det tot assoc]])

theorem ap_par_assoc_det_nd:
  fixes P Q R :: "('t::trace, 'e) angelic_process" and j :: "('t \<times> 'e set) merge"
  assumes nondiv: "P is NDAP" "Q is NDAP" "R is NDAP"
    and det: "Functional j" and sym: "j is SymMerge" and assoc: "AssocMerge j"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R = P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> (Q \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> R)"
proof -
  let ?G = "\<lambda>x z. des_vars.ok\<^sub>v x \<and> \<not> rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more x)) \<longrightarrow> des_vars.ok\<^sub>v z"
  have closed: "\<And>x p q z. \<lbrakk>?G x p; ?G x q; merge_eval (merge_ap j) x p q z\<rbrakk> \<Longrightarrow> ?G x z"
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 okL X okR Y ok' Z
      using merge_ap_active_ok[of s0 j X Y ok' Z] by (cases ok0; cases okL; cases okR; simp)
    done
  have nd: "\<And>x z. S (x, z) \<Longrightarrow> ?G x z" if "S is NDAP" for S :: "('t, 'e) angelic_process"
    apply (unfold des_vars.splits(1) astate.splits(1) achoices.splits(1) unit_all_eq1)
    subgoal for ok0 s0 ok' Z
      using NDAP_active_obs[OF that, of s0 ok' Z] by (cases ok0; auto)
    done
  show ?thesis
    by (rule par_by_merge_assoc_guard[OF
        SymMerge_merge_guard[OF merge_ap_SymMerge[OF sym]]
        merge_ap_guard_AssocMerge[OF det assoc] closed
        nd[OF nondiv(1)] nd[OF nondiv(2)] nd[OF nondiv(3)]])
qed

end
