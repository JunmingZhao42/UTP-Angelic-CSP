section \<open>Reactive angelic design parallel by merge\<close>

theory utp_rad_parallel
  imports utp_rad_csp "UTP-Angelic-Designs.utp_ades_parallel"
    "UTP-Reactive-Designs.utp_rdes_parallel_lift"
begin

(* The ordinary parallel import restores this notation; retain the RAD meaning. *)
no_notation wait_f ("_\<^sub>f" [1000] 1000)

type_synonym ('t, 'e) rad_merge_rel =
  "(('t, 'e) rad_state) ades_merge_rel"

definition basic_merge_state ::
  "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow>
   ('t, 'e) rad_state \<Rightarrow> ('t, 'e) rad_state \<Rightarrow> bool"
where
  "basic_merge_state s0 sL sR s' \<longleftrightarrow>
    rad_tr\<^sub>v s0 \<le> rad_tr\<^sub>v s' \<and>
    rad_tr\<^sub>v s' = rad_tr\<^sub>v sL \<and>
    rad_tr\<^sub>v s' = rad_tr\<^sub>v sR \<and>
    rad_wait\<^sub>v s' = (rad_wait\<^sub>v sL \<or> rad_wait\<^sub>v sR)"


text \<open>Parallel uses a lifted merge on complete reactive observations.
  RAD and A2 operands yield a RAD-healthy result when the merge is ORDm-healthy.
  The ordinary correspondence uses p2ac rather than d2ac.\<close>

subsection \<open>Choice-set lifting\<close>

text \<open>Every pair of branch states must have a merged output in the final set.
  The ordinary merge supplies the control, trace, waiting and refusal policy.\<close>

definition rad_lift_merge ::
  "('t::trace, 'e set) rp merge \<Rightarrow> ('t, 'e) rad_merge_rel"
where
  "rad_lift_merge M = (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m;
        p = mrg_left\<^sub>v m;
        q = mrg_right\<^sub>v m;
        X = achoices.ac\<^sub>v (des_vars.more p);
        Y = achoices.ac\<^sub>v (des_vars.more q);
        Z = achoices.ac\<^sub>v (des_vars.more z);
        s0 = astate.s\<^sub>v (des_vars.more x)
    in X \<noteq> {} \<and> Y \<noteq> {} \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
        merge_eval M
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v x, \<dots> = s0\<rparr>)
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v p, \<dots> = sL\<rparr>)
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v q, \<dots> = sR\<rparr>)
          (\<lparr>ok\<^sub>v = des_vars.ok\<^sub>v z, \<dots> = s'\<rparr>)))"

lemma rad_lift_merge_obs:
  "ades_merge_obs (rad_lift_merge M) ok0 s0 okL X okR Y ok' Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
      merge_eval M (\<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>)
        (\<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>)
        (\<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>)
        (\<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)))"
  by (simp add: rad_lift_merge_def Let_def)

lemma rad_lift_merge_mono:
  "M \<sqsubseteq> N \<Longrightarrow> rad_lift_merge M \<sqsubseteq> rad_lift_merge N"
  by (auto simp: pred_refine_iff rad_lift_merge_def Let_def split: prod.splits; blast)

lemma rad_lift_merge_SymMerge:
  "M is SymMerge \<Longrightarrow> rad_lift_merge M is SymMerge"
proof -
  assume assms: "M is SymMerge"
  have sym: "merge_eval M x p q z = merge_eval M x q p z" for x p q z
    using assms by (simp add: SymMerge_eval)
  show ?thesis
    by (simp add: SymMerge_eval rad_lift_merge_def Let_def sym; blast)
qed

subsection \<open>RAD parallel by merge\<close>

definition rad_par ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e set) rp merge \<Rightarrow>
    ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = (P \<parallel>\<^bsub>rad_lift_merge M\<^esub> Q)"

lemma rad_par_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
  shows "p2ac P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> p2ac Q = p2ac (P \<parallel>\<^bsub>M\<^esub> Q)"
  unfolding rad_par_def
  apply (rule ades_obs_ext)
  apply (simp only: rad_p2ac_obs par_by_merge_eval
      choices_ex rad_lift_merge_obs[simplified])
  apply (simp only: des_vars.splits)
  by (blast intro: exI[where x="{_}"])

lemma rad_par_form:
  "\<lbrakk> P is RAD; Q is RAD; P is A2; Q is A2 \<rbrakk> \<Longrightarrow>
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = p2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
proof -
  assume assms: "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  show ?thesis
  using rad_par_p2ac[of "ac2p P" M "ac2p Q"]
    by (simp only: rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
        rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])
qed

lemma rad_par_ac2p:
  "\<lbrakk> P is RAD; Q is RAD; P is A2; Q is A2 \<rbrakk> \<Longrightarrow>
    ac2p (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) = (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
proof -
  assume assms: "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  show ?thesis
  by (simp only: rad_par_form[OF assms] rad_ac2p_p2ac_inverse')
qed

lemma rad_par_A2:
  "\<lbrakk> P is RAD; Q is RAD; P is A2; Q is A2 \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A2"
proof -
  assume assms: "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  show ?thesis
  by (simp add: rad_par_form[OF assms] Healthy_def')
qed

text \<open>Closure transfers from ordinary RD parallel through p2ac. ORDm is
  sufficient; no normality premise or excluded-output witness is required.\<close>

lemma rad_par_RAD [closure]:
  "\<lbrakk> P is RAD; Q is RAD; P is A2; Q is A2; M is ORDm \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is RAD"
proof -
  assume assms: "P is RAD" "Q is RAD" "P is A2" "Q is A2" "M is ORDm"
  show ?thesis
  unfolding rad_par_form[OF assms(1-4)]
    by (rule rad_p2ac_RD_closure,
        rule RD_par_by_ORDm[OF rad_ac2p_RD[OF assms(1,3)] rad_ac2p_RD[OF assms(2,4)] assms(5)])
qed

subsection \<open>Algebra\<close>

lemma rad_par_mono:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow>
    P1 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q1 \<sqsubseteq> P2 \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q2"
proof -
  assume assms: "P1 \<sqsubseteq> P2" "Q1 \<sqsubseteq> Q2"
  show ?thesis
  unfolding rad_par_def
    using assms
    by (auto simp: pred_refine_iff par_by_merge_eval split: prod.splits; blast)
qed

lemma rad_par_comm:
  "rad_lift_merge M is SymMerge \<Longrightarrow>
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> P"
proof -
  assume assms: "rad_lift_merge M is SymMerge"
  show ?thesis
  unfolding rad_par_def
    by (rule par_by_merge_comm[OF assms])
qed

lemma rad_par_comm_merge:
  "M is SymMerge \<Longrightarrow>
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q = Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> P"
proof -
  assume assms: "M is SymMerge"
  show ?thesis
  by (rule rad_par_comm[OF rad_lift_merge_SymMerge[OF assms]])
qed

lemma rad_par_assoc_state:
  "\<lbrakk> P is RAD;
     Q is RAD;
     R is RAD;
     P is A2;
     Q is A2;
     R is A2;
     M is ORDm;
     \<And>x p q r z.
      (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z) =
      (\<exists>u. merge_eval M x q r u \<and> merge_eval M x p u z) \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R)"
proof -
  assume assms: "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2" "M is ORDm"
    "\<And>x p q r z.
      (\<exists>u. merge_eval M x p q u \<and> merge_eval M x u r z) =
      (\<exists>u. merge_eval M x q r u \<and> merge_eval M x p u z)"
  note assoc = assms(8)
  have ordinary: "((D \<parallel>\<^bsub>M\<^esub> E) \<parallel>\<^bsub>M\<^esub> F) = (D \<parallel>\<^bsub>M\<^esub> (E \<parallel>\<^bsub>M\<^esub> F))" for D E F
    using par_by_merge_assoc_iff[of M] assoc by blast
  have pq: "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is RAD" "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) is A2"
    by (simp_all add: rad_par_RAD[OF assms(1,2,4,5,7)] rad_par_A2[OF assms(1,2,4,5)])
  have qr: "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) is RAD" "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R) is A2"
    by (simp_all add: rad_par_RAD[OF assms(2,3,5,6,7)] rad_par_A2[OF assms(2,3,5,6)])
  show ?thesis
    by (simp only: rad_par_form[OF pq(1) assms(3) pq(2) assms(6)]
        rad_par_form[OF assms(1) qr(1) assms(4) qr(2)]
        rad_par_ac2p[OF assms(1,2,4,5)]
        rad_par_ac2p[OF assms(2,3,5,6)] ordinary)
qed

lemma rad_par_assoc:
  "\<lbrakk> P is RAD; Q is RAD; R is RAD; P is A2; Q is A2; R is A2; M is ORDm; M is SymMerge;
     AssocMerge M \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R = P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>M\<^esub> R)"
proof -
  assume assms: "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2" "M is ORDm"
    "M is SymMerge" "AssocMerge M"
  have ordinary: "\<forall>D E F.
    (D \<parallel>\<^bsub>M\<^esub> E) \<parallel>\<^bsub>M\<^esub> F =
    D \<parallel>\<^bsub>M\<^esub> (E \<parallel>\<^bsub>M\<^esub> F)"
    using par_by_merge_assoc[OF assms(8,9)] by blast
  show ?thesis
    by (rule rad_par_assoc_state[OF assms(1-7)];
        use ordinary par_by_merge_assoc_iff[of M] in blast)
qed

text \<open>The lifted RD merge is associative only for operands whose RD
  images never diverge from an active prior; the law transfers through
  @{const ac2p}.\<close>

lemma rad_par_lift_assoc:
  "\<lbrakk> P is RAD; Q is RAD; R is RAD; P is A2; Q is A2; R is A2; j is SymMerge;
     AssocMerge j; pre\<^sub>R (ac2p P) = true\<^sub>r; pre\<^sub>R (ac2p Q) = true\<^sub>r;
     pre\<^sub>R (ac2p R) = true\<^sub>r \<rbrakk> \<Longrightarrow>
    (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>rdes_lift_merge j\<^esub> Q) \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>rdes_lift_merge j\<^esub> R =
    P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>rdes_lift_merge j\<^esub> (Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>rdes_lift_merge j\<^esub> R)"
proof -
  assume assms: "P is RAD" "Q is RAD" "R is RAD" "P is A2" "Q is A2" "R is A2" "j is SymMerge"
    "AssocMerge j" "pre\<^sub>R (ac2p P) = true\<^sub>r" "pre\<^sub>R (ac2p Q) = true\<^sub>r"
    "pre\<^sub>R (ac2p R) = true\<^sub>r"
  let ?M = "rdes_lift_merge j"
  have M: "?M is ORDm" by (rule rdes_lift_merge_ORDm)
  have rd: "ac2p P is RD" "ac2p Q is RD" "ac2p R is RD"
    using rad_ac2p_RD assms(1-6) by blast+
  have nondiv: "ac2p P is NDRD" "ac2p Q is NDRD" "ac2p R is NDRD"
    using rd assms(9-11) by (simp_all add: NDRD_healthy_iff)
  have ordinary: "(ac2p P \<parallel>\<^bsub>?M\<^esub> ac2p Q) \<parallel>\<^bsub>?M\<^esub> ac2p R =
      ac2p P \<parallel>\<^bsub>?M\<^esub> (ac2p Q \<parallel>\<^bsub>?M\<^esub> ac2p R)"
    by (rule rdes_lift_parallel_assoc_nondiv[OF assms(7,8) rd nondiv])
  have pq: "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>?M\<^esub> Q) is RAD" "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>?M\<^esub> Q) is A2"
    by (simp_all add: rad_par_RAD[OF assms(1,2,4,5) M] rad_par_A2[OF assms(1,2,4,5)])
  have qr: "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>?M\<^esub> R) is RAD" "(Q \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>?M\<^esub> R) is A2"
    by (simp_all add: rad_par_RAD[OF assms(2,3,5,6) M] rad_par_A2[OF assms(2,3,5,6)])
  show ?thesis
    by (simp only: rad_par_form[OF pq(1) assms(3) pq(2) assms(6)]
        rad_par_form[OF assms(1) qr(1) assms(4) qr(2)]
        rad_par_ac2p[OF assms(1,2,4,5)]
        rad_par_ac2p[OF assms(2,3,5,6)] ordinary)
qed


subsection \<open>Basic merge example\<close>

definition rad_basic_merge :: "('t::trace, 'e set) rp merge" where
  "rad_basic_merge = (\<lambda>(m,z).
    (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and>
      des_vars.ok\<^sub>v (mrg_right\<^sub>v m) \<longrightarrow> des_vars.ok\<^sub>v z) \<and>
    basic_merge_state
      (des_vars.more (mrg_prior\<^sub>v m))
      (des_vars.more (mrg_left\<^sub>v m))
      (des_vars.more (mrg_right\<^sub>v m))
      (des_vars.more z))"

lemma rad_lift_basic_merge_obs:
  "ades_merge_obs (rad_lift_merge rad_basic_merge) ok0 s0 okL X okR Y ok' Z =
    (X \<noteq> {} \<and> Y \<noteq> {} \<and> (okL \<and> okR \<longrightarrow> ok') \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z. basic_merge_state s0 sL sR s'))"
  apply (simp only: rad_lift_merge_obs)
  by (simp add: rad_basic_merge_def; blast)

lemma rad_lift_basic_trace_agreement:
  "\<lbrakk> ades_merge_obs (rad_lift_merge rad_basic_merge) ok0 s0 okL X okR Y ok' Z;
     sL \<in> X; sR \<in> Y \<rbrakk> \<Longrightarrow>
    rad_tr\<^sub>v sL = rad_tr\<^sub>v sR"
proof -
  assume assms: "ades_merge_obs (rad_lift_merge rad_basic_merge) ok0 s0 okL X okR Y ok' Z"
    "sL \<in> X" "sR \<in> Y"
  show ?thesis
  using assms
    apply (simp only: rad_lift_basic_merge_obs)
    unfolding basic_merge_state_def
    by fastforce
qed

lemma rad_lift_basic_singletons:
  "ades_merge_obs (rad_lift_merge rad_basic_merge)
      ok0 s0 True {sL} True {sR} True Z =
    (\<exists>s'\<in>Z. basic_merge_state s0 sL sR s')"
  by (simp add: rad_lift_basic_merge_obs[simplified])

lemma rad_lift_basic_same:
  "ades_merge_obs (rad_lift_merge rad_basic_merge)
    ok0 s0 True {s0} True {s0} True {s0}"
  by (simp add: rad_lift_basic_merge_obs[simplified] basic_merge_state_def)


subsubsection \<open>Repairing the Basic Merge\<close>

text \<open>The basic merge is not ORDm-healthy. Applying ORDm repairs unstarted
  and waiting behaviour. On started, non-waiting observations it preserves the
  original policy when both branch traces extend the initial trace. These
  trace premises hold for outputs admitted by R1-healthy operands.\<close>

context
begin

declare des_vars.splits [alpha_splits del]

lemma rad_basic_merge_not_ORDm:
  "\<not> ((rad_basic_merge :: ('t::trace, 'e set) rp merge) is ORDm)"
proof -
  have "\<not> ((rad_basic_merge :: ('t, 'e set) rp merge) is RD1m)"
    apply (simp add: Healthy_def' fun_eq_iff rad_basic_merge_def basic_merge_state_def)
    apply (pred_simp)
    by (metis (mono_tags, lifting) order_refl)
  then show ?thesis by (simp add: ORDm_healthy_iff)
qed

lemma rad_basic_merge_RD2: "rad_basic_merge is RD2"
  by (simp add: Healthy_def' RD2_def H2_split rad_basic_merge_def basic_merge_state_def; pred_auto)

lemma rad_basic_merge_R2m:
  "\<lbrakk> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p;
     rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v q \<rbrakk> \<Longrightarrow>
    merge_eval (R2m rad_basic_merge) x p q z = merge_eval rad_basic_merge x p q z"
proof -
  assume assms: "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p"
    "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v q"
  show ?thesis
  using assms
    apply (simp add: rad_basic_merge_def basic_merge_state_def)
    apply (pred_simp)
    by (metis diff_add_cancel_left')
qed

lemma ORDm_basic_merge_running:
  "\<lbrakk> des_vars.ok\<^sub>v x; \<not> rea_vars.wait\<^sub>v x;
     rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p;
     rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v q \<rbrakk> \<Longrightarrow>
    merge_eval (ORDm rad_basic_merge) x p q z = merge_eval rad_basic_merge x p q z"
proof -
  assume assms: "des_vars.ok\<^sub>v x" "\<not> rea_vars.wait\<^sub>v x"
    "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p"
    "rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v q"
  show ?thesis
  using assms
    by (simp add: ORDm_def Healthy_if[OF rad_basic_merge_RD2]
        RD1m_eval R3cm_eval rad_basic_merge_R2m[OF assms(3,4)])
qed

lemma ORDm_basic_merge_waiting:
  "\<lbrakk> des_vars.ok\<^sub>v x; rea_vars.wait\<^sub>v x \<rbrakk> \<Longrightarrow>
    merge_eval (ORDm rad_basic_merge) x p q z = (z = x)"
  by (simp add: ORDm_def R3cm_def RD1m_def; pred_auto)

end

subsubsection \<open>Post-State-Dependent Failure\<close>

text \<open>The seed below constrains the final refusal set, including on failure.
  With RD true as each operand, started running parallel accepts an output
  exactly when its trace extends the initial trace and its refusal set is empty.
  In particular, the failure slice still depends on the post-state. The raw
  p2ac correspondence transfers this example to RAD and A2 operands.\<close>

context
begin

declare des_vars.splits [alpha_splits del]

lemma ORDm_post_ref_example:
  fixes x z :: "('t::trace, 'e set) rp"
  shows "\<lbrakk> des_vars.ok\<^sub>v x; \<not> rea_vars.wait\<^sub>v x \<rbrakk> \<Longrightarrow>
    (RD true \<parallel>\<^bsub>ORDm (\<lambda>(m,y). rea_vars.more y = {})\<^esub> RD true) (x,z) =
    (rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z \<and> rea_vars.more z = {})"
proof -
  assume assms: "des_vars.ok\<^sub>v x" "\<not> rea_vars.wait\<^sub>v x"
  let ?N = "ORDm (\<lambda>(m,y). rea_vars.more y = {})"
  have d: "RD true (x,p) \<longleftrightarrow> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v p" for p
    using assms by (cases x; cases p; simp add: RD2_def H2_split; pred_auto)
  have n: "merge_eval ?N x p q z \<longleftrightarrow> rea_vars.tr\<^sub>v x \<le> rea_vars.tr\<^sub>v z \<and> rea_vars.more z = {}"
    for p q
    using assms by (cases x; cases z; simp add: ORDm_def RD2_def H2_split; pred_auto)
  show ?thesis
    by (simp only: par_by_merge_eval d n; blast intro: exI[where x=x])
qed

end

end
