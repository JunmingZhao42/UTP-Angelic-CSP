theory AP_Probe
  imports "UTP-Angelic-CSP.utp_ap_parallel_operator" "RAD_Geometry_Probe.RAD_Probe"
begin

section \<open>The synchronisation examples at AP level\<close>

(* On nondivergent operands AP parallel is H1 of RAD parallel on the RA1 images,
   and H1 leaves a started prior unchanged, so the AP examples reduce to the RAD ones *)
lemma ap_par_started:
  assumes "P is AP" "Q is AP" "P is NDAP" "Q is NDAP"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) (ades_obs True s0 c Z) \<longleftrightarrow>
    (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q) (ades_obs True s0 c Z)"
  by (simp only: ap_par_rad_NDAP[OF assms] H1_obs simp_thms)

(* the prefix processes and their choices are nondivergent *)
lemma PrefixSkip_AP_NDAP: "PrefixSkip_AP a is NDAP"
  unfolding Healthy_def PrefixSkip_AP_def
  by (rule NDAP_AP_true_design_fixed[OF PrefixSkip_AP_facts(1) _ PrefixSkip_AP_facts(3)])
     (simp add: Healthy_def PrefixSkip_AP_facts(2))

lemma PrefixSkip_AP_choice_healthy:
  "(PrefixSkip_AP a \<sqinter>\<^sub>A\<^sub>P PrefixSkip_AP b) is AP" "(PrefixSkip_AP a \<sqinter>\<^sub>A\<^sub>P PrefixSkip_AP b) is NDAP"
  "(PrefixSkip_AP a \<squnion>\<^sub>A\<^sub>P PrefixSkip_AP b) is AP" "(PrefixSkip_AP a \<squnion>\<^sub>A\<^sub>P PrefixSkip_AP b) is NDAP"
  by (rule AP_demonic_closure[OF PrefixSkip_AP_is_AP PrefixSkip_AP_is_AP],
      rule Healthy_intro[where H=NDAP, OF NDAP_demonic_closure[OF PrefixSkip_AP_NDAP PrefixSkip_AP_NDAP]],
      rule AP_angelic_closure[OF PrefixSkip_AP_is_AP PrefixSkip_AP_is_AP],
      rule Healthy_intro[where H=NDAP, OF NDAP_angelic_closure[OF PrefixSkip_AP_NDAP PrefixSkip_AP_NDAP]])

lemmas ap_par_started_prefix =
  ap_par_started[OF PrefixSkip_AP_is_AP PrefixSkip_AP_is_AP PrefixSkip_AP_NDAP PrefixSkip_AP_NDAP]
lemmas ap_par_started_dchoice =
  ap_par_started[OF PrefixSkip_AP_is_AP PrefixSkip_AP_choice_healthy(1)
    PrefixSkip_AP_NDAP PrefixSkip_AP_choice_healthy(2)]
lemmas ap_par_started_achoice =
  ap_par_started[OF PrefixSkip_AP_is_AP PrefixSkip_AP_choice_healthy(3)
    PrefixSkip_AP_NDAP PrefixSkip_AP_choice_healthy(4)]

lemma RA1_PrefixSkip_AP_achoice:
  "RA1 (PrefixSkip_AP a \<squnion>\<^sub>A\<^sub>P PrefixSkip_AP b) = PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
  by (simp only: RAD_angelic_choice RA1_conj RA1_PrefixSkip_AP)

lemma RA1_PrefixSkip_AP_dchoice:
  "RA1 (PrefixSkip_AP a \<sqinter>\<^sub>A\<^sub>P PrefixSkip_AP b) = PrefixSkip_RAD a \<sqinter>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b"
  by (simp only: RAD_demonic_choice RA1_disj RA1_PrefixSkip_AP)

(* with a partner that also does a, the composite can terminate after a *)
lemma ap_sync_progress:
  assumes "\<not> rad_wait\<^sub>v s0"
  shows "(PrefixSkip_AP a \<parallel>\<^sub>A\<^sub>P\<^bsub>jsync\<^esub> PrefixSkip_AP a) (ades_obs True s0 True {done_a a s0})"
  using rad_sync_progress[OF assms] by (simp only: ap_par_started_prefix RA1_PrefixSkip_AP)

(* a demonic partner does not block progress *)
lemma ap_sync_demonic_progress:
  assumes "\<not> rad_wait\<^sub>v s0"
  shows "(PrefixSkip_AP a \<parallel>\<^sub>A\<^sub>P\<^bsub>jsync\<^esub> (PrefixSkip_AP a \<sqinter>\<^sub>A\<^sub>P PrefixSkip_AP b))
           (ades_obs True s0 True {done_a a s0})"
  using rad_sync_demonic_progress[OF assms]
  by (simp only: ap_par_started_dchoice RA1_PrefixSkip_AP RA1_PrefixSkip_AP_dchoice)

(* an angelic partner blocks progress, as in RAD *)
lemma ap_sync_angelic_stuck:
  assumes "\<not> rad_wait\<^sub>v s0" "a \<noteq> b"
    and "(PrefixSkip_AP a \<parallel>\<^sub>A\<^sub>P\<^bsub>jsync\<^esub> (PrefixSkip_AP a \<squnion>\<^sub>A\<^sub>P PrefixSkip_AP b))
           (ades_obs True s0 c Z)"
  shows "\<exists>z\<in>Z. rad_tr\<^sub>v z = rad_tr\<^sub>v s0"
proof -
  have "(PrefixSkip_RAD a \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>jsync\<^esub> (PrefixSkip_RAD a \<squnion>\<^sub>R\<^sub>A\<^sub>D PrefixSkip_RAD b))
          (ades_obs True s0 c Z)"
    using assms(3) by (simp only: ap_par_started_achoice RA1_PrefixSkip_AP RA1_PrefixSkip_AP_achoice)
  then show ?thesis
    by (rule rad_sync_angelic_stuck[OF assms(1,2)])
qed

(* so the AP composite is the RAD one at started priors *)
lemma ap_sync_angelic_eval:
  assumes "\<not> rad_wait\<^sub>v s0" "a \<noteq> b"
  shows "(PrefixSkip_AP a \<parallel>\<^sub>A\<^sub>P\<^bsub>jsync\<^esub> (PrefixSkip_AP a \<squnion>\<^sub>A\<^sub>P PrefixSkip_AP b))
           (ades_obs True s0 c Z) \<longleftrightarrow>
         c \<and> (\<exists>y\<in>Z. rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y)"
  by (simp only: ap_par_started_achoice RA1_PrefixSkip_AP RA1_PrefixSkip_AP_achoice
      rad_sync_angelic_eval[OF assms])

(* AP Miracle, at a started prior, keeps a waiting state and has nothing else *)
lemma top_AP_obs:
  "(\<^bold>\<top>\<^sub>A\<^sub>P :: ('e list, 'e) angelic_process) (ades_obs True s1 c Z) \<longleftrightarrow>
    c \<and> rad_wait\<^sub>v s1 \<and> s1 \<in> Z"
  by (simp add: top_AP_design design_def ades_state_choice_def expr_if_def; pred_auto)

(* a followed by AP Miracle, at a started non-waiting prior *)
lemma Prefix_AP_top_obs:
  assumes s0: "\<not> rad_wait\<^sub>v s0"
  shows "(a \<rightarrow>\<^sub>A\<^sub>P \<^bold>\<top>\<^sub>A\<^sub>P) (ades_obs True s0 c Z) \<longleftrightarrow>
         c \<and> (\<exists>y\<in>Z. rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y)"
proof -
  have "(a \<rightarrow>\<^sub>A\<^sub>P \<^bold>\<top>\<^sub>A\<^sub>P) (ades_obs True s0 c Z) \<longleftrightarrow>
      (\<exists>ok0. PrefixSkip_RAD a (ades_obs True s0 ok0 {s1. \<^bold>\<top>\<^sub>A\<^sub>P (ades_obs ok0 s1 c Z)}))"
    unfolding Prefix_AP_def angelic_design_seq_def H1_PrefixSkip_RAD[symmetric]
    by (simp add: H1_obs)
  also have "\<dots> \<longleftrightarrow> (\<exists>y. \<^bold>\<top>\<^sub>A\<^sub>P (ades_obs True y c Z) \<and> pobs a s0 y)"
    by (simp only: PrefixSkip_RAD_obs[OF s0] mem_Collect_eq Bex_def ex_bool_eq simp_thms)
  also have "\<dots> \<longleftrightarrow> c \<and> (\<exists>y\<in>Z. rad_wait\<^sub>v y \<and> rad_tr\<^sub>v y = rad_tr\<^sub>v s0 \<and> a \<notin> rad_ref\<^sub>v y)"
    by (simp only: top_AP_obs pobs_def) auto
  finally show ?thesis .
qed

(* at a started waiting prior, every RAD process keeps the state *)
lemma RAD_waiting_obs:
  assumes "P is RAD" "rad_wait\<^sub>v s0"
  shows "P (ades_obs True s0 c Z) \<longleftrightarrow> c \<and> s0 \<in> Z"
proof -
  have "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D (ades_obs True s0 c Z) \<Longrightarrow> P (ades_obs True s0 c Z)"
      "P (ades_obs True s0 c Z) \<Longrightarrow> Chaos\<^sub>R\<^sub>A\<^sub>D (ades_obs True s0 c Z)"
    using top_RAD_upper[OF assms(1)] bottom_RAD_lower[OF assms(1)]
    unfolding Chaos_RAD_RAD pred_refine_iff by blast+
  moreover have "\<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D (ades_obs True s0 c Z) \<longleftrightarrow> c \<and> s0 \<in> Z"
      "Chaos\<^sub>R\<^sub>A\<^sub>D (ades_obs True s0 c Z) \<longleftrightarrow> c \<and> s0 \<in> Z"
    using assms(2) by (simp_all add: top_RAD_eval Chaos_RAD_eval)
  ultimately show ?thesis by blast
qed

(* the AP prefix of Miracle, unfolded: H1 at the prior, then the RAD prefix *)
lemma Prefix_AP_top_unfold:
  "(a \<rightarrow>\<^sub>A\<^sub>P \<^bold>\<top>\<^sub>A\<^sub>P) (ades_obs ok0 s0 c Z) \<longleftrightarrow>
    \<not> ok0 \<or> (\<exists>ok1. PrefixSkip_RAD a (ades_obs True s0 ok1 {s1. \<^bold>\<top>\<^sub>A\<^sub>P (ades_obs ok1 s1 c Z)}))"
  unfolding Prefix_AP_def angelic_design_seq_def H1_PrefixSkip_RAD[symmetric]
  by (cases ok0; simp add: H1_obs)

(* so the AP composite is exactly a followed by AP Miracle *)
theorem ap_sync_angelic_miracle:
  assumes ab: "a \<noteq> b"
  shows "PrefixSkip_AP a \<parallel>\<^sub>A\<^sub>P\<^bsub>jsync\<^esub> (PrefixSkip_AP a \<squnion>\<^sub>A\<^sub>P PrefixSkip_AP b) =
         a \<rightarrow>\<^sub>A\<^sub>P \<^bold>\<top>\<^sub>A\<^sub>P"
proof -
  have lhs: "PrefixSkip_AP a \<parallel>\<^sub>A\<^sub>P\<^bsub>jsync\<^esub> (PrefixSkip_AP a \<squnion>\<^sub>A\<^sub>P PrefixSkip_AP b) =
      H1 (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D)"
    by (simp only: ap_par_rad_NDAP[OF PrefixSkip_AP_is_AP PrefixSkip_AP_choice_healthy(3)
          PrefixSkip_AP_NDAP PrefixSkip_AP_choice_healthy(4)]
        RA1_PrefixSkip_AP RA1_PrefixSkip_AP_achoice rad_sync_angelic_miracle[OF ab])
  have rad: "(a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D) is RAD"
    by (rule Prefix_RAD_closure[OF RAD_healthy])
  show ?thesis
    unfolding lhs
  proof (rule ades_obs_ext)
    fix ok0 s0 c Z
    show "H1 (a \<rightarrow>\<^sub>R\<^sub>A\<^sub>D \<^bold>\<top>\<^sub>R\<^sub>A\<^sub>D) (ades_obs ok0 s0 c Z) = (a \<rightarrow>\<^sub>A\<^sub>P \<^bold>\<top>\<^sub>A\<^sub>P) (ades_obs ok0 s0 c Z)"
    proof (cases ok0)
      assume ok: ok0
      show ?thesis
      proof (cases "rad_wait\<^sub>v s0")
        assume w: "rad_wait\<^sub>v s0"
        have "(a \<rightarrow>\<^sub>A\<^sub>P \<^bold>\<top>\<^sub>A\<^sub>P) (ades_obs True s0 c Z) \<longleftrightarrow> c \<and> s0 \<in> Z"
          by (simp only: Prefix_AP_top_unfold RAD_waiting_obs[OF PrefixSkip_RAD_is_RAD w]
              mem_Collect_eq ex_bool_eq simp_thms top_AP_obs) (simp add: w)
        then show ?thesis
          using ok by (simp add: H1_obs RAD_waiting_obs[OF rad w])
      next
        assume w: "\<not> rad_wait\<^sub>v s0"
        show ?thesis
          using ok by (simp add: H1_obs Prefix_RAD_top_obs[OF w] Prefix_AP_top_obs[OF w])
      qed
    next
      assume "\<not> ok0"
      then show ?thesis
        by (simp add: H1_obs Prefix_AP_top_unfold)
    qed
  qed
qed

end
