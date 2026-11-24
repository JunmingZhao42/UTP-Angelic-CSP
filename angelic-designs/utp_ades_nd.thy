section \<open>Non-Divergent Angelic Designs\<close>

theory utp_ades_nd
  imports utp_ades_a2
begin

subsection \<open>Non-Divergent Angelic Designs\<close>

(* Choice_AD = true \<turnstile> (ac' \<noteq> {}). *)
definition Choice_AD :: "'s angelic_design" where
[pred]: "Choice_AD \<equiv> (true \<turnstile> ac_non_empty)"

lemma Choice_AD_is_A [closure]: "Choice_AD is A"
  by (simp add: Healthy_def' Choice_AD_def A_design_form ac_non_empty_def;
      pred_auto)

(* NDAD P = P \<and> Choice_AD. *)
definition NDAD :: "'s angelic_design \<Rightarrow> 's angelic_design" where
[pred]: "NDAD P \<equiv> P \<squnion>\<^sub>A\<^sub>D Choice_AD"

lemma NDAD_obs:
  "NDAD P (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (P (ades_obs ok0 s0 ok' ac') \<and> (ok0 \<longrightarrow> ok' \<and> ac' \<noteq> {}))"
  by (simp add: NDAD_def Choice_AD_def angelic_design_angelic
      design_def ac_non_empty_def; pred_auto)

lemma preD_NDAD [simp]: "pre\<^sub>D (NDAD P) = true"
  by (subst preD_true_iff; pred_auto; simp add: NDAD_obs)

lemma NDAD_idem: "NDAD (NDAD P) = NDAD P"
  by (simp add: NDAD_def inf_assoc)

lemma NDAD_Idempotent [closure]: "Idempotent NDAD"
  by (simp add: Idempotent_def NDAD_idem)

lemma NDAD_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> NDAD P \<sqsubseteq> NDAD Q"
  unfolding NDAD_def angelic_design_angelic
  by (intro pred_ba.inf_mono; simp)

lemma NDAD_Monotonic [closure]: "Monotonic NDAD"
  by (rule MonotonicI, rule NDAD_mono)

lemma NDAD_A_closure [closure]:
  assumes "P is A"
  shows "NDAD P is A"
  unfolding NDAD_def
  by (rule A_angelic_closure[OF assms Choice_AD_is_A])

lemma NDAD_Choice: "NDAD Choice_AD = Choice_AD"
  by (simp add: NDAD_def)

lemma NDAD_healthy_obs_iff:
  "P is NDAD \<longleftrightarrow>
   (\<forall>s0 ok' ac'. P (ades_obs True s0 ok' ac') \<longrightarrow>
      ok' \<and> ac' \<noteq> {})"
proof
  assume fixed: "P is NDAD"
  show "\<forall>s0 ok' ac'. P (ades_obs True s0 ok' ac') \<longrightarrow>
      ok' \<and> ac' \<noteq> {}"
  proof (intro allI impI)
    fix s0 ok' ac'
    assume p: "P (ades_obs True s0 ok' ac')"
    have eq: "NDAD P (ades_obs True s0 ok' ac') = P (ades_obs True s0 ok' ac')"
      using fixed by (simp add: Healthy_def')
    show "ok' \<and> ac' \<noteq> {}"
      using eq p by (simp add: NDAD_obs)
  qed
next
  assume guard: "\<forall>s0 ok' ac'. P (ades_obs True s0 ok' ac') \<longrightarrow>
      ok' \<and> ac' \<noteq> {}"
  have eq: "NDAD P (ades_obs ok0 s0 ok' ac') =
      P (ades_obs ok0 s0 ok' ac')" for ok0 s0 ok' ac'
    using guard by (cases ok0; simp add: NDAD_obs; blast)
  show "P is NDAD"
    by (rule Healthy_intro, rule ades_obs_ext, rule eq)
qed

(* Under A0, non-divergence also excludes the empty terminating choice set. *)
lemma NDAD_healthy_iff:
  assumes "P is A0"
  shows "P is NDAD \<longleftrightarrow> pre\<^sub>D P = true"
proof
  assume healthy: "P is NDAD"
  have guard: "\<forall>s0 ok' ac'. P (ades_obs True s0 ok' ac') \<longrightarrow>
      ok' \<and> ac' \<noteq> {}"
    by (rule NDAD_healthy_obs_iff[THEN iffD1, OF healthy])
  show "pre\<^sub>D P = true"
    using guard by (subst preD_true_iff; pred_auto; blast)
next
  assume pre: "pre\<^sub>D P = true"
  have no_div: "\<forall>s0 ok' ac'. P (ades_obs True s0 ok' ac') \<longrightarrow> ok'"
    using preD_true_iff[THEN iffD1, OF pre] by (pred_auto; blast)
  have a0: "\<forall>s0. P (ades_obs True s0 True {}) \<longrightarrow>
      P (ades_obs True s0 False {})"
    using assms by (simp add: A0_healthy_obs_iff)
  have no_empty: "\<forall>s0. \<not> P (ades_obs True s0 True {})"
    using a0 no_div by blast
  have guard: "\<forall>s0 ok' ac'. P (ades_obs True s0 ok' ac') \<longrightarrow>
      ok' \<and> ac' \<noteq> {}"
  proof (intro allI impI)
    fix s0 ok' ac'
    assume p: "P (ades_obs True s0 ok' ac')"
    have ok': "ok'"
      using no_div p by blast
    have "ac' \<noteq> {}"
      using no_empty p ok' by auto
    with ok' show "ok' \<and> ac' \<noteq> {}" by simp
  qed
  show "P is NDAD"
    by (rule NDAD_healthy_obs_iff[THEN iffD2, OF guard])
qed

end
