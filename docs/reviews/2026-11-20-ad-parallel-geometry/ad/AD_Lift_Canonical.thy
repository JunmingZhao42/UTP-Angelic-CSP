theory AD_Lift_Canonical
  imports "UTP-Angelic-Designs.utp_ades"
begin

section \<open>Which merges on choice sets are admissible\<close>

text \<open>We compare an arbitrary merge M on choice sets with the shared lift
  ac'_lift_merge N of an inner merge N on single states. We ask two things of M:
  growing a branch choice set never helps, and on single branch states M merges
  no more than N.\<close>

(* M(X',Y',Z) and nonempty X \<subseteq> X', Y \<subseteq> Y' give M(X,Y,Z) *)
definition antitone_m :: "'s ades_merge_rel \<Rightarrow> bool" where
  "antitone_m M \<longleftrightarrow> (\<forall>ok0 s0 okL X X' okR Y Y' ok' Z.
     X \<noteq> {} \<longrightarrow> Y \<noteq> {} \<longrightarrow> X \<subseteq> X' \<longrightarrow> Y \<subseteq> Y' \<longrightarrow>
     ades_merge_obs M ok0 s0 okL X' okR Y' ok' Z \<longrightarrow> ades_merge_obs M ok0 s0 okL X okR Y ok' Z)"

(* M relates only nonempty branch choice sets *)
definition nonempty_m :: "'s ades_merge_rel \<Rightarrow> bool" where
  "nonempty_m M \<longleftrightarrow> (\<forall>ok0 s0 okL X okR Y ok' Z.
     ades_merge_obs M ok0 s0 okL X okR Y ok' Z \<longrightarrow> X \<noteq> {} \<and> Y \<noteq> {})"

(* M({sL},{sR},Z) needs some s' \<in> Z with N(s,sL,sR,s') *)
definition sound_m :: "'s des_merge \<Rightarrow> 's ades_merge_rel \<Rightarrow> bool" where
  "sound_m N M \<longleftrightarrow> (\<forall>ok0 s0 okL sL okR sR ok' Z.
     ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' Z \<longrightarrow>
     (\<exists>s'\<in>Z. merge_eval N \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
                          \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>))"

lemma antitone_mD:
  "antitone_m M \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> Y \<subseteq> Y' \<Longrightarrow> ades_merge_obs M ok0 s0 okL X' okR Y' ok' Z \<Longrightarrow>
   ades_merge_obs M ok0 s0 okL X okR Y ok' Z"
  unfolding antitone_m_def by blast

lemma nonempty_mD:
  "nonempty_m M \<Longrightarrow> ades_merge_obs M ok0 s0 okL X okR Y ok' Z \<Longrightarrow> X \<noteq> {} \<and> Y \<noteq> {}"
  unfolding nonempty_m_def by blast

lemma sound_mD:
  "sound_m N M \<Longrightarrow> ades_merge_obs M ok0 s0 okL {sL} okR {sR} ok' Z \<Longrightarrow>
   \<exists>s'\<in>Z. merge_eval N \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
                        \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>"
  unfolding sound_m_def by blast

section \<open>The shared lift is admissible and greatest\<close>

lemma lift_antitone: "antitone_m (ac'_lift_merge N)"
  unfolding antitone_m_def ac'_lift_merge_obs by blast

lemma lift_nonempty: "nonempty_m (ac'_lift_merge N)"
  unfolding nonempty_m_def ac'_lift_merge_obs by blast

lemma lift_sound: "sound_m N (ac'_lift_merge N)"
  unfolding sound_m_def ac'_lift_merge_obs by simp

(* on single branch states the lift is exactly N *)
lemma lift_singleton:
  "ades_merge_obs (ac'_lift_merge N) ok0 s0 okL {sL} okR {sR} ok' Z \<longleftrightarrow>
   (\<exists>s'\<in>Z. merge_eval N \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
                        \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>)"
  by (simp only: ac'_lift_merge_obs) simp

(* every admissible merge is contained in the lift *)
lemma lift_greatest_obs:
  assumes A: "antitone_m M" and E: "nonempty_m M" and S: "sound_m N M"
    and M: "ades_merge_obs M ok0 s0 okL X okR Y ok' Z"
  shows "ades_merge_obs (ac'_lift_merge N) ok0 s0 okL X okR Y ok' Z"
proof -
  have ne: "X \<noteq> {}" "Y \<noteq> {}" using nonempty_mD[OF E M] by simp_all
  have pairs: "\<exists>s'\<in>Z. merge_eval N \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
                        \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>"
    if "sL \<in> X" "sR \<in> Y" for sL sR
  proof -
    have "{sL} \<noteq> {}" "{sR} \<noteq> {}" "{sL} \<subseteq> X" "{sR} \<subseteq> Y" using that by simp_all
    from antitone_mD[OF A this M] show ?thesis by (rule sound_mD[OF S])
  qed
  show ?thesis
    unfolding ac'_lift_merge_obs using ne pairs by blast
qed

section \<open>Refinement consequences\<close>

lemma ades_merge_refine:
  fixes M1 M2 :: "'s ades_merge_rel"
  assumes "\<And>ok0 s0 okL X okR Y ok' Z.
    ades_merge_obs M2 ok0 s0 okL X okR Y ok' Z \<Longrightarrow> ades_merge_obs M1 ok0 s0 okL X okR Y ok' Z"
  shows "M1 \<sqsubseteq> M2"
  using assms by (simp add: pred_refine_iff; pred_auto)

lemma par_by_merge_merge_mono:
  assumes M: "M1 \<sqsubseteq> M2"
  shows "P \<parallel>\<^bsub>M1\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>M2\<^esub> Q"
  unfolding pred_refine_iff
proof (intro allI impI)
  fix w assume H: "(P \<parallel>\<^bsub>M2\<^esub> Q) w"
  obtain x z where w: "w = (x, z)" by (cases w)
  from H obtain p q where pq: "P (x, p)" "Q (x, q)" "merge_eval M2 x p q z"
    unfolding w par_by_merge_eval by blast
  have "merge_eval M1 x p q z" using M[unfolded pred_refine_iff, rule_format, OF pq(3)] .
  with pq(1,2) show "(P \<parallel>\<^bsub>M1\<^esub> Q) w" unfolding w par_by_merge_eval by blast
qed

lemma lift_greatest:
  assumes "antitone_m M" "nonempty_m M" "sound_m N M"
  shows "ac'_lift_merge N \<sqsubseteq> M"
  by (rule ades_merge_refine) (rule lift_greatest_obs[OF assms])

(* every admissible merge refines the shared lift's parallel composition *)
theorem par_lift_canonical:
  assumes "antitone_m M" "nonempty_m M" "sound_m N M"
  shows "P \<parallel>\<^bsub>ac'_lift_merge N\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>M\<^esub> Q"
  by (rule par_by_merge_merge_mono[OF lift_greatest[OF assms]])

section \<open>Antitonicity costs nothing for up-closed operands\<close>

lemma ABm_obs_antitone:
  assumes ne: "X \<noteq> {}" "Y \<noteq> {}" and sub: "X \<subseteq> X'" "Y \<subseteq> Y'"
    and H: "ades_merge_obs (ABm M) ok0 s0 okL X' okR Y' ok' Z"
  shows "ades_merge_obs (ABm M) ok0 s0 okL X okR Y ok' Z"
proof -
  from H obtain X'' Y'' where X'': "X' \<subseteq> X''" and Y'': "Y' \<subseteq> Y''"
    and M: "ades_merge_obs M ok0 s0 okL X'' okR Y'' ok' Z"
    unfolding ABm_obs by blast
  have "X \<subseteq> X''" by (rule subset_trans[OF sub(1) X''])
  moreover have "Y \<subseteq> Y''" by (rule subset_trans[OF sub(2) Y''])
  ultimately show ?thesis
    unfolding ABm_obs using ne M by (intro conjI exI[where x=X''] exI[where x=Y'']) simp_all
qed

lemma ABm_antitone: "antitone_m (ABm M)"
  unfolding antitone_m_def by (intro allI impI) (rule ABm_obs_antitone)

lemma ABm_nonempty: "nonempty_m (ABm M)"
  unfolding nonempty_m_def ABm_obs by (intro allI impI) (elim conjE, intro conjI)

lemma par_ABm_eq:
  assumes P: "P is PBMH_ades" and Q: "Q is PBMH_ades" and E: "nonempty_m M"
  shows "P \<parallel>\<^bsub>ABm M\<^esub> Q = P \<parallel>\<^bsub>M\<^esub> Q"
proof (rule ades_obs_ext)
  fix b s0 c Z
  have upP: "P (ades_obs b s0 okL X'')" if "P (ades_obs b s0 okL X')" "X' \<subseteq> X''" for okL X' X''
  proof -
    have "PBMH_ades P (ades_obs b s0 okL X'')"
      unfolding PBMH_ades_obs using that by (intro exI[where x=X']) simp
    then show ?thesis using P by (simp only: Healthy_def)
  qed
  have upQ: "Q (ades_obs b s0 okR Y'')" if "Q (ades_obs b s0 okR Y')" "Y' \<subseteq> Y''" for okR Y' Y''
  proof -
    have "PBMH_ades Q (ades_obs b s0 okR Y'')"
      unfolding PBMH_ades_obs using that by (intro exI[where x=Y']) simp
    then show ?thesis using Q by (simp only: Healthy_def)
  qed
  show "(P \<parallel>\<^bsub>ABm M\<^esub> Q) (ades_obs b s0 c Z) = (P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
  proof
    assume "(P \<parallel>\<^bsub>ABm M\<^esub> Q) (ades_obs b s0 c Z)"
    then obtain okL X okR Y where PX: "P (ades_obs b s0 okL X)" and QY: "Q (ades_obs b s0 okR Y)"
      and A: "ades_merge_obs (ABm M) b s0 okL X okR Y c Z"
      unfolding ades_par_by_merge_obs by blast
    from A obtain X' Y' where "X \<subseteq> X'" "Y \<subseteq> Y'" and M: "ades_merge_obs M b s0 okL X' okR Y' c Z"
      unfolding ABm_obs by blast
    with upP[OF PX] upQ[OF QY] have "P (ades_obs b s0 okL X')" "Q (ades_obs b s0 okR Y')" by simp_all
    with M show "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
      unfolding ades_par_by_merge_obs
      by (intro exI[where x=okL] exI[where x=X'] exI[where x=okR] exI[where x=Y'] conjI)
  next
    assume "(P \<parallel>\<^bsub>M\<^esub> Q) (ades_obs b s0 c Z)"
    then obtain okL X okR Y where PX: "P (ades_obs b s0 okL X)" and QY: "Q (ades_obs b s0 okR Y)"
      and M: "ades_merge_obs M b s0 okL X okR Y c Z"
      unfolding ades_par_by_merge_obs by blast
    have A: "ades_merge_obs (ABm M) b s0 okL X okR Y c Z"
      unfolding ABm_obs using nonempty_mD[OF E M] M
      by (intro conjI exI[where x=X] exI[where x=Y]) simp_all
    show "(P \<parallel>\<^bsub>ABm M\<^esub> Q) (ades_obs b s0 c Z)"
      unfolding ades_par_by_merge_obs
      by (intro exI[where x=okL] exI[where x=X] exI[where x=okR] exI[where x=Y] conjI PX QY A)
  qed
qed

(* so for up-closed operands any merge that is sound on single states,
   once made antitone by ABm, refines the shared lift *)
corollary par_lift_canonical_PBMH:
  assumes "P is PBMH_ades" "Q is PBMH_ades" "nonempty_m M" "sound_m N (ABm M)"
  shows "P \<parallel>\<^bsub>ac'_lift_merge N\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>M\<^esub> Q"
  using par_lift_canonical[OF ABm_antitone ABm_nonempty assms(4), of P Q]
  by (simp only: par_ABm_eq[OF assms(1,2,3)])

section \<open>The AD operator\<close>

(* merge_ades adds H1m and H3m around the lift; both are monotone *)
theorem ades_par_canonical:
  assumes "antitone_m M" "nonempty_m M" "sound_m (merge_des j) M"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>H3m (H1m M)\<^esub> Q"
proof -
  have "ac'_lift_merge (merge_des j) \<sqsubseteq> M" by (rule lift_greatest[OF assms])
  then have "H1m (ac'_lift_merge (merge_des j)) \<sqsubseteq> H1m M"
    by (rule H1m_Monotonic[unfolded Monotonic_refine, rule_format])
  then have "H3m (H1m (ac'_lift_merge (merge_des j))) \<sqsubseteq> H3m (H1m M)"
    by (rule H3m_Monotonic[unfolded Monotonic_refine, rule_format])
  then show ?thesis
    unfolding ades_par_def merge_ades_design_lift by (rule par_by_merge_merge_mono)
qed

end
