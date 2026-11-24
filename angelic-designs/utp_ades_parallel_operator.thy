section \<open>AD Parallel\<close>

theory utp_ades_parallel_operator
  imports utp_ades_parallel_lifted_merge
begin

text \<open>The AD parallel operator: definition, evaluation, closure, correspondence with
  designs, and canonicity.\<close>

subsection \<open>Definition and Evaluation\<close>

definition ades_par ::
  "'s angelic_design \<Rightarrow> 's merge \<Rightarrow> 's angelic_design \<Rightarrow> 's angelic_design"
  ("_ \<parallel>\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^bsub>merge_ades j\<^esub> Q"

text \<open>H1 handles unstarted observations; A2 reduces nonempty branch sets to singleton witnesses.\<close>

lemma ades_par_obs_A2:
  fixes P Q :: "'s angelic_design"
  assumes "P is A2" "Q is A2" "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not>ok0 \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> (\<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
proof -
  have pick: "\<exists>x\<in>X. R (ades_obs True s0 okL {x})"
    if "R is A2" "X \<noteq> {}" "R (ades_obs True s0 okL X)" for R :: "'s angelic_design" and okL X
  proof -
    have "R (ades_obs True s0 okL Y) \<longleftrightarrow>
        R (ades_obs True s0 okL {}) \<or> (\<exists>y\<in>Y. R (ades_obs True s0 okL {y}))" for Y
      using A2_obs[of R True s0 okL Y] by (simp only: Healthy_if[OF that(1)])
    then show ?thesis
      using that(2,3) by blast
  qed
  show ?thesis
    apply (cases ok0; simp add: ades_par_def par_by_merge_eval choices_ex merge_ades_obs[simplified]
        assms(3,4)[unfolded H1_healthy_obs_iff])
    apply (rule iffI)
    subgoal using pick[OF assms(1)] pick[OF assms(2)] by metis
    subgoal by (fastforce intro: exI[where x="{_}"])
    done
qed

lemma ades_par_obs:
  fixes P Q :: "'s angelic_design"
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<not> ok0 \<or> (\<exists>okL sL okR sR.
      P (ades_obs True s0 okL {sL}) \<and> Q (ades_obs True s0 okR {sR}) \<and>
      (\<exists>s'. merge_eval j s0 sL sR s') \<and>
      (okL \<and> okR \<longrightarrow> (ok' \<and> (\<exists>s'\<in>ac'. merge_eval j s0 sL sR s')))))"
proof -
  have operands_H1: "P is H1" "Q is H1"
    using assms(1,2) by (simp_all add: A_healthy_components_iff)
  show ?thesis
    by (rule ades_par_obs_A2[OF assms(3,4) operands_H1])
qed

lemma ades_par_normalise_A:
  assumes "P is A2" "Q is A2" "P is H1" "Q is H1"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = A P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> A Q"
  by (rule ades_obs_ext;
      simp add: ades_par_obs_A2[OF assms]
        ades_par_obs_A2[OF A_preserves_A2[OF assms(1)] A_preserves_A2[OF assms(2)] A_is_H1[folded Healthy_def'] A_is_H1[folded Healthy_def']]
        A_obs_A2[OF assms(1)] A_obs_A2[OF assms(2)] ex_bool_eq; blast)

lemma ades_par_eval:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR.
      P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      (\<not>ok0 \<or> (acL \<noteq> {} \<and> acR \<noteq> {} \<and>
        (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'. merge_eval j s0 sL sR s') \<and>
        (okL \<and> okR \<longrightarrow> (ok' \<and>
          (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'. merge_eval j s0 sL sR s'))))))"
  by (simp add: ades_par_def
      par_by_merge_eval choices_ex merge_ades_obs[simplified])

subsection \<open>Healthiness Closure\<close>

lemma ades_par_A0_closure [closure]:
  "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A0"
  unfolding ades_par_def
  by (rule A0_par_by_merge[OF merge_ades_is_A0m])

lemma ades_par_A1_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A1"
  unfolding ades_par_def
  by (rule A1_par_by_merge[OF assms merge_ades_is_A1m])

lemma ades_par_A_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A"
  unfolding ades_par_def
  by (rule A_par_by_merge[OF assms merge_ades_is_ADm])

lemma ades_par_A2_closure [closure]:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  unfolding ades_par_def
  by (rule A2_par_by_merge[OF assms merge_ades_is_A2m])

lemma ades_par_A3_closure [closure]:
  assumes "P is H1" "Q is H1"
  shows "(P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A3"
  unfolding ades_par_def
  by (rule A3_par_by_merge[OF assms merge_ades_is_H1m merge_ades_is_H3m])

subsection \<open>Correspondence with Designs\<close>

text \<open>For A- and A2-healthy operands, ac2p and d2ac preserve parallel by the
  lift of an HDm- and H3m-healthy design merge.\<close>

lemma ades_par_d2ac_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q = d2ac ((ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q))"
  unfolding ades_par_def merge_ades_design_lift
  by (rule ades_par_by_merge_d2ac_ac2p[OF assms merge_des_is_HDm merge_des_is_H3m refl])

lemma ades_par_d2ac:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(d2ac P) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac Q) = d2ac (P \<parallel>\<^sub>D\<^bsub>j\<^esub> Q)"
  by (simp only: ades_par_d2ac_ac2p[OF d2ac_is_A d2ac_is_A d2ac_is_A2 d2ac_is_A2]
      ac2p_d2ac[OF assms(1), simplified comp_apply]
      ac2p_d2ac[OF assms(2), simplified comp_apply])

lemma ades_par_ac2p:
  assumes "P is A" "Q is A" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) = (ac2p P) \<parallel>\<^sub>D\<^bsub>j\<^esub> (ac2p Q)"
  unfolding ades_par_def
  by (rule ades_par_by_merge_ac2p[OF assms merge_des_is_HDm merge_des_is_H3m merge_ades_design_lift])

lemma ades_par_ac2p_d2ac:
  assumes "D is \<^bold>H" "E is \<^bold>H"
  shows "D \<parallel>\<^sub>D\<^bsub>j\<^esub> E = ac2p ((d2ac D) \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> (d2ac E))"
  by (simp only: ades_par_d2ac[OF assms]
      ac2p_d2ac[OF des_par_H_closure[OF H_implies_H1[OF assms(1)] H_implies_H1[OF assms(2)]], simplified comp_apply])

subsection \<open>Canonicity\<close>

(* P \<parallel>\<^sub>A\<^sub>D[j] Q \<sqsubseteq> P \<parallel>[H3m (H1m M)] Q *)
theorem ades_par_canonical:
  assumes "M is ABm" "singleton_refines (merge_des j) M"
  shows "P \<parallel>\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>H3m (H1m M)\<^esub> Q"
proof -
  have "ABm (ac'_lift_merge (merge_des j)) \<sqsubseteq> M"
    by (rule choice_lift_least[OF assms])
  then have "H1m (ABm (ac'_lift_merge (merge_des j))) \<sqsubseteq> H1m M"
    by (rule H1m_Monotonic[unfolded Monotonic_refine, rule_format])
  then have "H3m (H1m (ABm (ac'_lift_merge (merge_des j)))) \<sqsubseteq> H3m (H1m M)"
    by (rule H3m_Monotonic[unfolded Monotonic_refine, rule_format])
  then show ?thesis
    unfolding ades_par_def merge_ades_design_lift by (rule par_by_merge_mono_merge)
qed

end
