section \<open>RAD Parallel\<close>

theory utp_rad_parallel_operator
  imports utp_rad_parallel_lifted_merge
begin

subsection \<open>RAD parallel by merge\<close>

lemma rad_lift_par_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
  shows "p2ac P \<parallel>\<^bsub>rad_lift_merge M\<^esub> p2ac Q = p2ac (P \<parallel>\<^bsub>M\<^esub> Q)"
  apply (rule ades_obs_ext)
  apply (simp only: rad_p2ac_obs par_by_merge_eval
      choices_ex rad_lift_merge_obs[simplified])
  apply (simp only: des_vars.splits)
  by (blast intro: exI[where x="{_}"])

lemma rad_par_by_merge_form:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
    and "AM = rad_lift_merge M"
  shows "P \<parallel>\<^bsub>AM\<^esub> Q =
    p2ac (ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q)"
  using rad_lift_par_p2ac[where P="ac2p P" and Q="ac2p Q" and M=M]
  by (simp only: assms(5) rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

lemma rad_par_by_merge_ac2p:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
    and "AM = rad_lift_merge M"
  shows "ac2p (P \<parallel>\<^bsub>AM\<^esub> Q) =
    ac2p P \<parallel>\<^bsub>M\<^esub> ac2p Q"
  by (simp only: rad_par_by_merge_form[OF assms] rad_ac2p_p2ac_inverse')

(* merge_rad j = rad_lift_merge (merge_rdes j) *)
abbreviation merge_rad :: "('t::trace \<times> 'e set) merge \<Rightarrow> ('t, 'e) rad_merge_rel"
  where "merge_rad j \<equiv> rad_lift_merge (merge_rdes j)"

(* P \<parallel>\<^sub>R\<^sub>A\<^sub>D[j] Q = P \<parallel>[merge_rad j] Q. *)
abbreviation rad_par_lift ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow> ('t \<times> 'e set) merge \<Rightarrow>
    ('t, 'e) reactive_angelic_design \<Rightarrow> ('t, 'e) reactive_angelic_design"
  ("_ \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<equiv>
    P \<parallel>\<^bsub>merge_rad j\<^esub> Q"

lemma rad_par_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
    and j :: "('t \<times> 'e set) merge"
  shows "p2ac P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> p2ac Q =
    p2ac (P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q)"
  by (rule rad_lift_par_p2ac)

lemma rad_par_form:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q =
    p2ac (ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p Q)"
  by (rule rad_par_by_merge_form[OF assms refl])

(* (P \<parallel> Q)(x,z) holds when some branch observations, with nonempty sets, merge into z *)
lemma rad_par_eval:
  "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 ok' ac') \<longleftrightarrow>
    (\<exists>okL acL okR acR.
      P (ades_obs ok0 s0 okL acL) \<and> Q (ades_obs ok0 s0 okR acR) \<and>
      acL \<noteq> {} \<and> acR \<noteq> {} \<and>
      (\<forall>sL\<in>acL. \<forall>sR\<in>acR. \<exists>s'\<in>ac'.
        merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = ok0, \<dots> = s0\<rparr>
          \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
          \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr>
          \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>))"
  by (simp add: par_by_merge_eval choices_ex rad_lift_merge_obs[simplified])

lemma rad_par_ac2p:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "ac2p (P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) =
    ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p Q"
  by (rule rad_par_by_merge_ac2p[OF assms refl])

lemma rad_par_ac2p_p2ac:
  fixes P Q :: "('t::trace, 'e set) rp_hrel"
    and j :: "('t \<times> 'e set) merge"
  shows "P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> Q =
    ac2p (p2ac P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> p2ac Q)"
  by (simp only: rad_par_p2ac rad_ac2p_p2ac_inverse')

lemma rad_par_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is A2"
  by (simp add: rad_par_form[OF assms] Healthy_def')

lemma rad_par_RAD [closure]:
  assumes "P is RAD" "Q is RAD"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is RAD"
  by (rule rad_par_by_merge_RAD[OF assms rad_lift_merge_RADm[OF merge_rdes_ORDm]])

lemma rad_par_NDRAD [closure]:
  assumes rad: "P is RAD" "Q is RAD"
      and a2: "P is A2" "Q is A2"
      and nondiv: "P is NDRAD" "Q is NDRAD"
  shows "(P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q) is NDRAD"
proof -
  have rd: "ac2p P is RD" "ac2p Q is RD"
    using rad a2 by (blast intro: rad_ac2p_RD)+
  have nd: "ac2p P is NDRD" "ac2p Q is NDRD"
    using rad a2 nondiv by (blast intro: rad_ac2p_NDRD)+
  have "(ac2p P \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p Q) is NDRD"
    by (rule rdes_lift_parallel_NDRD[OF rd nd])
  from rad_p2ac_NDRAD[OF this] show ?thesis
    by (simp only: rad_par_form[OF rad a2])
qed

subsection \<open>Canonicity\<close>

(* P \<parallel>\<^sub>R\<^sub>A\<^sub>D[j] Q \<sqsubseteq> P \<parallel>[M] Q *)
theorem rad_par_canonical:
  assumes "M is ABm" "singleton_refines (merge_rdes j) M"
  shows "P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> Q \<sqsubseteq> P \<parallel>\<^bsub>M\<^esub> Q"
  unfolding rad_lift_merge_def comp_apply
  by (rule par_choice_lift_canonical[OF assms])

end
