section \<open>Angelic Process Parallel\<close>

theory utp_ap_parallel_operator
  imports utp_ap_parallel_lifted_merge
begin

subsection \<open>Definition\<close>

(* P \<parallel>\<^sub>A\<^sub>P[j] Q = P \<parallel>[merge_ap j] Q *)
abbreviation ap_par ::
  "('t::trace, 'e) angelic_process \<Rightarrow> ('t \<times> 'e set) merge \<Rightarrow>
   ('t, 'e) angelic_process \<Rightarrow> ('t, 'e) angelic_process"
  ("_ \<parallel>\<^sub>A\<^sub>P\<^bsub>_\<^esub> _" [85,0,86] 85)
where
  "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q \<equiv> P \<parallel>\<^bsub>merge_ap j\<^esub> Q"

subsection \<open>Closure\<close>

text \<open>Closure needs no A2 premise and no premise on j.\<close>

lemma ap_par_AP [closure]:
  assumes "P is AP" "Q is AP"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) is AP"
  by (rule ap_par_by_merge_AP[OF assms merge_ap_H1m merge_ap_H2m merge_ap_ADm
        merge_ap_RA2APm merge_ap_RA3APm])

lemma ap_par_A2 [closure]:
  assumes "P is A2" "Q is A2"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) is A2"
  by (rule A2_par_by_merge[OF assms merge_ap_A2m])

lemma ap_par_NDAP [closure]:
  assumes ap: "P is AP" "Q is AP" and nd: "P is NDAP" "Q is NDAP"
  shows "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) is NDAP"
proof -
  let ?R = "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q"
  have R: "?R is AP" by (rule ap_par_AP[OF ap])
  have choice: "Choice\<^sub>A\<^sub>P (ades_obs ok0 s0 c Z)" if r: "?R (ades_obs ok0 s0 c Z)" for ok0 s0 c Z
  proof (cases ok0)
    case False
    then show ?thesis using AP_unstarted_obs[OF Choice_AP_is_AP] by simp
  next
    case True
    show ?thesis
    proof (cases "rad_wait\<^sub>v s0")
      case wait: True
      then show ?thesis
        using r AP_wait_obs[OF R wait] AP_wait_obs[OF Choice_AP_is_AP wait] by simp
    next
      case act: False
      obtain okL X okR Y where p: "P (ades_obs True s0 okL X)" and q: "Q (ades_obs True s0 okR Y)"
          and m: "ades_merge_obs (merge_ap j) True s0 okL X okR Y c Z"
        using r True by (simp only: simp_thms) (unfold ades_par_by_merge_obs, blast)
      have ok: "okL" "okR"
        using NDAP_active_obs[OF nd(1) p act] NDAP_active_obs[OF nd(2) q act] by simp_all
      have "c \<and> rad_trace_extensions s0 \<inter> Z \<noteq> {}"
        by (rule merge_ap_active_ok[OF act]) (use m ok in simp)
      moreover have "Choice\<^sub>A\<^sub>P (ades_obs True s0 True Z)" if "rad_trace_extensions s0 \<inter> Z \<noteq> {}"
        using act that by (simp add: Choice_AP_design RA1_obs; pred_auto)
      ultimately show ?thesis using True by simp
    qed
  qed
  show ?thesis
    by (rule Healthy_intro, rule ades_obs_ext) (use choice in \<open>auto simp: NDAP_def inf_fun_def\<close>)
qed

subsection \<open>Comparison with RAD\<close>

text \<open>We relate AP parallel to RAD parallel as the paper relates the sequential
  compositions (Theorems 61 to 63): P \<parallel> Q \<sqsubseteq> H1 (RA1 P \<parallel> RA1 Q), with equality
  for nondivergent operands.\<close>

(* P \<parallel>AP[j] Q \<sqsubseteq> H1 (RA1 P \<parallel>RAD[j] RA1 Q) *)
theorem ap_par_rad_refine:
  fixes P Q :: "('t::trace, 'e) angelic_process"
  assumes "P is AP" "Q is AP"
  shows "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q \<sqsubseteq> H1 (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q)"
proof -
  have refine: "M \<sqsubseteq> N"
    if "\<And>ok0 s0 okL X okR Y ok' Z. ades_merge_obs N ok0 s0 okL X okR Y ok' Z \<Longrightarrow>
      ades_merge_obs M ok0 s0 okL X okR Y ok' Z"
    for M N :: "('t, 'e) rad_merge_rel"
    unfolding pred_refine_iff using that by pred_auto
  have "merge_ap j \<sqsubseteq> merge_rad j"
  proof (rule refine)
    fix ok0 s0 okL X okR Y ok' Z
    assume h: "ades_merge_obs (merge_rad j) ok0 s0 okL X okR Y ok' Z"
    show "ades_merge_obs (merge_ap j) ok0 s0 okL X okR Y ok' Z"
    proof (cases "ok0 \<and> rad_wait\<^sub>v s0")
      case True
      obtain sL sR s' where "s' \<in> Z" and
        m: "merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = okL, \<dots> = sL\<rparr>
            \<lparr>ok\<^sub>v = okR, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = ok', \<dots> = s'\<rparr>"
        using h True by (simp only: ac'_lift_merge_obs simp_thms ex_in_conv[symmetric]; blast)
      moreover have "ok' \<and> s' = s0"
        using m True by (cases s0; simp add: merge_rdes_eval)
      ultimately show ?thesis
        using True by (simp only: merge_ap_obs if_True simp_thms; blast)
    next
      case False
      then show ?thesis
        using h by (cases ok0; cases "rad_wait\<^sub>v s0";
            simp only: merge_ap_obs ac'_lift_merge_obs if_True if_False simp_thms; blast)
    qed
  qed
  then have "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q \<sqsubseteq> RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q"
    by (rule par_by_merge_mono[OF RA1_refine[OF AP_is_PBMH_ades[OF assms(1)]]
          RA1_refine[OF AP_is_PBMH_ades[OF assms(2)]]])
  then have "H1 (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) \<sqsubseteq> H1 (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q)"
    by (rule H1_monotone)
  then show ?thesis
    by (simp only: Healthy_if[OF H1_par_by_merge[OF H_implies_H1[OF AP_is_H[OF assms(1)]]
          H_implies_H1[OF AP_is_H[OF assms(2)]] merge_ap_H1m]])
qed

(* P \<parallel>AP[j] Q = H1 (RA1 P \<parallel>RAD[j] RA1 Q) for nondivergent operands *)
theorem ap_par_rad_NDAP:
  fixes P Q :: "('t::trace, 'e) angelic_process"
  assumes ap: "P is AP" "Q is AP" and nd: "P is NDAP" "Q is NDAP"
  shows "P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q = H1 (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q)"
proof -
  have refine: "S \<sqsubseteq> T" if "\<And>b s0 c X. T (ades_obs b s0 c X) \<Longrightarrow> S (ades_obs b s0 c X)"
    for S T :: "('t, 'e) angelic_process"
    unfolding pred_refine_iff using that by pred_auto
  (* RA2 lets us drop the choices that do not extend the prior trace *)
  have ext: "S (ades_obs b s0 c (rad_trace_extensions s0 \<inter> X)) = S (ades_obs b s0 c X)"
    if "S is RA2" for S :: "('t, 'e) angelic_process" and b s0 c X
  proof -
    have "RA2 S (ades_obs b s0 c (rad_trace_extensions s0 \<inter> X)) = RA2 S (ades_obs b s0 c X)"
      by (simp only: RA2_obs' rad_normalise_choices_extensions)
    then show ?thesis by (simp only: Healthy_if[OF that])
  qed
  have converse: "H1 (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q) \<sqsubseteq> P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q"
  proof (rule refine)
    fix ok0 s0 c Z
    assume r: "(P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) (ades_obs ok0 s0 c Z)"
    show "H1 (RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q) (ades_obs ok0 s0 c Z)"
    proof (cases ok0)
      case False
      then show ?thesis by (simp add: H1_obs)
    next
      case True
      show ?thesis
      proof (cases "rad_wait\<^sub>v s0")
        case wait: True
        have cz: "c \<and> s0 \<in> Z"
          using r True AP_wait_obs[OF ap_par_AP[OF ap] wait] by simp
        have p: "RA1 P (ades_obs True s0 True {s0})" "RA1 Q (ades_obs True s0 True {s0})"
          using AP_wait_obs[OF ap(1) wait] AP_wait_obs[OF ap(2) wait]
          by (simp_all add: RA1_obs rad_trace_extensions_def)
        have m: "merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr>
            \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s0\<rparr>"
          using cz wait by (simp add: merge_rdes_eval)
        show ?thesis
          unfolding H1_obs rad_par_eval
          by (rule disjI2, rule exI[of _ True], rule exI[of _ "{s0}"], rule exI[of _ True],
              rule exI[of _ "{s0}"]) (use True p m cz in auto)
      next
        case act: False
        obtain okL X okR Y where p: "P (ades_obs True s0 okL X)" and q: "Q (ades_obs True s0 okR Y)"
            and m: "ades_merge_obs (merge_ap j) True s0 okL X okR Y c Z"
          using r True by (simp only: simp_thms) (unfold ades_par_by_merge_obs, blast)
        have okp: "okL \<and> rad_trace_extensions s0 \<inter> X \<noteq> {}" by (rule NDAP_active_obs[OF nd(1) p act])
        have okq: "okR \<and> rad_trace_extensions s0 \<inter> Y \<noteq> {}" by (rule NDAP_active_obs[OF nd(2) q act])
        have lift: "X \<noteq> {} \<and> Y \<noteq> {} \<and> (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>s'\<in>Z.
            merge_eval (merge_rdes j) \<lparr>ok\<^sub>v = True, \<dots> = s0\<rparr> \<lparr>ok\<^sub>v = True, \<dots> = sL\<rparr>
              \<lparr>ok\<^sub>v = True, \<dots> = sR\<rparr> \<lparr>ok\<^sub>v = c, \<dots> = s'\<rparr>)"
          using m okp okq by (simp only: merge_ap_both_ok[OF act] simp_thms; blast)
        have rp: "RA1 P (ades_obs True s0 True X)" "RA1 Q (ades_obs True s0 True Y)"
          using p q okp okq ext[OF AP_is_RA2[OF ap(1)]] ext[OF AP_is_RA2[OF ap(2)]]
          by (simp_all add: RA1_obs)
        show ?thesis
          unfolding H1_obs rad_par_eval
          by (rule disjI2, rule exI[of _ True], rule exI[of _ X], rule exI[of _ True],
              rule exI[of _ Y]) (use True rp lift in auto)
      qed
    qed
  qed
  show ?thesis
    using antisym[OF converse[unfolded ref_by_pred_is_leq]
        ap_par_rad_refine[OF ap, unfolded ref_by_pred_is_leq]] .
qed

lemma ap_par_RA1:
  assumes "P is AP" "Q is AP" "P is NDAP" "Q is NDAP"
  shows "RA1 (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q) = RA1 P \<parallel>\<^sub>R\<^sub>A\<^sub>D\<^bsub>j\<^esub> RA1 Q"
  by (simp only: ap_par_rad_NDAP[OF assms],
      rule RA1_H1_RAD_healthy[simplified comp_apply],
      rule rad_par_RAD[OF RA1_AP_RAD_closure[OF assms(1)] RA1_AP_RAD_closure[OF assms(2)]])

lemma ap_par_ac2p:
  assumes "P is AP" "Q is AP" "P is NDAP" "Q is NDAP" "P is A2" "Q is A2"
  shows "ac2p (RA1 (P \<parallel>\<^sub>A\<^sub>P\<^bsub>j\<^esub> Q)) = ac2p (RA1 P) \<parallel>\<^sub>R\<^sub>D\<^bsub>j\<^esub> ac2p (RA1 Q)"
  unfolding ap_par_RA1[OF assms(1-4)]
  by (rule rad_par_ac2p; simp add: assms RA1_AP_RAD_closure RA1_A2_closure)

end
