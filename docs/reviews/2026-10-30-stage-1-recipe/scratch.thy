theory tmp_pide_mcp_scratch_stage1_ades_recipe
  imports "UTP-Angelic-Designs.utp_ades_parallel"
begin

definition stage1_raw :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "stage1_raw j \<equiv> (\<lambda>(m,obsOut).
    let s0 = astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m));
        SL = achoices.ac\<^sub>v (des_vars.more (mrg_left\<^sub>v m));
        SR = achoices.ac\<^sub>v (des_vars.more (mrg_right\<^sub>v m));
        SOut = achoices.ac\<^sub>v (des_vars.more obsOut)
    in SL \<noteq> {} \<and> SR \<noteq> {} \<and>
       des_vars.ok\<^sub>v obsOut =
         (des_vars.ok\<^sub>v (mrg_left\<^sub>v m) \<and> des_vars.ok\<^sub>v (mrg_right\<^sub>v m)) \<and>
       (\<forall>sL\<in>SL. \<forall>sR\<in>SR. \<exists>sOut\<in>SOut. merge_eval j s0 sL sR sOut))"

lemma stage1_recipe:
  "ADH1m (stage1_raw j) ;; II\<^sub>D = merge_ades j"
  apply (simp add: stage1_raw_def merge_ades_unfold ADH1m_def Let_def)
  apply pred_auto
  by (metis UNIV_I ex_in_conv)+

definition stage1_merge :: "'s merge \<Rightarrow> 's ades_merge_rel" where
  "stage1_merge j \<equiv> ADH1m (stage1_raw j) ;; II\<^sub>D"

lemma stage1_alt:
  "stage1_merge j = ADHM (lift_merge j)"
  by (simp add: stage1_merge_def stage1_raw_def ADHM_def ADH1m_def
      ADH2m_def lift_merge_def Let_def; pred_auto; metis UNIV_I ex_in_conv)

lemma stage1_ADH1m:
  "stage1_merge j is ADH1m"
  by (simp add: Healthy_def' stage1_alt ADHM_def ADH1m_idem)

lemma stage1_ADH2m:
  "stage1_merge j is ADH2m"
  by (simp add: Healthy_def' ADH2m_def stage1_merge_def seqr_assoc skip_d_absorb_J_1)

lemma stage1_ADHM:
  "stage1_merge j is ADHM"
  by (simp add: Healthy_def' ADHM_def stage1_ADH1m[unfolded Healthy_def']
      stage1_ADH2m[unfolded Healthy_def'])

lemma stage1_completion:
  "stage1_merge j ;; II\<^sub>D = stage1_merge j"
  by (simp add: stage1_merge_def seqr_assoc)

end
