section \<open>Angelic Process Merge Healthiness\<close>

theory utp_ap_parallel_merge
  imports utp_ap_nd "UTP-Reactive-Angelic-Designs.utp_rad_parallel_merge"
begin

text \<open>We want parallel to be closed under AP. The AD merge conditions give H1,
  H2 and A, and the RAD condition RA2APm gives RA2, so we only add a merge
  condition for RA3AP.\<close>

subsection \<open>RA3APm\<close>

(* While waiting, the merge is the AP skip, as RA3AP P = II_AP \<triangleleft> s.wait \<triangleright> P *)
definition RA3APm :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RA3APm M \<equiv> (\<lambda>(m,z).
    if rad_wait\<^sub>v (astate.s\<^sub>v (des_vars.more (mrg_prior\<^sub>v m)))
    then II_AP (mrg_prior\<^sub>v m, z) else M (m,z))"

lemma RA3APm_obs:
  "ades_merge_obs (RA3APm M) ok0 s0 okL X okR Y ok' Z =
    (if rad_wait\<^sub>v s0 then II_AP (ades_obs ok0 s0 ok' Z)
     else ades_merge_obs M ok0 s0 okL X okR Y ok' Z)"
  by (simp add: RA3APm_def)

lemma RA3APm_idem: "RA3APm (RA3APm M) = RA3APm M"
  by (rule ades_merge_ext; simp add: RA3APm_obs[simplified])

lemma RA3APm_Idempotent [closure]: "Idempotent RA3APm"
  by (simp add: Idempotent_def RA3APm_idem)

lemma RA3APm_Monotonic [closure]: "Monotonic RA3APm"
  by (rule MonotonicI; auto simp: pred_refine_iff RA3APm_def Let_def split: prod.splits if_splits; blast)

end
