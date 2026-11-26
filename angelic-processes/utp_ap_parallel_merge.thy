section \<open>Angelic Process Merge Healthiness\<close>

theory utp_ap_parallel_merge
  imports utp_ap_nd "UTP-Reactive-Angelic-Designs.utp_rad_parallel_merge"
begin

text \<open>We want parallel to be closed under AP. The AD merge conditions give H1,
  H2 and A, so we only add merge conditions for RA2 and RA3AP.\<close>

subsection \<open>RA2APm and RA3APm\<close>

(* We normalise the prior trace and the three choice sets, as RA2 does for processes.
   RA2APm M((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
     M((ok,s[0/tr]),(okL,\<delta>_s ` acL),(okR,\<delta>_s ` acR),(ok',N_s(ac'))) *)
definition RA2APm :: "('t::trace, 'e) rad_merge_rel \<Rightarrow> ('t, 'e) rad_merge_rel" where
  "RA2APm M \<equiv> (\<lambda>(m,z).
    let x = mrg_prior\<^sub>v m; p = mrg_left\<^sub>v m; q = mrg_right\<^sub>v m;
        s0 = astate.s\<^sub>v (des_vars.more x)
    in ades_merge_obs M (des_vars.ok\<^sub>v x) (rad_zero_trace s0)
         (des_vars.ok\<^sub>v p) (image (rad_trace_difference s0) (achoices.ac\<^sub>v (des_vars.more p)))
         (des_vars.ok\<^sub>v q) (image (rad_trace_difference s0) (achoices.ac\<^sub>v (des_vars.more q)))
         (des_vars.ok\<^sub>v z) (rad_normalise_choices s0 (achoices.ac\<^sub>v (des_vars.more z))))"

lemma RA2APm_obs:
  "ades_merge_obs (RA2APm M) ok0 s0 okL X okR Y ok' Z =
    ades_merge_obs M ok0 (rad_zero_trace s0)
      okL (image (rad_trace_difference s0) X) okR (image (rad_trace_difference s0) Y)
      ok' (rad_normalise_choices s0 Z)"
  by (simp add: RA2APm_def Let_def)

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

lemma RA2APm_idem: "RA2APm (RA2APm M) = RA2APm M"
  by (rule ades_merge_ext; simp add: RA2APm_obs[simplified])

lemma RA3APm_idem: "RA3APm (RA3APm M) = RA3APm M"
  by (rule ades_merge_ext; simp add: RA3APm_obs[simplified])

lemma RA2APm_Idempotent [closure]: "Idempotent RA2APm"
  by (simp add: Idempotent_def RA2APm_idem)

lemma RA2APm_Monotonic [closure]: "Monotonic RA2APm"
  by (rule MonotonicI; auto simp: pred_refine_iff RA2APm_def Let_def split: prod.splits if_splits; blast)

lemma RA3APm_Idempotent [closure]: "Idempotent RA3APm"
  by (simp add: Idempotent_def RA3APm_idem)

lemma RA3APm_Monotonic [closure]: "Monotonic RA3APm"
  by (rule MonotonicI; auto simp: pred_refine_iff RA3APm_def Let_def split: prod.splits if_splits; blast)

end
