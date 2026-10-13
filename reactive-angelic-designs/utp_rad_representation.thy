section \<open>RAD representation regression\<close>

theory utp_rad_representation
  imports utp_rad_parallel
begin

text \<open>This audit reproduces the former inner record and observation adapter.
  It checks the change of representation independently of the retained RAD laws.\<close>

record ('t, 'e) legacy_rad_state =
  legacy_tr :: 't
  legacy_ref :: "'e set"
  legacy_wait :: bool

definition encode_rad :: "('t::trace, 'e) legacy_rad_state \<Rightarrow> ('t, 'e) rad_state" where
  "encode_rad x = rea_vars_ext (legacy_wait x) (legacy_tr x) (legacy_ref x)"

definition decode_rad :: "('t::trace, 'e) rad_state \<Rightarrow> ('t, 'e) legacy_rad_state" where
  "decode_rad x = \<lparr>legacy_tr = rad_tr\<^sub>v x, legacy_ref = rad_ref\<^sub>v x,
    legacy_wait = rad_wait\<^sub>v x\<rparr>"

lemma decode_encode_rad [simp]: "decode_rad (encode_rad x) = x"
  by (cases x) (simp add: encode_rad_def decode_rad_def)

lemma encode_decode_rad [simp]: "encode_rad (decode_rad x) = x"
  by (cases x) (simp add: encode_rad_def decode_rad_def)

lemma encode_rad_inj: "inj encode_rad"
  by (rule injI; metis decode_encode_rad)

lemma encode_rad_choices [simp]: "encode_rad ` (decode_rad ` X) = X"
  by (simp add: image_image)

lemma encode_rad_trace_update:
  "encode_rad (legacy_tr_update f x) = rad_tr\<^sub>v_update f (encode_rad x)"
  by (cases x) (simp add: encode_rad_def)

lemma encode_rad_wait_update:
  "encode_rad (legacy_wait_update f x) = rad_wait\<^sub>v_update f (encode_rad x)"
  by (cases x) (simp add: encode_rad_def)

definition legacy_obs ::
  "('t::trace, 'e) legacy_rad_state des_vars_scheme \<Rightarrow> ('t, 'e set) rp" where
  "legacy_obs x = \<lparr>ok\<^sub>v = ok\<^sub>v x,
    rea_vars.wait\<^sub>v = legacy_wait (des_vars.more x),
    rea_vars.tr\<^sub>v = legacy_tr (des_vars.more x),
    \<dots> = legacy_ref (des_vars.more x)\<rparr>"

definition legacy_rel where
  "legacy_rel D = (\<lambda>(x,y). D (legacy_obs x, legacy_obs y))"

definition legacy_view ::
  "('t::trace, 'e) reactive_angelic_design \<Rightarrow>
   ('t, 'e) legacy_rad_state angelic_design" where
  "legacy_view P = (\<lambda>(x,y). P (ades_obs (ok\<^sub>v x)
    (encode_rad (astate.s\<^sub>v (des_vars.more x))) (ok\<^sub>v y)
    (encode_rad ` achoices.ac\<^sub>v (des_vars.more y))))"

lemma legacy_view_obs [simp]:
  "legacy_view P (ades_obs b s0 c X) = P (ades_obs b (encode_rad s0) c (encode_rad ` X))"
  by (simp add: legacy_view_def)

lemma legacy_p2ac_agrees:
  "legacy_view (p2ac D) = p2ac (legacy_rel D)"
  by (simp add: legacy_view_def p2ac_def legacy_rel_def
      legacy_obs_def encode_rad_def fun_eq_iff; pred_auto)

lemma legacy_ac2p_agrees:
  "ac2p (legacy_view P) = legacy_rel (ac2p P)"
  apply (simp only: ac2p_subset )
  apply (simp add: legacy_view_def legacy_rel_def legacy_obs_def
      encode_rad_def fun_eq_iff StateII_def subset_singleton_iff)
  apply pred_auto
  subgoal by (rule exI[of _ "{}"]) simp
  subgoal for x y by (rule exI[of _ "{des_vars.more y}"]) simp
  done


definition legacy_lift_merge ::
  "('t::trace, 'e set) rp merge \<Rightarrow> (('t, 'e) legacy_rad_state) ades_merge_rel"
where
  "legacy_lift_merge M = (\<lambda>(m,out).
    let x = mrg_prior\<^sub>v m;
        p = mrg_left\<^sub>v m;
        q = mrg_right\<^sub>v m;
        X = achoices.ac\<^sub>v (des_vars.more p);
        Y = achoices.ac\<^sub>v (des_vars.more q);
        Z = achoices.ac\<^sub>v (des_vars.more out);
        s0 = astate.s\<^sub>v (des_vars.more x)
    in X \<noteq> {} \<and> Y \<noteq> {} \<and>
      (\<forall>sL\<in>X. \<forall>sR\<in>Y. \<exists>sOut\<in>Z.
        merge_eval M
          (legacy_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v x, \<dots> = s0\<rparr>)
          (legacy_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v p, \<dots> = sL\<rparr>)
          (legacy_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v q, \<dots> = sR\<rparr>)
          (legacy_obs \<lparr>ok\<^sub>v = des_vars.ok\<^sub>v out, \<dots> = sOut\<rparr>)))"


lemma legacy_merge_agrees:
  "ades_merge_obs (legacy_lift_merge M) b s0 c X d Y e Z =
   ades_merge_obs (rad_lift_merge M) b (encode_rad s0)
     c (encode_rad ` X) d (encode_rad ` Y) e (encode_rad ` Z)"
  by (simp add: legacy_lift_merge_def rad_lift_merge_def legacy_obs_def
      encode_rad_def Let_def)

lemma legacy_choices_ex:
  "(\<exists>X :: ('t::trace, 'e) rad_state set. F X) =
   (\<exists>X :: ('t, 'e) legacy_rad_state set. F (encode_rad ` X))"
  by (metis encode_rad_choices)

lemma legacy_raw_parallel_agrees:
  "legacy_view (P \<parallel>\<^bsub>rad_lift_merge M\<^esub> Q) =
   (legacy_view P \<parallel>\<^bsub>legacy_lift_merge M\<^esub> legacy_view Q)"
  apply (rule ades_obs_ext)
  apply (simp only: legacy_view_obs ades_par_by_merge_eval choices_ex legacy_choices_ex
      legacy_merge_agrees[simplified])
  done

end
