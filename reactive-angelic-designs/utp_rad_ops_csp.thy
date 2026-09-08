section \<open>Reactive Angelic Operators and CSP\<close>

theory utp_rad_ops_csp
  imports utp_rad_seq
begin

text \<open>
  The CSP operators use the same flat observation alphabet as
  \<open>rad_ac2p\<close>. Its \<open>rea_vars.more\<close> component contains the
  refusal set. The definitions below instantiate the thesis's relational
  CSP operators on this alphabet.
\<close>

subsection \<open>Prefixing\<close>

(* Thesis Definition 62. *)
definition csp_prefix_post :: "'e \<Rightarrow> ('e list, 'e set) rp_hrel" where
[pred]: "csp_prefix_post a = (\<lambda> (s, y).
  if rea_vars.wait\<^sub>v y
  then rea_vars.tr\<^sub>v y = rea_vars.tr\<^sub>v s \<and> a \<notin> rea_vars.more y
  else rea_vars.tr\<^sub>v y = rea_vars.tr\<^sub>v s @ [a])"

definition PrefixSkip_R :: "'e \<Rightarrow> ('e list, 'e set) rp_hrel" where
[pred]: "PrefixSkip_R a = \<^bold>R (true \<turnstile> csp_prefix_post a)"

lemma rad_p2ac_prefix_post:
  "rad_p2ac (csp_prefix_post a) = prefix_post a"
  by (simp add: rad_p2ac_def csp2rad_rel_def rad2csp_obs_def
      csp_prefix_post_def prefix_post_def ades_singleton_choice_def
      expr_if_def rad_state.wait_def p2ac_def fun_eq_iff;
      pred_auto)

(* Thesis Theorem T.5.4.28. *)
lemma rad_p2ac_PrefixSkip_R:
  "rad_p2ac (PrefixSkip_R a) = PrefixSkip_RAD a"
proof -
  have mapped_false: "rad_p2ac false = false"
    by (simp add: rad_p2ac_def csp2rad_rel_def; pred_auto)
  have mapped_design:
    "(ac_non_empty \<and> rad_p2ac (true \<turnstile> csp_prefix_post a)) =
     (ac_non_empty \<and> (true \<turnstile> prefix_post a))"
    using rad_p2ac_design_nonempty[where F=false and T="csp_prefix_post a"]
    by (simp only: pred_ba.compl_bot_eq mapped_false rad_p2ac_prefix_post)
  show ?thesis
    by (simp only: PrefixSkip_R_def rad_p2ac_R'
        RA_cong_ac_non_empty[OF mapped_design] PrefixSkip_RAD_RA)
qed

(* Thesis Theorem T.5.4.27. *)
lemma rad_ac2p_PrefixSkip_RAD:
  "rad_ac2p (PrefixSkip_RAD a) = PrefixSkip_R a"
  by (simp only: rad_p2ac_PrefixSkip_R[symmetric] rad_ac2p_p2ac_inverse')

subsection \<open>External choice\<close>

(* Thesis Definition 64. *)
definition csp_extchoice_post ::
  "('t::trace, 'e set) rp_hrel \<Rightarrow> ('t, 'e set) rp_hrel \<Rightarrow>
   ('t, 'e set) rp_hrel" where
[pred]: "csp_extchoice_post P Q =
  ((P \<and> Q) \<triangleleft> $rea_vars.tr\<^sup>> = $rea_vars.tr\<^sup>< \<and>
    $rea_vars.wait\<^sup>> \<triangleright> (P \<or> Q))"

definition csp_extchoice ::
  "('t::trace, 'e set) rp_hrel \<Rightarrow> ('t, 'e set) rp_hrel \<Rightarrow>
   ('t, 'e set) rp_hrel" where
[pred]: "csp_extchoice P Q = \<^bold>R
  (((\<not> wait_f (P\<^sup>f)) \<and> (\<not> wait_f (Q\<^sup>f))) \<turnstile>
   csp_extchoice_post (wait_f (P\<^sup>t)) (wait_f (Q\<^sup>t)))"

lemma rad_p2ac_extchoice_post:
  "rad_p2ac (csp_extchoice_post P Q) =
   extchoice_post (rad_p2ac P) (rad_p2ac Q)"
  by (auto simp add: csp_extchoice_post_def extchoice_post_def ades_singleton_choice_def
      rad_p2ac_def p2ac_def csp2rad_rel_def rad2csp_obs_def
      expr_if_def fun_eq_iff SEXP_def lens_defs rad_state.wait_def rad_state.tr_def
      rea_vars.tr_def rea_vars.wait_def conj_pred_def disj_pred_def
      split: prod.splits)

lemma rad_p2ac_extchoice:
  "rad_p2ac (csp_extchoice P Q) =
   rad_p2ac P \<box>\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q"
proof -
  let ?F = "wait_f (P\<^sup>f) \<or> wait_f (Q\<^sup>f)"
  let ?T = "csp_extchoice_post (wait_f (P\<^sup>t)) (wait_f (Q\<^sup>t))"
  have F_unrest: "$ok\<^sup>> \<sharp> rad_p2ac ?F"
    by (simp only: rad_p2ac_disj; simp add: unrest rad_p2ac_subst_unrest_ok)
  have T_unrest: "$ok\<^sup>> \<sharp> rad_p2ac ?T"
    by (simp only: rad_p2ac_extchoice_post;
        rule extchoice_post_unrest_ok; rule rad_p2ac_subst_unrest_ok)
  have pre: "((\<not> wait_f (P\<^sup>f)) \<and> (\<not> wait_f (Q\<^sup>f))) = (\<not> ?F)"
    by pred_auto
  have "rad_p2ac (csp_extchoice P Q) =
      (RA \<circ> A) ((\<not> rad_p2ac ?F) \<turnstile> rad_p2ac ?T)"
    by (simp only: csp_extchoice_def pre
        rad_p2ac_R_design_components[OF F_unrest T_unrest])
  also have "... = rad_p2ac P \<box>\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q"
    unfolding extchoice_RAD_def rad_p2ac_wait_false_ok
    apply (rule arg_cong[where f="RA \<circ> A"])
    by (simp only: rad_p2ac_extchoice_post rad_p2ac_disj; pred_auto)
  finally show ?thesis .
qed

(* Thesis Theorem T.5.4.32. The identity holds for arbitrary predicates
   with the Definition 64 expression above. *)
lemma RAD_extchoice_CSP:
  "rad_ac2p (rad_p2ac P \<box>\<^sub>R\<^sub>A\<^sub>D rad_p2ac Q) =
   csp_extchoice P Q"
  by (simp only: rad_p2ac_extchoice[symmetric] rad_ac2p_p2ac_inverse')

(* Thesis Theorem T.5.4.33. *)
lemma RAD_extchoice_CSP_refine:
  assumes "P is RAD" "Q is RAD"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Q \<sqsubseteq>
    rad_p2ac (csp_extchoice (rad_ac2p P) (rad_ac2p Q))"
  unfolding rad_p2ac_extchoice
  by (rule extchoice_RAD_mono;
      rule rad_p2ac_ac2p_refine'[OF RAD_is_PBMH_ades]) (fact assms)+

(* Thesis Theorem T.5.4.34. *)
lemma RAD_extchoice_CSP_A2:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "rad_p2ac (csp_extchoice (rad_ac2p P) (rad_ac2p Q)) =
    P \<box>\<^sub>R\<^sub>A\<^sub>D Q"
  by (simp only: rad_p2ac_extchoice
      rad_p2ac_ac2p_RAD_A2'[OF assms(1,3)]
      rad_p2ac_ac2p_RAD_A2'[OF assms(2,4)])

(* Thesis Theorem T.5.4.35. *)
lemma extchoice_RAD_A2_closure [closure]:
  assumes "P is RAD" "Q is RAD" "P is A2" "Q is A2"
  shows "P \<box>\<^sub>R\<^sub>A\<^sub>D Q is A2"
  by (simp only: RAD_extchoice_CSP_A2[OF assms, symmetric]
      rad_p2ac_def comp_apply Healthy_def' A2_p2ac)

end
