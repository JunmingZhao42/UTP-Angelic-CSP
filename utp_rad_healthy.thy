section \<open>Reactive Angelic Healthiness Conditions\<close>

theory utp_rad_healthy
  imports utp_rad_bridge
begin

subsection \<open>Trace extension (Paper Definitions 27 and 28)\<close>

definition rad_trace_extensions :: "'e rad_state \<Rightarrow> 'e rad_state set" where
"rad_trace_extensions x =
  {z. rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v z}"

definition RA1 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where
"RA1 P = (\<lambda> (x, y).
  let s0 = get\<^bsub>s\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> x);
      A = get\<^bsub>ac\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> y);
      A' = rad_trace_extensions s0 \<inter> A;
      y' = put\<^bsub>\<^bold>v\<^sub>D\<^esub> y
        (put\<^bsub>ac\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> y) A')
  in P (x, y') \<and> A' \<noteq> {})"

lemma RA1_idem: "RA1 (RA1 P) = RA1 P"
  by (simp add: RA1_def rad_trace_extensions_def fun_eq_iff; blast)

lemma RA1_Idempotent: "Idempotent RA1"
  by (simp add: Idempotent_def RA1_idem)

lemma RA1_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA1 P \<sqsubseteq> RA1 Q"
  by (auto simp add: RA1_def pred_refine_iff Let_def split: prod.splits)

lemma RA1_Monotonic [closure]: "Monotonic RA1"
  by (rule MonotonicI, rule RA1_mono)

subsection \<open>Trace-history independence (Paper Definition 29)\<close>

definition rad_zero_trace :: "'e rad_state \<Rightarrow> 'e rad_state" where
"rad_zero_trace x = put\<^bsub>rad_state.tr\<^esub> x []"

definition rad_trace_difference ::
  "'e rad_state \<Rightarrow> 'e rad_state \<Rightarrow> 'e rad_state"
where
"rad_trace_difference x z =
  put\<^bsub>rad_state.tr\<^esub> z (rad_state.tr\<^sub>v z - rad_state.tr\<^sub>v x)"

definition rad_normalise_choices ::
  "'e rad_state \<Rightarrow> 'e rad_state set \<Rightarrow> 'e rad_state set"
where
"rad_normalise_choices x choices =
  {rad_trace_difference x z | z.
    z \<in> choices \<and> rad_state.tr\<^sub>v x \<le> rad_state.tr\<^sub>v z}"

definition RA2 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where
"RA2 P = (\<lambda> (x, y).
  let s0 = get\<^bsub>s\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> x);
      A = get\<^bsub>ac\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> y);
      x' = put\<^bsub>\<^bold>v\<^sub>D\<^esub> x
        (put\<^bsub>s\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> x) (rad_zero_trace s0));
      y' = put\<^bsub>\<^bold>v\<^sub>D\<^esub> y
        (put\<^bsub>ac\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> y)
          (rad_normalise_choices s0 A))
  in P (x', y'))"

lemma RA2_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA2 P \<sqsubseteq> RA2 Q"
  by (auto simp add: RA2_def pred_refine_iff Let_def split: prod.splits)

lemma RA2_Monotonic [closure]: "Monotonic RA2"
  by (rule MonotonicI, rule RA2_mono)

subsection \<open>Reactive identity and waiting (Paper Definitions 30 and 31)\<close>

definition II_Rac :: "'e reactive_angelic_design" where
"II_Rac = (\<lambda> (x, y).
  let s0 = get\<^bsub>s\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> x);
      A = get\<^bsub>ac\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> y)
  in RA1 (\<lambda> (x, y). \<not> ok\<^sub>v x) (x, y) \<or> (ok\<^sub>v x \<and> s0 \<in> A))"

definition RA3 ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where
"RA3 P = (\<lambda> (x, y).
  if rad_state.wait\<^sub>v
      (get\<^bsub>s\<^esub> (get\<^bsub>\<^bold>v\<^sub>D\<^esub> x))
  then II_Rac (x, y)
  else P (x, y))"

lemma RA3_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA3 P \<sqsubseteq> RA3 Q"
  by (simp add: RA3_def, pred_auto)

lemma RA3_Monotonic [closure]: "Monotonic RA3"
  by (rule MonotonicI, rule RA3_mono)

subsection \<open>Reactive angelic healthiness (Paper Definition 32)\<close>

definition RA ::
  "'e reactive_angelic_design \<Rightarrow> 'e reactive_angelic_design"
where
"RA = RA1 \<circ> RA2 \<circ> RA3"

lemma RA_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RA P \<sqsubseteq> RA Q"
  by (simp add: RA_def RA1_mono RA2_mono RA3_mono)

lemma RA_Monotonic [closure]: "Monotonic RA"
  unfolding RA_def
  by (intro Monotonic_comp RA1_Monotonic RA2_Monotonic RA3_Monotonic)

end
