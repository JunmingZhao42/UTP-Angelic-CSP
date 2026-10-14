# Reactive angelic designs

[Paper coverage](README.md) · [AD](AD.md) · [AP](AP.md)

Paper §6 and Appendix A; thesis Chapter 5 and Appendix G.

[Alphabet](#alphabet-and-notation) · [§6.1 Healthiness](#61-healthiness-conditions) · [§6.2 RAD](#62-reactive-angelic-designs) · [§6.3 CSP correspondence](#63-relationship-with-csp) · [§6.4 Operators](#64-operators) · [§6.5 Non-divergence](#65-non-divergent-reactive-angelic-designs) · [Appendix](#appendix-a-supporting-results) · [Theory files](#theory-files)

## Alphabet and notation

AD’s inner state gains waiting, trace and refusal observations. General results use the trace class; prefix results use event lists.

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d26"></a>**D26** / D107 | Reactive angelic alphabet | — | [utp_rad_core.thy](../../reactive-angelic-designs/utp_rad_core.thy) |

## §6.1 Healthiness conditions

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d27"></a>**D27** / D108 | Trace-extending final states | — | [rad_trace_extensions](../../reactive-angelic-designs/utp_rad_healthy.thy#L10) |
| <a id="d28"></a>**D28** / D109 | RA1 trace-extension healthiness | — | [RA1](../../reactive-angelic-designs/utp_rad_healthy.thy#L16) |
| <a id="t9"></a>**T9** / T.5.2.1 | RA1 absorbs A0 | None | [RA1_A0_absorb](../../reactive-angelic-designs/utp_rad_healthy.thy#L146) |
| <a id="d29"></a>**D29** / D110 | RA2 trace normalization | — | [RA2](../../reactive-angelic-designs/utp_rad_healthy.thy#L301) |
| <a id="d30"></a>**D30** / D111 | Reactive identity | — | [II_Rac](../../reactive-angelic-designs/utp_rad_healthy.thy#L513) |
| <a id="d31"></a>**D31** / D112 | RA3 waiting behaviour | — | [RA3](../../reactive-angelic-designs/utp_rad_healthy.thy#L736) |
| <a id="d32"></a>**D32** / D113 | Combined reactive healthiness | — | [RA](../../reactive-angelic-designs/utp_rad_healthy.thy#L861) |
| <a id="ex11"></a>**Ex11** | RA1 and PBMH disagree on empty choices | — | [RA1_PBMH_ades_ac_empty_example](../../reactive-angelic-designs/utp_rad_examples.thy#L15) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.5.2.2–3, 6–7, 12–13 | RA1/RA2/RA3 distribution | See component declarations | [utp_rad_healthy](../../reactive-angelic-designs/utp_rad_healthy.thy) |
| T.5.2.15 | PBMH absorption around RA3 | None | [PBMH_ades_RA3_absorb](../../reactive-angelic-designs/utp_rad_healthy.thy#L815) |

</details>

## §6.2 Reactive angelic designs

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d33"></a>**D33** / D114 | CSPA1 healthiness | — | [CSPA1](../../reactive-angelic-designs/utp_rad_designs.thy#L10) |
| <a id="t10"></a>**T10** | RA1 after CSPA1 agrees with RA1 after H1 | None | [RA1_CSPA1](../../reactive-angelic-designs/utp_rad_designs.thy#L34) |
| <a id="d34"></a>**D34** / D115 | CSPA2 healthiness | — | [CSPA2](../../reactive-angelic-designs/utp_rad_designs.thy#L60) |
| <a id="d35"></a>**D35** / D116 | RAD healthiness | — | [RAD](../../reactive-angelic-designs/utp_rad_designs.thy#L86) |
| <a id="t11"></a>**T11** / T.5.2.20 | RAD design normal form | None; healthy specialization requires RAD | [RAD_design_form](../../reactive-angelic-designs/utp_rad_designs.thy#L118), [RAD_design_form'](../../reactive-angelic-designs/utp_rad_designs.thy#L138) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.5.2.18 | CSPA1 after RA1 agrees with RA1 after H1 | None | [CSPA1_RA1](../../reactive-angelic-designs/utp_rad_designs.thy#L40) |
| T.5.2.21 | RAD implies upward closure | P is RAD | [RAD_is_PBMH_ades](../../reactive-angelic-designs/utp_rad_designs.thy#L107) |
| T.G.4.5 | Re-extraction preserves the design normal form | Projected design form | [RA_design_form_idem](../../reactive-angelic-designs/utp_rad_healthy.thy#L1144) |
| T.G.5.1 | CSPA1 idempotence | None | [CSPA1_Idempotent](../../reactive-angelic-designs/utp_rad_designs.thy#L24) |

</details>

## §6.3 Relationship with CSP

### §6.3.1 From reactive angelic designs to CSP

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t12"></a>**T12** / T.5.3.1 | ac2p carries RA to ordinary reactive healthiness | P is PBMH_ades | [rad_ac2p_RA](../../reactive-angelic-designs/utp_rad_csp.thy#L102) |
| <a id="t13"></a>**T13** / T.5.3.2 | ac2p of the reactive design normal form | Projected failure/success components | [rad_ac2p_RA_design](../../reactive-angelic-designs/utp_rad_csp.thy#L111) |
| <a id="d36"></a>**D36** / D122 | Singleton-choice binder | — | [ades_singleton_choice](../../angelic-designs/utp_ades_healthy.thy#L1169), [ac_singleton_choice](../../angelic-designs/utp_ades_healthy.thy#L1153) |
| <a id="ex12"></a>**Ex12** | Choice of differently prefixed deadlocks; a ≠ b for CSP comparison | — | [Prefix_Stop_Stop_angelic_choice](../../reactive-angelic-designs/utp_rad_examples.thy#L433), [Prefix_Stop_Stop_R](../../reactive-angelic-designs/utp_rad_examples.thy#L488) |
| <a id="l5"></a>**L5** | Ordinary CSP comparison of different prefixed deadlocks | a ≠ b; list traces | [Prefix_Stop_Stop_R](../../reactive-angelic-designs/utp_rad_examples.thy#L488) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.G.7.1–2 | ac2p maps trace healthiness | P is PBMH_ades | [rad_ac2p_RA1](../../reactive-angelic-designs/utp_rad_csp.thy#L43), [rad_ac2p_RA1_RA2](../../reactive-angelic-designs/utp_rad_csp.thy#L55) |
| T.G.7.3 | ac2p maps waiting healthiness | None | [rad_ac2p_RA3](../../reactive-angelic-designs/utp_rad_csp.thy#L87) |

</details>

### §6.3.2 From CSP to reactive angelic designs

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t14"></a>**T14** / T.5.3.3 | p2ac carries ordinary reactive healthiness to RA | None | [rad_p2ac_R](../../reactive-angelic-designs/utp_rad_csp.thy#L209) |
| <a id="t15"></a>**T15** / T.5.3.4 | p2ac of an ordinary reactive design | Projected failure/success components | [rad_p2ac_R_design](../../reactive-angelic-designs/utp_rad_csp.thy#L268) |
| <a id="ex13"></a>**Ex13** | Ordinary reactive identity maps to II_Rac | — | [rad_p2ac_Skip_R](../../reactive-angelic-designs/utp_rad_examples.thy#L622) |
| <a id="t16"></a>**T16** / T.5.3.5 | Ordinary reactive predicate round trip | None | [rad_ac2p_p2ac_inverse](../../reactive-angelic-designs/utp_rad_csp.thy#L278) |
| <a id="l6"></a>**L6** | Existential form of the reverse round trip | None | [rad_p2ac_ac2p](../../reactive-angelic-designs/utp_rad_csp.thy#L284) |
| <a id="ex14"></a>**Ex14** | Two-prefix postcondition round trip; a ≠ b | — | [rad_p2ac_ac2p_prefix_stop_pair](../../reactive-angelic-designs/utp_rad_examples.thy#L636) |
| <a id="t17"></a>**T17** / T.5.3.6 | Reverse round-trip refinement | P is PBMH_ades | [rad_p2ac_ac2p_refine](../../reactive-angelic-designs/utp_rad_csp.thy#L301) |
| <a id="t18"></a>**T18** / T.5.3.7 | Exact round trip of the reactive design form | F(P), T(P) both A2 | [rad_p2ac_ac2p_RA_design](../../reactive-angelic-designs/utp_rad_csp.thy#L319) |

In T18, `F(P)` and `T(P)` set initial waiting false and final `ok′` false/true respectively.

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.G.7.8–10 | p2ac maps ordinary reactive components | None | [rad_p2ac_R1](../../reactive-angelic-designs/utp_rad_csp.thy#L167), [rad_p2ac_R1_R2](../../reactive-angelic-designs/utp_rad_csp.thy#L176), [rad_p2ac_R3](../../reactive-angelic-designs/utp_rad_csp.thy#L196) |
| L.G.7.2 | p2ac maps reactive identity | None | [rad_p2ac_II_C](../../reactive-angelic-designs/utp_rad_csp.thy#L187) |
| L.G.7.11 | A2 reverse round trip with nonempty choices | P is A2 | [rad_p2ac_ac2p_A2](../../reactive-angelic-designs/utp_rad_csp.thy#L312) |

Additional round-trip support: [rad_p2ac_ac2p_A2_form](../../reactive-angelic-designs/utp_rad_csp.thy#L293) retains the nonempty-choice factor; [rad_p2ac_ac2p_RAD_A2](../../reactive-angelic-designs/utp_rad_csp.thy#L369) gives equality for RAD/A2 inputs. Routine operator closure and component algebra are in the theory files below.

</details>

## §6.4 Operators

[Angelic choice](#641-angelic-choice) · [Demonic choice](#642-demonic-choice) · [Chaos](#643-chaos) · [Choice](#644-choice) · [Stop](#645-stop) · [Skip](#646-skip) · [Sequence](#647-sequential-composition) · [Prefix](#648-prefixing) · [External choice](#649-external-choice)

### §6.4.1 Angelic choice

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d37"></a>**D37** / D117 | Angelic choice | — | [achoice_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L10) |
| <a id="t19"></a>**T19** / T.5.4.1 | Angelic choice normal form | Both operands RAD | [RAD_angelic_choice_design](../../reactive-angelic-designs/utp_rad_ops.thy#L21) |
| <a id="t20"></a>**T20** / T.5.4.2 | CSP angelic-choice round trip | None | [RAD_angelic_choice_CSP](../../reactive-angelic-designs/utp_rad_ops.thy#L63) |
| <a id="t21"></a>**T21** / T.5.4.3 | Angelic choice refines its CSP image | Both operands RAD | [RAD_angelic_choice_CSP_refine](../../reactive-angelic-designs/utp_rad_ops.thy#L79) |

### §6.4.2 Demonic choice

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d38"></a>**D38** / D118 | Demonic choice | — | [dchoice_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L101) |
| <a id="t22"></a>**T22** / T.5.4.4 | Demonic choice normal form | Both operands RAD | [RAD_demonic_choice_design](../../reactive-angelic-designs/utp_rad_ops.thy#L111) |
| <a id="t23"></a>**T23** / T.5.4.5 | Reverse mapping distributes over demonic choice | None | [RAD_demonic_choice_CSP_distrib](../../reactive-angelic-designs/utp_rad_ops.thy#L147) |
| <a id="l7"></a>**L7** / L.5.4.1 | Exact demonic-choice CSP image | Both operands RAD and A2 | [RAD_demonic_choice_CSP_A2](../../reactive-angelic-designs/utp_rad_ops.thy#L153) |
| <a id="t24"></a>**T24** / T.5.4.6 | CSP demonic-choice round trip | None | [RAD_demonic_choice_CSP](../../reactive-angelic-designs/utp_rad_ops.thy#L162) |

### §6.4.3 Chaos

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d39"></a>**D39** / D119 | Chaos | — | [Chaos_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L183) |
| <a id="t25"></a>**T25** / T.5.4.8 | Chaos is an angelic-choice unit | P is RAD | [Chaos_RAD_angelic_choice_unit](../../reactive-angelic-designs/utp_rad_ops.thy#L211) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.5.4.7 | Chaos is a demonic-choice zero | P is RAD | [Chaos_RAD_demonic_choice_zero](../../reactive-angelic-designs/utp_rad_ops.thy#L225) |

</details>

### §6.4.4 Choice

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d40"></a>**D40** / D120 | Choice | — | [Choice_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L240) |
| <a id="t26"></a>**T26** / T.5.4.13 | Angelic choice with Choice | P is RAD | [Choice_RAD_angelic_choice](../../reactive-angelic-designs/utp_rad_ops.thy#L295) |
| <a id="t27"></a>**T27** / T.5.4.14 | Demonic choice with Choice | P is RAD | [Choice_RAD_demonic_choice](../../reactive-angelic-designs/utp_rad_ops.thy#L330) |

### §6.4.5 Stop

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d41"></a>**D41** / D121 | Stop | — | [Stop_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L360) |
| <a id="t28"></a>**T28** / T.5.4.15 | Angelic choice with Stop | P is RAD | [Stop_RAD_angelic_choice](../../reactive-angelic-designs/utp_rad_ops.thy#L537) |

### §6.4.6 Skip

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d42"></a>**D42** / D123 | Skip | — | [Skip_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L570) |
| <a id="t29"></a>**T29** / T.5.4.18 | Angelic choice with Skip | P is RAD | [Skip_RAD_angelic_choice](../../reactive-angelic-designs/utp_rad_ops.thy#L669) |
| <a id="ex15"></a>**Ex15** | Choice of Stop and Skip | — | [Stop_Skip_angelic_choice](../../reactive-angelic-designs/utp_rad_examples.thy#L23) |
| <a id="l8"></a>**L8** / L.5.4.2 | CSP image of Stop angelically combined with Skip | None | [rad_ac2p_Stop_Skip](../../reactive-angelic-designs/utp_rad_examples.thy#L64) |

### §6.4.7 Sequential composition

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| §6.4.7 (paper) / §5.4.7 | Sequential operator | Same underlying design composition as AD | [seq_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L704) |
| <a id="t30"></a>**T30** / T.5.4.21 | Sequential composition normal form | Both operands RAD | [RAD_seq_design](../../reactive-angelic-designs/utp_rad_seq.thy#L276) |
| <a id="l9"></a>**L9** / L.5.4.3 | Stop/Skip choice followed by Chaos | None | [Stop_Skip_seq_Chaos](../../reactive-angelic-designs/utp_rad_examples.thy#L83) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.5.4.22 | Sequential CSP refinement | Both operands RAD | [RAD_seq_CSP_refine](../../reactive-angelic-designs/utp_rad_seq.thy#L25) |
| T.5.4.23 | Exact sequential CSP image | Both operands RAD and A2 | [RAD_seq_CSP_A2](../../reactive-angelic-designs/utp_rad_seq.thy#L34) |
| T.5.4.24 | Sequential CSP round trip | None | [RAD_seq_CSP_inverse](../../reactive-angelic-designs/utp_rad_seq.thy#L42) |
| T.5.4.25 | Sequential A2 closure | Both operands RAD and A2 | [RAD_seq_A2_closure](../../reactive-angelic-designs/utp_rad_seq.thy#L363) |
| T.G.8.5–6 | RA/RA1 component sequence calculations | Component healthiness and independence; see declarations | [utp_rad_seq](../../reactive-angelic-designs/utp_rad_seq.thy) |

</details>

### §6.4.8 Prefixing

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d43"></a>**D43** / D124 | Primitive event prefix | — | [PrefixSkip_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L722) |
| <a id="t31"></a>**T31** / T.5.4.26 | Angelic choice with primitive prefix | P is RAD; list traces | [PrefixSkip_RAD_angelic_choice](../../reactive-angelic-designs/utp_rad_ops.thy#L835) |
| <a id="ex16"></a>**Ex16** / Ex33 | Prefixed deadlock avoids divergence through termination | — | [Prefix_Stop_Skip_seq_Chaos](../../reactive-angelic-designs/utp_rad_examples.thy#L272) |
| <a id="ex17"></a>**Ex17** / Ex34 | Termination avoids divergence after the same prefix | — | [Prefix_Skip_Chaos_angelic_choice](../../reactive-angelic-designs/utp_rad_examples.thy#L380) |
| <a id="ex18"></a>**Ex18** | Different events preserve RAD trace history; a ≠ b | — | [Prefix_Skip_Chaos_different_events](../../reactive-angelic-designs/utp_rad_examples.thy#L593) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| §5.4.8 | Compound event prefix | List traces | [Prefix_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L865) |
| T.5.4.27–28 | Primitive-prefix mappings | List traces | [rad_ac2p_PrefixSkip_RAD](../../reactive-angelic-designs/utp_rad_ops_csp.thy#L50), [rad_p2ac_PrefixSkip_R](../../reactive-angelic-designs/utp_rad_ops_csp.thy#L34) |
| T.5.4.29 | General prefix normal form | P is RAD; list traces | [Prefix_RAD_design](../../reactive-angelic-designs/utp_rad_seq.thy#L480) |

</details>

### §6.4.9 External choice

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d44"></a>**D44** / D125 | External choice | — | [extchoice_RAD](../../reactive-angelic-designs/utp_rad_ops.thy#L902) |
| <a id="t32"></a>**T32** / T.5.4.30 | External choice with Stop | P is RAD | [extchoice_RAD_Stop](../../reactive-angelic-designs/utp_rad_ops.thy#L976) |
| <a id="t33"></a>**T33** / T.5.4.31 | Stop is an external-choice unit | P is RAD and A2 | [extchoice_RAD_Stop_unit](../../reactive-angelic-designs/utp_rad_ops.thy#L1006) |
| <a id="ex19"></a>**Ex19** | External choice with Stop prevents a divergent event choice | — | [Prefix_Chaos_Chaos_extchoice_Stop](../../reactive-angelic-designs/utp_rad_examples.thy#L673) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| D62, D64 | Ordinary prefix and external-choice helpers | See explicit definitions | [utp_rad_ops_csp](../../reactive-angelic-designs/utp_rad_ops_csp.thy) |
| T.5.4.32 | External-choice correspondence | None for the explicit helper | [rad_p2ac_extchoice](../../reactive-angelic-designs/utp_rad_ops_csp.thy#L80), [RAD_extchoice_CSP](../../reactive-angelic-designs/utp_rad_ops_csp.thy#L106) |
| T.5.4.33 | External-choice CSP refinement | Both operands RAD | [RAD_extchoice_CSP_refine](../../reactive-angelic-designs/utp_rad_ops_csp.thy#L112) |
| T.5.4.34 | Exact external-choice CSP image | Both operands RAD and A2 | [RAD_extchoice_CSP_A2](../../reactive-angelic-designs/utp_rad_ops_csp.thy#L121) |
| T.5.4.35 | External-choice A2 closure | Both operands RAD and A2 | [extchoice_RAD_A2_closure](../../reactive-angelic-designs/utp_rad_ops_csp.thy#L130) |

</details>

## §6.5 Non-divergent reactive angelic designs

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d45"></a>**D45** / D126 | Non-divergence transformer | — | [NDRAD](../../reactive-angelic-designs/utp_rad_nd.thy#L9) |
| <a id="ex20"></a>**Ex20** | NDRAD maps Chaos to Choice | — | [NDRAD_Chaos_example](../../reactive-angelic-designs/utp_rad_examples.thy#L521) |
| <a id="ex21"></a>**Ex21** | Primitive prefix is already non-divergent | — | [NDRAD_Prefix_Skip](../../reactive-angelic-designs/utp_rad_examples.thy#L526) |
| <a id="t34"></a>**T34** / T.5.5.2 | Non-divergent design normal form | P is RAD | [NDRAD_design_form](../../reactive-angelic-designs/utp_rad_nd.thy#L34) |
| <a id="t35"></a>**T35** / T.5.5.3 | Non-divergence fixed points | P is RAD; failure test guarded by initial ok | [NDRAD_fixed_point](../../reactive-angelic-designs/utp_rad_nd.thy#L43) |

T35 tests failure only at started observations; see [theorem35_counterexample](../../reactive-angelic-designs/utp_rad_nd.thy#L180).

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.5.5.1 | NDRAD idempotence | None | [NDRAD_idem](../../reactive-angelic-designs/utp_rad_nd.thy#L12) |
| T.G.6.1 | Non-divergent sequence normal form and derived closure | Both operands RAD and NDRAD | [NDRAD_seq_design](../../reactive-angelic-designs/utp_rad_nd.thy#L89), [NDRAD_seq_closure](../../reactive-angelic-designs/utp_rad_nd.thy#L142) |

</details>

## Appendix A: supporting results

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t66"></a>**T66** / T.5.2.11 | PBMH absorption around RA2 | None | [PBMH_ades_RA2_absorb](../../reactive-angelic-designs/utp_rad_healthy.thy#L482) |
| <a id="t67"></a>**T67** | RA after A agrees with RA after PBMH | P is H | [RA_A](../../reactive-angelic-designs/utp_rad_healthy.thy#L926) |
| <a id="t68"></a>**T68** / T.5.2.16 | RA1 and RA3 commute | None; printed correction | [RA1_RA3_commute](../../reactive-angelic-designs/utp_rad_healthy.thy#L825) |
| <a id="t69"></a>**T69** / T.5.2.17 | RA2 and RA3 commute | None | [RA2_RA3_commute](../../reactive-angelic-designs/utp_rad_healthy.thy#L829) |
| <a id="t70"></a>**T70** / T.5.2.5 | PBMH absorption around RA1 | None | [PBMH_ades_RA1_absorb](../../reactive-angelic-designs/utp_rad_healthy.thy#L174) |
| <a id="t71"></a>**T71** / T.5.2.10 | RA1 and RA2 commute | None | [RA1_RA2_commute](../../reactive-angelic-designs/utp_rad_healthy.thy#L407) |

T67 requires H-healthiness. T68 states the commutation established by the source proof, whose printed equation repeats one side.

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="l19"></a>**L19** | RA3 absorbs initial-wait-false substitution | None | [RA3_wait_false_absorb](../../reactive-angelic-designs/utp_rad_healthy.thy#L840) |
| <a id="l20"></a>**L20** | Failure projection of the reactive design form | Projected design form | [RA_design_wf_ok_false](../../reactive-angelic-designs/utp_rad_healthy.thy#L1010) |
| <a id="l21"></a>**L21** | Success projection of the reactive design form | Projected design form | [RA_design_wf_ok_true](../../reactive-angelic-designs/utp_rad_healthy.thy#L1038) |
| <a id="l22"></a>**L22** | Normalize a reactive design postcondition | Design form | [RA_design_post](../../reactive-angelic-designs/utp_rad_healthy.thy#L1055) |
| <a id="l23"></a>**L23** | Normalize a reactive design precondition | Design form | [RA1_design_pre](../../reactive-angelic-designs/utp_rad_healthy.thy#L130) |

## Theory files

| File | Supporting material |
| --- | --- |
| [utp_rad_core](../../reactive-angelic-designs/utp_rad_core.thy) | Native record selectors, updates, cases and lenses; implementation support for D26. |
| [utp_rad_healthy](../../reactive-angelic-designs/utp_rad_healthy.thy) | Trace-set algebra; `ok`/wait substitution and independence; RA distribution and composition. `RA1_conj/disj`, `RA2_conj/disj`, `RA3_conj/disj` correspond to thesis T.5.2.2–3, 6–7, 12–13. |
| [utp_rad_designs](../../reactive-angelic-designs/utp_rad_designs.thy) | Healthy components, bounds and normal-form closure. |
| [utp_rad_csp](../../reactive-angelic-designs/utp_rad_csp.thy) | Component mapping, substitution and round-trip lemmas. |
| [utp_rad_ops](../../reactive-angelic-designs/utp_rad_ops.thy) | Primitive postcondition normalisation, substitutions and healthiness. |
| [utp_rad_seq](../../reactive-angelic-designs/utp_rad_seq.thy) | RA1/RA sequential normal forms (T.G.8.6 / T.G.8.5); prefix handover and continuation calculations. |
| [utp_rad_ops_csp](../../reactive-angelic-designs/utp_rad_ops_csp.thy) | Explicit ordinary prefix/external-choice definitions and correspondence. |
| [utp_rad_nd](../../reactive-angelic-designs/utp_rad_nd.thy) | Non-divergence and the guarded T35 characterisation. |

The native `rad_state` is `('t, 'e set) rea_vars_ext`: library fields hold waiting and trace, and the extension tail holds refusals. The outer design supplies `ok`, so `ac2p`, `p2ac` and `d2ac` apply directly without an observation adapter.

<details>
<summary>Parallel research and representation comparison</summary>

<a id="parallel-research"></a>

Parallel-by-merge is an extension of this repository's paper development. Its definitions and closure conditions are documented separately in [RAD parallel](../parallel/RAD.md); they have no numbered RAD parallel counterpart in the source material indexed above.

| Research result | Premises | Implementation |
| --- | --- | --- |
| Lift an ordinary reactive merge using nonempty branch choices and `∀left ∀right ∃output` coverage. | None | [`rad_lift_merge`](../../reactive-angelic-designs/utp_rad_parallel.thy#L276) |
| RADm is a monotonic, idempotent transformer on ordinary reactive merges. | None | [`RADm`](../../reactive-angelic-designs/utp_rad_parallel.thy#L170), [`RADm_Monotonic`](../../reactive-angelic-designs/utp_rad_parallel.thy#L187), [`RADm_Idempotent`](../../reactive-angelic-designs/utp_rad_parallel.thy#L184) |
| `p2ac(RD D) = RAD(p2ac D)`. | None | [`rad_p2ac_RD`](../../reactive-angelic-designs/utp_rad_parallel.thy#L370) |
| `ac2p P is RD`. | `P` both RAD and A2 | [`rad_ac2p_RD`](../../reactive-angelic-designs/utp_rad_parallel.thy#L445) |
| Raw lifted parallel is RAD-healthy; applying RAD afterwards is redundant. | `P`, `Q` both RAD and A2; `M is RADm` | [`rad_par_raw_RADm`](../../reactive-angelic-designs/utp_rad_parallel.thy#L456), [`rad_par_eq_raw`](../../reactive-angelic-designs/utp_rad_parallel.thy#L462) |

The migration-only [representation comparison](../../reactive-angelic-designs/utp_rad_representation.thy) checks correspondence with the former custom record. Its encode/decode definitions are not used by the RAD implementation or by the proofs above.

</details>
