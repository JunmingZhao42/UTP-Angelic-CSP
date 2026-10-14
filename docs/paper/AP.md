# Angelic processes

[Paper coverage](README.md) · [AD](AD.md) · [RAD](RAD.md)

Paper §7; thesis Chapter 6 and Appendix H.

[Alphabet](#alphabet-and-notation) · [§7.1 Healthiness](#71-healthiness-conditions) · [§7.2 RAD correspondence](#72-relationship-with-reactive-angelic-designs) · [§7.3 Operators](#73-operators) · [Theory files](#theory-files)

## Alphabet and notation

AP keeps the [RAD alphabet and trace conventions](RAD.md#alphabet-and-notation), with different healthiness conditions.

## §7.1 Healthiness conditions

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d46"></a>**D46** / D127 | AP healthiness | — | [AP](../../angelic-processes/utp_ap_healthy.thy#L173) |

### §7.1.1 RA3AP

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d47"></a>**D47** / D128 | AP waiting identity | — | [II_AP](../../angelic-processes/utp_ap_healthy.thy#L10) |
| <a id="d48"></a>**D48** / D129 | AP waiting healthiness | — | [RA3AP](../../angelic-processes/utp_ap_healthy.thy#L34) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.6.2.1–2 | RA3AP idempotence and monotonicity | None | [RA3AP_Idempotent](../../angelic-processes/utp_ap_healthy.thy#L40), [RA3AP_Monotonic](../../angelic-processes/utp_ap_healthy.thy#L47) |
| T.6.2.3–4 | RA3AP distributes over both choices | None | [RA3AP_conj](../../angelic-processes/utp_ap_healthy.thy#L50), [RA3AP_disj](../../angelic-processes/utp_ap_healthy.thy#L53) |
| T.6.2.7 | RA2 and RA3AP commute | None | [RA2_RA3AP_commute](../../angelic-processes/utp_ap_healthy.thy#L98) |

</details>

### §7.1.2 Angelic processes

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t36"></a>**T36** / T.6.2.8 | AP design representation | None | [AP_design_form](../../angelic-processes/utp_ap_healthy.thy#L186) |
| <a id="t37"></a>**T37** / T.6.2.9 | Waiting-conditional AP normal form | None | [AP_wait_cond_design](../../angelic-processes/utp_ap_healthy.thy#L204) |

### §7.1.3 Non-divergent angelic processes

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d49"></a>**D49** / D130 | Non-divergence transformer | — | [NDAP](../../angelic-processes/utp_ap_nd.thy#L10) |
| <a id="t38"></a>**T38** / T.6.2.10 | Non-divergent AP normal form | P is AP | [NDAP_design_form](../../angelic-processes/utp_ap_nd.thy#L49) |

<details>
<summary>Supplementary results</summary>

[NDAP_is_H3](../../angelic-processes/utp_ap_nd.thy#L76) assumes AP input, and [RA1_NDAP_NDRAD](../../angelic-processes/utp_ap_nd.thy#L198) links the normalized non-divergent images.

</details>

## §7.2 Relationship with reactive angelic designs

### §7.2.1 From reactive angelic designs to angelic processes

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t39"></a>**T39** / T.6.3.1 | RAD-to-AP image under H1 | None | [H1_RAD_design](../../angelic-processes/utp_ap_rad.thy#L10) |
| <a id="ex22"></a>**Ex22** | H1 image of RAD Chaos | — | [H1_Chaos_RAD_example](../../angelic-processes/utp_ap_examples.thy#L13) |

### §7.2.2 Non-divergent processes

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="l10"></a>**L10** | H1 image of a true-precondition reactive design | Projected success component | [H1_RA_A_true_design](../../angelic-processes/utp_ap_rad.thy#L80) |
| <a id="ex23"></a>**Ex23** | H1 image of RAD Skip | — | [H1_Skip_RAD_example](../../angelic-processes/utp_ap_examples.thy#L23) |

### §7.2.3 From angelic processes to reactive angelic designs

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t40"></a>**T40** / T.6.3.2 | AP-to-RAD image under RA1 | None | [RA1_AP_design](../../angelic-processes/utp_ap_rad.thy#L135), [RA1_AP_RAD](../../angelic-processes/utp_ap_rad.thy#L155) |
| <a id="ex24"></a>**Ex24** | RAD Chaos round trip | — | [RA1_H1_Chaos_RAD_example](../../angelic-processes/utp_ap_examples.thy#L32) |

### §7.2.4 Isomorphism and Galois connection

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t41"></a>**T41** / T.6.3.3 | Exact RAD round trip | None on the RAD image | [RA1_H1_RAD](../../angelic-processes/utp_ap_rad.thy#L172) |
| <a id="t42"></a>**T42** / T.6.3.4 | AP round-trip refinement | None on the AP image | [H1_RA1_AP_refine](../../angelic-processes/utp_ap_rad.thy#L184) |
| <a id="ex25"></a>**Ex25** | AP bottom round trip | — | [H1_RA1_bottom_AP_example](../../angelic-processes/utp_ap_examples.thy#L40) |
| <a id="t43"></a>**T43** / T.6.3.5 | Exact non-divergent AP round trip | None on the NDAP/AP image | [H1_RA1_NDAP_AP](../../angelic-processes/utp_ap_nd.thy#L188) |

<details>
<summary>Supplementary results</summary>

[AP_RAD_galois](../../angelic-processes/utp_ap_rad.thy#L201) relates AP and RAD carriers.

</details>

## §7.3 Operators

[Angelic choice](#731-angelic-choice) · [Demonic choice](#732-demonic-choice) · [Divergence](#733-divergence) · [Choice](#734-choice) · [Stop](#735-stop) · [Skip](#736-skip) · [Sequence](#737-sequential-composition) · [Prefix](#738-prefixing)

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.6.4.1, 5 | Angelic and demonic choice preserve AP | Both operands AP | [AP_angelic_closure](../../angelic-processes/utp_ap_ops.thy#L53), [AP_demonic_closure](../../angelic-processes/utp_ap_ops.thy#L111) |

</details>

### §7.3.1 Angelic choice

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d50"></a>**D50** / D131 | Angelic choice | — | [achoice_AP](../../angelic-processes/utp_ap_ops.thy#L9) |
| <a id="t44"></a>**T44** / T.6.4.2 | Angelic choice preserves NDAP | Both operands NDAP | [NDAP_angelic_closure](../../angelic-processes/utp_ap_nd.thy#L136) |
| <a id="t45"></a>**T45** / T.6.4.3 | RAD angelic choice preserved through AP | Both operands RAD | [RA1_H1_angelic_choice](../../angelic-processes/utp_ap_ops.thy#L73) |
| <a id="t46"></a>**T46** / T.6.4.4 | AP angelic-choice refinement through RAD | Both operands AP | [H1_RA1_angelic_choice_refine](../../angelic-processes/utp_ap_ops.thy#L81) |

### §7.3.2 Demonic choice

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d51"></a>**D51** / D132 | Demonic choice | — | [dchoice_AP](../../angelic-processes/utp_ap_ops.thy#L99) |
| <a id="t47"></a>**T47** / T.6.4.6 | Demonic choice preserves NDAP | Both operands NDAP | [NDAP_demonic_closure](../../angelic-processes/utp_ap_nd.thy#L144) |
| <a id="t48"></a>**T48** / T.6.4.7 | RAD demonic choice preserved through AP | Both operands RAD | [RA1_H1_demonic_choice](../../angelic-processes/utp_ap_ops.thy#L135) |
| <a id="t49"></a>**T49** / T.6.4.8 | AP demonic-choice refinement through RAD | Both operands AP | [H1_RA1_demonic_choice_refine](../../angelic-processes/utp_ap_ops.thy#L143) |

### §7.3.3 Divergence

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d52"></a>**D52** / D133 | Chaos | — | [Chaos_AP](../../angelic-processes/utp_ap_ops.thy#L162) |
| <a id="l11"></a>**L11** / L.6.4.1 | Chaos design form | None | [Chaos_AP_design](../../angelic-processes/utp_ap_ops.thy#L174) |
| <a id="t50"></a>**T50** / T.6.4.9 | Chaos is an angelic-choice unit | P is AP | [Chaos_AP_angelic_choice_unit](../../angelic-processes/utp_ap_ops.thy#L200) |
| <a id="d53"></a>**D53** / D134 | Chaos with CSP divergence | — | [ChaosCSP_AP](../../angelic-processes/utp_ap_ops.thy#L216) |
| <a id="t51"></a>**T51** / T.6.4.10 | H1 maps RAD Chaos to AP ChaosCSP | None | [H1_Chaos_RAD](../../angelic-processes/utp_ap_ops.thy#L278) |
| <a id="t52"></a>**T52** / T.6.4.11 | RA1 maps AP ChaosCSP to RAD Chaos | None | [RA1_ChaosCSP_AP](../../angelic-processes/utp_ap_ops.thy#L295) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| L.6.4.2 | ChaosCSP design form | None | [ChaosCSP_AP_design](../../angelic-processes/utp_ap_ops.thy#L242) |

</details>

### §7.3.4 Choice

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d54"></a>**D54** / D135 | Choice | — | [Choice_AP](../../angelic-processes/utp_ap_ops.thy#L303) |
| <a id="t53"></a>**T53** / T.6.4.12 | H1 maps RAD Choice to AP Choice | None | [H1_Choice_RAD](../../angelic-processes/utp_ap_ops.thy#L333) |
| <a id="t54"></a>**T54** / T.6.4.13 | RA1 maps AP Choice to RAD Choice | None | [RA1_Choice_AP](../../angelic-processes/utp_ap_ops.thy#L339) |

### §7.3.5 Stop

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d55"></a>**D55** / D136 | Stop | — | [Stop_AP](../../angelic-processes/utp_ap_ops.thy#L347) |
| <a id="t55"></a>**T55** / T.6.4.14 | H1 maps RAD Stop to AP Stop | None | [H1_Stop_RAD](../../angelic-processes/utp_ap_ops.thy#L363) |
| <a id="t56"></a>**T56** / T.6.4.15 | RA1 maps AP Stop to RAD Stop | None | [RA1_Stop_AP](../../angelic-processes/utp_ap_ops.thy#L369) |

### §7.3.6 Skip

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d56"></a>**D56** / D137 | Skip | — | [Skip_AP](../../angelic-processes/utp_ap_ops.thy#L377) |
| <a id="t57"></a>**T57** / T.6.4.16 | H1 maps RAD Skip to AP Skip | None | [H1_Skip_RAD](../../angelic-processes/utp_ap_ops.thy#L393) |
| <a id="t58"></a>**T58** / T.6.4.17 | RA1 maps AP Skip to RAD Skip | None | [RA1_Skip_AP](../../angelic-processes/utp_ap_ops.thy#L399) |

### §7.3.7 Sequential composition

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| §7.4.7 (paper) / §6.4.7 | Sequential operator | Same design composition as AD | [angelic_design_seq](../../angelic-designs/utp_ades_ops.thy#L260) |
| <a id="t59"></a>**T59** / T.6.4.18 | Sequential composition normal form | Both operands AP | [AP_seq_design](../../angelic-processes/utp_ap_ops.thy#L788) |
| <a id="ex26"></a>**Ex26** / Ex44 | Stop/Skip choice followed by Chaos | — | [Stop_Skip_seq_Chaos_AP](../../angelic-processes/utp_ap_examples.thy#L51) |
| <a id="t60"></a>**T60** / T.6.4.19 | RAD sequence refinement through AP | Both operands RAD | [RA1_H1_seq_refine](../../angelic-processes/utp_ap_ops.thy#L813) |
| <a id="t61"></a>**T61** / T.6.4.20 | AP sequence refinement through RAD | Both operands AP | [H1_RA1_seq_refine](../../angelic-processes/utp_ap_ops.thy#L838) |
| <a id="t62"></a>**T62** / T.6.4.21 | Exact non-divergent RAD sequence transport | Both operands RAD and NDRAD | [RA1_H1_seq](../../angelic-processes/utp_ap_ops.thy#L900) |
| <a id="t63"></a>**T63** / T.6.4.22 | Sequential composition preserves NDAP | Both operands AP and NDAP | [NDAP_seq_closure](../../angelic-processes/utp_ap_nd.thy#L157) |

T63 requires both AP and NDAP and does not assume associativity. Closure and correspondence laws alone do not establish unrestricted reassociation.

<details>
<summary>Supplementary results</summary>

[AP_seq_closure](../../angelic-processes/utp_ap_ops.thy#L807) requires both operands AP.

</details>

### §7.3.8 Prefixing

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d57"></a>**D57** / D138 | Primitive event prefix | — | [PrefixSkip_AP](../../angelic-processes/utp_ap_ops.thy#L935) |
| §7.4.8 (paper) / §6.4.8 | Compound event prefix | List traces | [Prefix_AP](../../angelic-processes/utp_ap_ops.thy#L967) |
| <a id="l12"></a>**L12** / L.6.4.4 | H1 maps RAD primitive prefix to AP | List traces | [H1_PrefixSkip_RAD](../../angelic-processes/utp_ap_ops.thy#L953) |
| <a id="l13"></a>**L13** / L.6.4.5 | RA1 maps AP primitive prefix to RAD | List traces | [RA1_PrefixSkip_AP](../../angelic-processes/utp_ap_ops.thy#L959) |
| <a id="l14"></a>**L14** / L.6.4.6 | Prefix followed by ChaosCSP | List traces | [Prefix_ChaosCSP_AP](../../angelic-processes/utp_ap_examples.thy#L119) |
| <a id="ex27"></a>**Ex27** / Ex45 | Divergence erases an event prefix | — | [Prefix_Chaos_AP](../../angelic-processes/utp_ap_examples.thy#L108) |
| <a id="ex28"></a>**Ex28** / Ex46 | Angelic choice avoids a divergent prefix; no a ≠ b premise | — | [Prefix_Chaos_Skip_angelic_choice](../../angelic-processes/utp_ap_examples.thy#L186) |

<details>
<summary>Supplementary results</summary>

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| T.6.4.23 | General prefix normal form | P is AP; list traces | [Prefix_AP_design](../../angelic-processes/utp_ap_ops.thy#L987) |

</details>

## Theory files

| File | Contents |
| --- | --- |
| [utp_ap_healthy](../../angelic-processes/utp_ap_healthy.thy) | AP healthiness, waiting laws, normal forms and component support. |
| [utp_ap_rad](../../angelic-processes/utp_ap_rad.thy) | H1/RA1 correspondence, closure and the Galois law. |
| [utp_ap_ops](../../angelic-processes/utp_ap_ops.thy) | Operators, sequential and prefix calculations, transport laws. |
| [utp_ap_nd](../../angelic-processes/utp_ap_nd.thy) | NDAP, non-divergent transport and closure. |

<details>
<summary>Related research</summary>

[AP parallel](../parallel/AP.md) documents the research operator [ap_par](../../angelic-processes/utp_ap_parallel.thy#L121):

```text
P ∥AP[M] Q = H1((RA1 P) ∥RAD[M] (RA1 Q))
```

[ap_par_AP](../../angelic-processes/utp_ap_parallel.thy#L128) proves unconditional AP closure. [ap_par_RA1](../../angelic-processes/utp_ap_parallel.thy#L133) proves its exact RAD image; [ap_par_H1](../../angelic-processes/utp_ap_parallel.thy#L138) relates RAD operands transported through H1. The merge premises and further mapping laws belong in the parallel guide, not the paper coverage. [AP_feasible](../../angelic-processes/utp_ap_healthy.thy#L507) is also implementation research support: it requires a successful outcome at every started, non-waiting input, and is distinct from trace-growth productivity.

</details>
