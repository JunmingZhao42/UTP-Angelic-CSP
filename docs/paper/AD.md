# Angelic designs

[Paper coverage](README.md) · [RAD](RAD.md) · [AP](AP.md)

Paper §5 and Appendix A; thesis Chapter 4 and Appendix C. [Known correspondence corrections](../reviews/2026-10-14-source-correspondence.md) remain deferred.

[Alphabet](#alphabet-and-notation) · [§5.1 Healthiness](#51-healthiness-conditions) · [§5.2 Composition](#52-sequential-composition) · [§5.3 Without angelic nondeterminism](#53-characterising-designs-without-angelic-nondeterminism) · [§5.4 To AD](#54-from-designs-to-angelic-designs) · [§5.5 From AD](#55-from-angelic-designs-to-designs) · [§5.6 Correspondence](#56-isomorphism-and-galois-connection) · [Appendix](#appendix-a-supporting-results) · [Theory files](#theory-files)

## Alphabet and notation

An observation has an initial state, a set of final choices, and outer `ok`/`ok′` flags. `P is X` states a healthiness condition; the alphabet type alone does not imply it.

Across these guides, “None” means no extra healthiness premise at the declared type; “—” means no separate premise note. Collapsed supplementary blocks contain selected thesis results and implementation support.

D15 and L3 are the PBMH background from paper §4.1; D16 introduces the alphabet in §5.

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d15"></a>**D15** / D88 | Upward closure of final choices | — | [PBMH](../../angelic-designs/utp_ades_core.thy#L146), [PBMH_ades](../../angelic-designs/utp_ades_healthy.thy#L189) |
| <a id="l3"></a>**L3** | Upward closure of the empty-choice predicate | None | [PBMH_ac_empty](../../angelic-designs/utp_ades_healthy.thy#L35) |
| <a id="d16"></a>**D16** / D85 | Angelic design alphabet | — | [utp_ades_core.thy](../../angelic-designs/utp_ades_core.thy) |

## §5.1 Healthiness conditions

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d17"></a>**D17** / D87, D89–90 | A0, A1 and combined A healthiness | — | [A0](../../angelic-designs/utp_ades_healthy.thy#L555), [A1](../../angelic-designs/utp_ades_healthy.thy#L621), [A](../../angelic-designs/utp_ades_healthy.thy#L700) |
| <a id="t3"></a>**T3** / T.4.2.3 | A0 adds nonempty successful choices | Reconstructed design form | [A0_design](../../angelic-designs/utp_ades_healthy.thy#L600) |

[A1_eq_PBMH_ades](../../angelic-designs/utp_ades_healthy.thy#L647) identifies A1 with upward closure only on H-healthy designs.

<details>
<summary>Supplementary results</summary>

`PBMH` closes state-to-choice relations; `PBMH_ades` applies that closure inside the full design alphabet, preserving outer control observations. `A2` likewise preserves those observations when normalising empty and singleton choices.

Alphabet lifting adds observation fields. [arel_to_ades](../../angelic-designs/utp_ades_core.thy#L92) instead constructs the contract `true ⊢r P`.

</details>

## §5.2 Sequential composition

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d18"></a>**D18** / D95 | Design sequential composition | — | [angelic_design_seq](../../angelic-designs/utp_ades_ops.thy#L260) |
| <a id="d19"></a>**D19** / D96 | Relation choice composition | — | [aseq](../../angelic-designs/utp_ades_ops.thy#L77) |

<a id="composition-support"></a>

<details>
<summary>Supplementary results</summary>

`aseq` composes state-to-choice relations; [aseq_ades](../../angelic-designs/utp_ades_ops.thy#L150) works on full observations. `angelic_design_seq` additionally hides the intermediate termination observation.

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| D94 | Assignment | None | [assign_arel](../../angelic-designs/utp_ades_ops.thy#L10), [assigns_ades](../../angelic-designs/utp_ades_ops.thy#L16) |
| D97 | Skip | None | [Skip_AD](../../angelic-designs/utp_ades_ops.thy#L29) |
| D98–99 | Demonic and angelic choice | None | [angelic_design_demonic](../../angelic-designs/utp_ades_ops.thy#L42), [angelic_design_angelic](../../angelic-designs/utp_ades_ops.thy#L55) |
| T.4.5.1 | Sequential pre/postcondition calculation | PBMH-healthy left failure and success components | [angelic_rdesign_seq](../../angelic-designs/utp_ades_healthy.thy#L488), [angelic_design_seq_eq_simplified](../../angelic-designs/utp_ades_ops.thy#L348) |
| §4.4 | Relation composition preserves PBMH | Both operands PBMH | [PBMH_aseq_closure](../../angelic-designs/utp_ades_healthy.thy#L125) |
| T.4.5.3 | Design composition preserves A | Both operands A | [angelic_design_seq_A_closure](../../angelic-designs/utp_ades_healthy.thy#L1013) |
| T.C.4.1 | Design composition preserves A2 | Both operands A2 | [angelic_design_seq_A2_closure](../../angelic-designs/utp_ades_healthy.thy#L1338) |
| T.4.5.5–6 | Skip healthiness and left identity | None for healthiness; P is H for identity | [Skip_AD_is_A](../../angelic-designs/utp_ades_healthy.thy#L1035), [Skip_AD_seq_left_unit](../../angelic-designs/utp_ades_healthy.thy#L1038) |
| T.4.5.8, qualified | Right identity iff normal | P is A | [Skip_AD_seq_right_unit_iff_normal](../../angelic-designs/utp_ades_healthy.thy#L1115) |
| T.4.5.15 | Left demonic distribution | None | [angelic_design_seq_demonic](../../angelic-designs/utp_ades_ops.thy#L335) |

</details>

## §5.3 Characterising designs without angelic nondeterminism

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d20"></a>**D20** / D91 | Empty and singleton choice healthiness | — | [A2_rel](../../angelic-designs/utp_ades_healthy.thy#L1139), [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) |
| <a id="t4"></a>**T4** / T.4.2.11 | A2 expansion through empty and singleton choices | None | [A2_obs](../../angelic-designs/utp_ades_healthy.thy#L1273), [A2_def'](../../angelic-designs/utp_ades_healthy.thy#L1307) |

## §5.4 From designs to angelic designs

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d21"></a>**D21** / D100 | Ordinary design to angelic design | — | [d2ac](../../angelic-designs/utp_ades_designs.thy#L101) |
| <a id="d22"></a>**D22** / D101 | State renaming through typed substitutions | — | [arel_state_subst](../../angelic-designs/utp_ades_core.thy#L78), [ades_state_subst](../../angelic-designs/utp_ades_core.thy#L85) |
| <a id="d23"></a>**D23** / D102 | Lift an ordinary predicate to choices | — | [p2ac](../../angelic-designs/utp_ades_designs.thy#L10) |

## §5.5 From angelic designs to designs

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="d24"></a>**D24** / D103 | Map choices to an ordinary predicate | — | [ac2p](../../angelic-designs/utp_ades_designs.thy#L158) |
| <a id="d25"></a>**D25** / D104 | Input-state record embedding | — | [StateII](../../angelic-designs/utp_ades_core.thy#L39) |
| <a id="l4"></a>**L4** | Existential witness-set form of ac2p | None | [ac2p_alt](../../angelic-designs/utp_ades_designs.thy#L216) |

<details>
<summary>Supplementary results</summary>

`ac2p P` evaluates `PBMH_ades P` at a singleton choice while retaining outer design flags. [Direct singleton evaluation](../../angelic-designs/utp_ades_designs.thy#L166) requires `P is PBMH_ades`; empty-choice behaviour still matters.

</details>

## §5.6 Isomorphism and Galois connection

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t5"></a>**T5** / T.4.6.7 | Ordinary-design round trip | D is H | [ac2p_d2ac](../../angelic-designs/utp_ades_designs.thy#L256) |
| <a id="t6"></a>**T6** / T.4.6.8 | Reverse-mapping refinement | P is A and A3; qualified | [d2ac_ac2p](../../angelic-designs/utp_ades_designs.thy#L427) |
| <a id="t7"></a>**T7** / T.4.6.9 | Opposite reverse-mapping refinement | P is A and A2 | [d2ac_ac2p_A2](../../angelic-designs/utp_ades_designs.thy#L436) |
| <a id="t8"></a>**T8** / T.4.6.10 | Exact reverse-mapping round trip | P is A, A2 and A3; qualified | [d2ac_ac2p_A2_eq](../../angelic-designs/utp_ades_designs.thy#L456) |

T6 and T8 require the additional A3 condition. [d2ac_ac2p_iff_A3](../../angelic-designs/utp_ades_designs.thy#L357) characterises it; [P_dummy_fails_theorem6](../../angelic-designs/utp_ades_designs.thy#L350) supplies the counterexample.

<details>
<summary>Supplementary results</summary>

For the additional mapping condition, start with [A3](../../angelic-designs/utp_ades_healthy.thy#L1419), [A3_healthy](../../angelic-designs/utp_ades_healthy.thy#L1441). Mapping closure and the qualified Galois law are in [d2ac_is_A](../../angelic-designs/utp_ades_designs.thy#L133), [d2ac_is_A2](../../angelic-designs/utp_ades_designs.thy#L136), [d2ac_is_A3](../../angelic-designs/utp_ades_designs.thy#L139), [ac2p_d2ac_galois](../../angelic-designs/utp_ades_designs.thy#L467). The latter requires an A/A3-healthy angelic operand and an H-healthy ordinary design.

</details>

## Appendix A: supporting results

| Paper / thesis | Brief idea / conditions | Essential premises / notes | Isabelle |
| --- | --- | --- | --- |
| <a id="t64"></a>**T64** | H1 commutes with upward closure | None | [PBMH_ades_H1_commute](../../angelic-designs/utp_ades_healthy.thy#L516) |
| <a id="t65"></a>**T65** | H2 commutes with upward closure | None | [PBMH_ades_H2_commute](../../angelic-designs/utp_ades_healthy.thy#L523) |
| <a id="t72"></a>**T72** | Lift a reconstructed design through p2ac | Nonempty final choices on both sides | [p2ac_design_nonempty](../../angelic-designs/utp_ades_designs.thy#L81) |
| <a id="l15"></a>**L15** | Nonempty choices are upward closed | None | [PBMH_ac_non_empty](../../angelic-designs/utp_ades_healthy.thy#L40), [PBMH_ades_ac_non_empty](../../angelic-designs/utp_ades_healthy.thy#L550) |
| <a id="l16"></a>**L16** | Upward closure of a design | Restricted-design components | [PBMH_ades_rdesign](../../angelic-designs/utp_ades_healthy.thy#L510), [PBMH_rdesign](../../angelic-designs/utp_ades_healthy.thy#L636) |
| <a id="l17"></a>**L17** | A2 of a design | Restricted-design components | [A2_rdesign](../../angelic-designs/utp_ades_healthy.thy#L1262) |
| <a id="l18"></a>**L18** | A commutes with state substitution | State-only substitution, enforced by type | [A_state_subst](../../angelic-designs/utp_ades_healthy.thy#L838) |
| <a id="l24"></a>**L24** | Design decomposition of ac2p | P is H | [ac2p_design](../../angelic-designs/utp_ades_designs.thy#L231) |
| <a id="l25"></a>**L25** | Upward closure leaves ac2p unchanged | None | [ac2p_PBMH_ades](../../angelic-designs/utp_ades_designs.thy#L172) |
| <a id="l26"></a>**L26** | p2ac produces upward-closed choices | None | [PBMH_ades_p2ac](../../angelic-designs/utp_ades_designs.thy#L91) |
| <a id="l27"></a>**L27** | General alphabet substitution calculus | No separate named mechanisation | — |
| <a id="l28"></a>**L28** | General alphabet substitution calculus | No separate named mechanisation | — |

The mapping proofs use typed records, lenses and substitution for the general alphabet calculus of L27–28.

## Theory files

| File | Contents |
| --- | --- |
| [utp_ades_core](../../angelic-designs/utp_ades_core.thy) | Alphabet, observation constructors, state substitution and PBMH. |
| [utp_ades_ops](../../angelic-designs/utp_ades_ops.thy) | Assignment, choice and the three sequential operators. |
| [utp_ades_healthy](../../angelic-designs/utp_ades_healthy.thy) | A0–A3, design forms, closure and identity laws. |
| [utp_ades_designs](../../angelic-designs/utp_ades_designs.thy) | Mappings, round trips and counterexamples. |

<details>
<summary>Related research</summary>

[AD parallel](../parallel/AD.md) documents the later merge operator and its healthiness conditions. Those results have no numbered AD-parallel counterpart in the source material above. General sequential associativity and further thesis algebra remain separate from the paper coverage recorded here.

</details>
