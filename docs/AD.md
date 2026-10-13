# Angelic designs: definitions and results

[Paper coverage](PAPER_COVERAGE.md) · [RAD](RAD.md) · [AP](AP.md) · [AD parallel](AD_PARALLEL.md)

This guide connects the implementation to Ribeiro and Cavalcanti's [*Angelic processes for CSP via the UTP*](https://doi.org/10.1016/j.tcs.2018.10.008), Section 5 and Appendix A, and Ribeiro's [*Angelic Processes* thesis](https://arxiv.org/abs/1505.04726v2), Chapter 4 and Appendix C. It covers paper Definitions 15–25, Theorems 3–8, and the associated appendix results. **Support** denotes implementation support; **Qualification** identifies a restriction on a source claim.

## Alphabet and notation

Paper D16 / thesis D85 is represented by `astate`, `achoices` and `angelic_design` in [utp_ades_core.thy](../angelic-designs/utp_ades_core.thy):

```text
R(s,X)             R :: 's angelic_rel
P(ok,s,ok′,X)      P :: 's angelic_design
s :: 's           X :: 's set
```

The input contains one state; the output contains a set of available states. `ok` and `ok′` are outer design observations. The type specifies the alphabet, not design healthiness.

| Notation | Meaning |
| --- | --- |
| `P is H` | Ordinary design healthiness (`𝐇` in Isabelle). |
| `P is A`, `P is A2`, etc. | Fixed point of the named transformer. |
| `P ⊑ Q` | UTP refinement: `Q` implies `P` at every observation. |
| `P^f`, `P^t` | Final `ok′` set to false / true. |
| `pre_D P`, `post_D P` | Extracted relation-level design components. |
| `a ⊢r q` | Restricted design, with control-free relation components: `ok ∧ a ⇒ ok′ ∧ q`. |
| `a ⊢ q` | Design expression on the full observation alphabet. |
| `NE` | [ac_non_empty](../angelic-designs/utp_ades_healthy.thy#L542): `X ≠ {}`. |
| `;;A`, `;;Aᵈ`, `;;DA` | Relation choice composition, its full-alphabet version, and design composition, respectively. |

## Healthiness definitions

Paper D15 / thesis D88 supplies upward closure:

```text
PBMH R(s,X)           = ∃Y ⊆ X. R(s,Y)
PBMH_ades P(ok,s,ok′,X) = ∃Y ⊆ X. P(ok,s,ok′,Y)
```

[PBMH](../angelic-designs/utp_ades_core.thy#L146) is defined using [pbmh_step](../angelic-designs/utp_ades_core.thy#L142). [PBMH_ades](../angelic-designs/utp_ades_healthy.thy#L189) preserves the outer flags; [PBMH_ades_obs](../angelic-designs/utp_ades_healthy.thy#L223) gives the second formula.

| Source | Definition / implementation | Meaning |
| --- | --- | --- |
| Paper D17 / thesis D87 | [A0](../angelic-designs/utp_ades_healthy.thy#L555): `A0 P = P ∧ ((ok ∧ ¬P^f) ⇒ (ok′ ⇒ NE))` | Successful behaviour satisfying the precondition has an available final state. |
| Paper D17 / thesis D89 | [A1](../angelic-designs/utp_ades_healthy.thy#L621): `(¬PBMH(¬pre_D P)) ⊢r PBMH(post_D P)` | Closes the extracted design under enlarging the choice set. |
| Paper D17 / thesis D90 | [A](../angelic-designs/utp_ades_healthy.thy#L700): `A = A0 ∘ A1` | Angelic design healthiness; order matters. |
| Paper D20 / thesis D91 | [A2_rel](../angelic-designs/utp_ades_healthy.thy#L1139), [A2](../angelic-designs/utp_ades_healthy.thy#L1218) | Retains empty and singleton witnesses; expanded below. |
| Implementation qualification | [A3_rel](../angelic-designs/utp_ades_healthy.thy#L1388), [A3](../angelic-designs/utp_ades_healthy.thy#L1419) | Singleton-witness condition on the precondition; described below. |

[A1_eq_PBMH_ades](../angelic-designs/utp_ades_healthy.thy#L647) establishes `A1 P = PBMH_ades P` **when `P is H`**. An arbitrary predicate on the design alphabet does not satisfy this premise merely by type.

Paper T3 / thesis T.4.2.3 is [A0_design](../angelic-designs/utp_ades_healthy.thy#L600), with no extra premises on the displayed expression:

```text
A0(¬P^f ⊢ P^t) = (¬P^f ⊢ (P^t ∧ NE))
```

### A2 and A3

Paper T4 / thesis T.4.2.11 expands A2 into empty/singleton evaluation:

```text
A2 P(ok,s,ok′,X) = P(ok,s,ok′,{}) ∨ (∃z∈X. P(ok,s,ok′,{z}))
```

[A2_rel_eq_expanded](../angelic-designs/utp_ades_healthy.thy#L1227) proves the relation-level expansion. [A2_obs](../angelic-designs/utp_ades_healthy.thy#L1273), [A2_lift](../angelic-designs/utp_ades_healthy.thy#L1302) and [A2_def'](../angelic-designs/utp_ades_healthy.thy#L1307) connect it to the full design alphabet without changing its flags.

A3 is an additional condition in this development, used to repair the reverse-mapping claim. For a relation `a`:

```text
A3_rel a(s,X) = a(s,X) ∧ (X ≠ {} ∨ (∃z. a(s,{z})))
A3 P         = A3_rel(pre_D P) ⊢r post_D P
```

For `P is A`, [A3_healthy](../angelic-designs/utp_ades_healthy.thy#L1441) says that `P is A3` exactly when its precondition satisfies this singleton-witness condition. It allows preconditions to depend on final choices. On an H-healthy design, [A3_obs_H](../angelic-designs/utp_ades_healthy.thy#L1428) gives the equivalent observation rule:

```text
A3 P(ok,s,ok′,X) = P(ok,s,ok′,X)
                  ∨ (X = {} ∧ (∀z. P(ok,s,false,{z})))
```

### Idempotence and monotonicity

These facts have no healthy-input premises at their stated types.

| Transformer | Idempotence | Monotonicity |
| --- | --- | --- |
| PBMH | [PBMH_Idempotent](../angelic-designs/utp_ades_healthy.thy#L16) | [PBMH_Monotonic](../angelic-designs/utp_ades_healthy.thy#L23) |
| PBMH_ades | [PBMH_ades_Idempotent](../angelic-designs/utp_ades_healthy.thy#L375) | [PBMH_ades_Monotonic](../angelic-designs/utp_ades_healthy.thy#L203) |
| A0 | [A0_Idempotent](../angelic-designs/utp_ades_healthy.thy#L586) | [A0_Monotonic](../angelic-designs/utp_ades_healthy.thy#L592) |
| A1 | [A1_Idempotent](../angelic-designs/utp_ades_healthy.thy#L679) | [A1_Monotonic](../angelic-designs/utp_ades_healthy.thy#L695) |
| A | [A_Idempotent](../angelic-designs/utp_ades_healthy.thy#L817) | [A_Monotonic](../angelic-designs/utp_ades_healthy.thy#L709) |
| A2 | [A2_Idempotent](../angelic-designs/utp_ades_healthy.thy#L1282) | [A2_Monotonic](../angelic-designs/utp_ades_healthy.thy#L1289) |
| A3 | [A3_Idempotent](../angelic-designs/utp_ades_healthy.thy#L1547) | [A3_Monotonic](../angelic-designs/utp_ades_healthy.thy#L1541) |

[A3_A_commute](../angelic-designs/utp_ades_healthy.thy#L1550) and [A3_A2_commute](../angelic-designs/utp_ades_healthy.thy#L1563) show that A3 commutes with A and A2. [A3_preserves_A](../angelic-designs/utp_ades_healthy.thy#L1581) and [A3_preserves_A2](../angelic-designs/utp_ades_healthy.thy#L1585) provide the corresponding closure rules.

## Mapping ordinary designs and predicates

`D` below is an ordinary design-alphabet predicate; `a` and `q` are ordinary state relations. Paper D21–25 / thesis D100–104 introduce the mappings and their alphabet substitutions.

```text
p2ac D(ok,s,ok′,X) = ∃z∈X. D((ok,s),(ok′,z))
ac2p P((ok,s),(ok′,z)) = ∃Y ⊆ {z}. P(ok,s,ok′,Y)

d2ac(a ⊢r q) = ((∀z∈X. a(s,z)) ∧ (∃z. a(s,z)))
                ⊢r (∃z∈X. q(s,z))
```

| Source | Implementation | Role |
| --- | --- | --- |
| Paper D21 / thesis D100 | [d2ac](../angelic-designs/utp_ades_designs.thy#L101), [d2ac_rdesign](../angelic-designs/utp_ades_designs.thy#L107) | Constructs an angelic contract from an ordinary design. |
| Paper D22 / thesis D101 | [arel_state_subst](../angelic-designs/utp_ades_core.thy#L78), [ades_state_subst](../angelic-designs/utp_ades_core.thy#L85) | Typed records, lenses and substitution implement the state renaming. |
| Paper D23 / thesis D102 | [p2ac](../angelic-designs/utp_ades_designs.thy#L10), [p2ac_rel](../angelic-designs/utp_ades_designs.thy#L21) | Existential lifting of a predicate into a choice set. |
| Paper D24 / thesis D103 | [ac2p](../angelic-designs/utp_ades_designs.thy#L158), [ac2p_subset](../angelic-designs/utp_ades_designs.thy#L199), [ac2p_rel](../angelic-designs/utp_ades_designs.thy#L194) | Upward closure followed by singleton observation. |
| Paper D25 / thesis D104 | [StateII](../angelic-designs/utp_ades_core.thy#L39) | Embeds a state in the input-state record. |

`d2ac` and `p2ac` are different maps. [ac2p_healthy_obs](../angelic-designs/utp_ades_designs.thy#L166) reduces `ac2p P` to direct singleton evaluation only if `P is PBMH_ades`; otherwise the empty subset also matters.

### Paper mapping theorems

| Paper / thesis | Exact premises | Law | Implementation |
| --- | --- | --- | --- |
| T5 / T.4.6.7 | `D is H` | `ac2p(d2ac D) = D` | [ac2p_d2ac](../angelic-designs/utp_ades_designs.thy#L256) |
| T6 / T.4.6.8, **qualified** | `P is A` and `P is A3` | `P ⊑ d2ac(ac2p P)` | [d2ac_ac2p](../angelic-designs/utp_ades_designs.thy#L427) |
| T7 / T.4.6.9 | `P is A` and `P is A2` | `d2ac(ac2p P) ⊑ P` | [d2ac_ac2p_A2](../angelic-designs/utp_ades_designs.thy#L436) |
| T8 / T.4.6.10, **qualified** | `P is A`, `A2` and `A3` | `d2ac(ac2p P) = P` | [d2ac_ac2p_A2_eq](../angelic-designs/utp_ades_designs.thy#L456) |
| Support | `P is A` | `P ⊑ d2ac(ac2p P) ⟷ P is A3` | [d2ac_ac2p_iff_A3](../angelic-designs/utp_ades_designs.thy#L357) |
| Support | `P is A` and `A3`; `D is H` | `ac2p P ⊑ D ⟷ P ⊑ d2ac D` | [ac2p_d2ac_galois](../angelic-designs/utp_ades_designs.thy#L467) |

The A3 premise is necessary for T6 on the implemented A carrier. [P_dummy](../angelic-designs/utp_ades_designs.thy#L317) is `(X = {} ⊢r X ≠ {})`: [P_dummy_is_A](../angelic-designs/utp_ades_designs.thy#L322) proves its A-healthiness, while [P_dummy_fails_theorem6](../angelic-designs/utp_ades_designs.thy#L350) refutes the unqualified refinement. [ac2p_P_dummy](../angelic-designs/utp_ades_designs.thy#L339) and [d2ac_ac2p_P_dummy](../angelic-designs/utp_ades_designs.thy#L344) calculate its round trip.

### Mapping support and appendix results

| Source | Premises | Result / role | Implementation |
| --- | --- | --- | --- |
| Support | None | `d2ac D` is A, A2 and A3. | [d2ac_is_A](../angelic-designs/utp_ades_designs.thy#L133), [d2ac_is_A2](../angelic-designs/utp_ades_designs.thy#L136), [d2ac_is_A3](../angelic-designs/utp_ades_designs.thy#L139) |
| Support | `P is H` | `ac2p P is H`. | [ac2p_H_closure](../angelic-designs/utp_ades_designs.thy#L238) |
| Support | None | The three maps are monotonic. | [p2ac_mono](../angelic-designs/utp_ades_designs.thy#L55), [ac2p_mono](../angelic-designs/utp_ades_designs.thy#L187), [d2ac_mono](../angelic-designs/utp_ades_designs.thy#L146) |
| Paper L4 | None | Existential alternative for `ac2p`, constraining every member of the witness set to the output state. | [ac2p_alt](../angelic-designs/utp_ades_designs.thy#L216) |
| Paper L24 | `P is H` | `ac2p P = (¬ac2p(P^f) ⊢ ac2p(P^t))`. | [ac2p_design](../angelic-designs/utp_ades_designs.thy#L231) |
| Paper L25–26 | None | `ac2p(PBMH_ades P) = ac2p P`; `PBMH_ades(p2ac D) = p2ac D`. | [ac2p_PBMH_ades](../angelic-designs/utp_ades_designs.thy#L172), [PBMH_ades_p2ac](../angelic-designs/utp_ades_designs.thy#L91) |
| Paper T72 | None beyond the displayed form | `NE ∧ p2ac(¬F ⊢ T) = NE ∧ (¬p2ac F ⊢ p2ac T)`. | [p2ac_design_nonempty](../angelic-designs/utp_ades_designs.thy#L81); restricted-design form [p2ac_design](../angelic-designs/utp_ades_designs.thy#L74) |
| Paper L6, relation-level support | None | `p2ac_rel(ac2p_rel R) = A2_rel R ∧ (X ≠ {})`. | [p2ac_ac2p_rel_A2](../angelic-designs/utp_ades_designs.thy#L278) |

The full reactive `p2ac`/`ac2p` round trips are collected in [RAD: round trips and A2](RAD.md#round-trips-and-a2).

## Operators and sequential laws

| Source | Definition | Implementation |
| --- | --- | --- |
| Thesis D94 | Assignment guarantees that the updated input state belongs to `X`. | [assign_arel](../angelic-designs/utp_ades_ops.thy#L10), [assigns_ades](../angelic-designs/utp_ades_ops.thy#L16) |
| Thesis D97 | `Skip_AD = true ⊢r (s ∈ X)`. | [Skip_AD](../angelic-designs/utp_ades_ops.thy#L29) |
| Thesis D98–99 | Demonic choice is disjunction; angelic choice is conjunction. | [angelic_design_demonic](../angelic-designs/utp_ades_ops.thy#L42), [angelic_design_angelic](../angelic-designs/utp_ades_ops.thy#L55) |
| Paper D19 / thesis D96 | `(R ;;A S)(s,X) = R(s,{z. S(z,X)})`. | [aseq](../angelic-designs/utp_ades_ops.thy#L77) |
| Support | The same choice construction with outer flags retained. | [aseq_ades](../angelic-designs/utp_ades_ops.thy#L150) |
| Paper D18 / thesis D95 | Hide the intermediate termination flag as well as composing choices. | [angelic_design_seq](../angelic-designs/utp_ades_ops.thy#L260) |

The full design composition is:

```text
(P ;;DA Q)(ok,s,ok′,X) =
  ∃b. P(ok,s,b,{z. Q(b,z,ok′,X)})
```

Thesis T.4.5.1 gives a pre/postcondition calculation. If `PBMH(¬a) = ¬a` and `PBMH q = q`, [angelic_design_seq_eq_simplified](../angelic-designs/utp_ades_ops.thy#L348) rewrites `(a ⊢r q) ;;DA (b ⊢r r)` using [angelic_design_seq_simplified](../angelic-designs/utp_ades_ops.thy#L328):

```text
pre  = ¬((¬pre_D P) ;;A true) ∧ ¬(post_D P ;;A ¬pre_D Q)
post = post_D P ;;A (pre_D Q ⇒ post_D Q)
result = pre ⊢r post
```

Here `P = (a ⊢r q)` and `Q = (b ⊢r r)`; the extracted postconditions include the usual design implication. [angelic_rdesign_seq](../angelic-designs/utp_ades_healthy.thy#L488) provides a direct restricted-component presentation.

| Source | Premises | Result | Implementation |
| --- | --- | --- | --- |
| Thesis §4.4 | `R`, `S` both PBMH | `R ;;A S is PBMH`. | [PBMH_aseq_closure](../angelic-designs/utp_ades_healthy.thy#L125) |
| Thesis T.4.5.3 | `P`, `Q` both A | `P ;;DA Q is A`. | [angelic_design_seq_A_closure](../angelic-designs/utp_ades_healthy.thy#L1013) |
| Thesis T.C.4.1 | `P`, `Q` both A2 | `P ;;DA Q is A2`. | [angelic_design_seq_A2_closure](../angelic-designs/utp_ades_healthy.thy#L1338) |
| Thesis T.4.5.5–6 | `P is H` for the identity law | `Skip_AD is A`; `Skip_AD ;;DA P = P`. | [Skip_AD_is_A](../angelic-designs/utp_ades_healthy.thy#L1035), [Skip_AD_seq_left_unit](../angelic-designs/utp_ades_healthy.thy#L1038) |
| Thesis T.4.5.8, **qualified** | `P is A` | `P ;;DA Skip_AD = P ⟷ P is N` (normal). | [Skip_AD_seq_right_unit_iff_normal](../angelic-designs/utp_ades_healthy.thy#L1115) |
| Thesis T.4.5.15 | None | `(P ∨ Q) ;;DA R = (P ;;DA R) ∨ (Q ;;DA R)`. | [angelic_design_seq_demonic](../angelic-designs/utp_ades_ops.thy#L335) |
| Support | None | `p2ac(D ;; E) = p2ac D ;;DA p2ac E`. | [p2ac_seq](../angelic-designs/utp_ades_designs.thy#L489) |

[Skip_AD_seq_right_unit_iff](../angelic-designs/utp_ades_healthy.thy#L1092) identifies normality here with independence of `pre_D P` from the final choice set. [Skip_AD_not_unconditional_right_unit](../angelic-designs/utp_ades_designs.thy#L335) is the counterexample. Relation-level [aseq_assoc](../angelic-designs/utp_ades_ops.thy#L138) does **not** establish unrestricted associativity of `;;DA`.

## Remaining appendix lemmas

| Paper | Premises | Result / implementation |
| --- | --- | --- |
| L3 | None | `PBMH(X = {}) = true`: [PBMH_ac_empty](../angelic-designs/utp_ades_healthy.thy#L35). |
| L15 | None | Nonempty choices are PBMH-healthy: [PBMH_ac_non_empty](../angelic-designs/utp_ades_healthy.thy#L40), [PBMH_ades_ac_non_empty](../angelic-designs/utp_ades_healthy.thy#L550). |
| L16 | Restricted-design components | PBMH of a design: [PBMH_ades_rdesign](../angelic-designs/utp_ades_healthy.thy#L510), [PBMH_rdesign](../angelic-designs/utp_ades_healthy.thy#L636). |
| L17 | Restricted-design components | A2 of a design: [A2_rdesign](../angelic-designs/utp_ades_healthy.thy#L1262). |
| L18 | Substitution depends only on state, enforced by its type | A commutes with substitution: [A_state_subst](../angelic-designs/utp_ades_healthy.thy#L838). |
| T64–65 | None | PBMH_ades commutes with H1 and H2: [PBMH_ades_H1_commute](../angelic-designs/utp_ades_healthy.thy#L516), [PBMH_ades_H2_commute](../angelic-designs/utp_ades_healthy.thy#L523). Relation/guard presentations: [PBMH_H1_commute](../angelic-designs/utp_ades_healthy.thy#L171), [PBMH_H2_commute](../angelic-designs/utp_ades_healthy.thy#L181). |
| L27–28 | — | No separate named mechanisation of the general alphabet calculus; the mapping proofs use typed records, lenses and substitution. |

## Supporting files and research

| File | Contents |
| --- | --- |
| [utp_ades_core](../angelic-designs/utp_ades_core.thy) | Alphabet, observation constructors, state substitution and PBMH. |
| [utp_ades_ops](../angelic-designs/utp_ades_ops.thy) | Assignment, choice and the three sequential operators. |
| [utp_ades_healthy](../angelic-designs/utp_ades_healthy.thy) | A0–A3, design forms, closure and identity laws. |
| [utp_ades_designs](../angelic-designs/utp_ades_designs.thy) | Mappings, round trips and counterexamples. |

[AD parallel](AD_PARALLEL.md) documents the later merge operator and its healthiness conditions. Those results have no numbered AD-parallel counterpart in the source material above. General sequential associativity and further thesis algebra remain separate from the paper coverage recorded here.
