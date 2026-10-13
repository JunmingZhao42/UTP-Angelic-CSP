# Angelic processes: definitions and results

[Paper coverage](PAPER_COVERAGE.md) · [AD](AD.md) · [RAD](RAD.md) · [AP parallel](AP_PARALLEL.md)

This guide connects the implementation to Ribeiro and Cavalcanti's [*Angelic processes for CSP via the UTP*](https://doi.org/10.1016/j.tcs.2018.10.008), Section 7, and Ribeiro's [*Angelic Processes* thesis](https://arxiv.org/abs/1505.04726v2), Chapter 6 and Appendix H. It covers paper Definitions 46–57, Theorems 36–63 and Lemmas 10–14. **Support** denotes implementation support; **Research** denotes the later parallel development.

## Alphabet and notation

AP uses the same alphabet as [RAD](RAD.md#alphabet-and-notation):

```text
P(ok,s,ok′,X)
s :: ('t,'e) rad_state = ('t,'e set) rea_vars_ext
X :: ('t,'e) rad_state set
```

Each state contains `wait`, `tr` and a refusal set in `more`. AP changes the healthiness conditions, particularly the treatment of divergence; it introduces no new state representation or conversion wrapper.

| Notation | Meaning |
| --- | --- |
| `P is AP`, `P is RAD`, `P is NDAP` | Fixed point of the named transformer; the premises are distinct. |
| `P ⊑ Q` | UTP refinement: `Q` implies `P` at every observation. |
| `P_f` | Initial waiting flag set to false. |
| `F(P) = (P_f)^f`, `T(P) = (P_f)^t` | Additionally set final `ok′` to false / true. Initial `ok` remains free. |
| `B = RA2 ∘ PBMH_ades` | Document abbreviation for normalising a failure component. |
| `C = RA2 ∘ RA1 ∘ PBMH_ades` | Document abbreviation for normalising a successful component. |
| `J = ades_state_choice` | `J(ok,s,ok′,X)` means `s ∈ X`. |
| `U ◁ b ▷ V` | `U` if `b`, otherwise `V`. |
| `;;A` / `;;DA` | [aseq_ades](../angelic-designs/utp_ades_ops.thy#L150) / [angelic_design_seq](../angelic-designs/utp_ades_ops.thy#L260): full-alphabet choice composition / design composition. |

General results use `'t::trace`; event-prefix results use `'e list`. Definitions of RA1, RA2, A and PBMH are in the [RAD](RAD.md#healthiness-definitions) and [AD](AD.md#healthiness-definitions) guides.

## Healthiness definitions

| Paper / thesis | Definition | Implementation |
| --- | --- | --- |
| D47 / D128 | `II_AP = H1(ok′ ∧ J)` | [II_AP](../angelic-processes/utp_ap_healthy.thy#L10) |
| D48 / D129 | `RA3AP P = II_AP ◁ s.wait ▷ P` | [RA3AP](../angelic-processes/utp_ap_healthy.thy#L34) |
| D46 / D127 | `AP = RA3AP ∘ RA2 ∘ A ∘ H1 ∘ CSPA2` | [AP](../angelic-processes/utp_ap_healthy.thy#L173) |
| D49 / D130 | `NDAP P = Choice_AP ⊔AP P` | [NDAP](../angelic-processes/utp_ap_nd.thy#L10) |

Composition applies from right to left; `CSPA2 = H2`. The waiting identity has the observation form:

```text
II_AP(ok,s,ok′,X) = ¬ok ∨ (ok′ ∧ s ∈ X)
```

Unlike `II_Rac`, it places no trace-extension requirement on unstarted observations. AP's normal form below also treats failure without RA1, while its successful component uses RA1. This difference permits the divergence behaviour illustrated in the examples.

### Idempotence, monotonicity and component closure

| Transformer / result | Premises | Implementation |
| --- | --- | --- |
| RA3AP is idempotent and monotonic (thesis T.6.2.1–2). | None | [RA3AP_Idempotent](../angelic-processes/utp_ap_healthy.thy#L40), [RA3AP_Monotonic](../angelic-processes/utp_ap_healthy.thy#L47) |
| AP is idempotent and monotonic. | None | [AP_Idempotent](../angelic-processes/utp_ap_healthy.thy#L393), [AP_Monotonic](../angelic-processes/utp_ap_healthy.thy#L182) |
| NDAP is idempotent and monotonic. | None | [NDAP_Idempotent](../angelic-processes/utp_ap_nd.thy#L20), [NDAP_Monotonic](../angelic-processes/utp_ap_nd.thy#L28) |
| RA3AP distributes over conjunction and disjunction (thesis T.6.2.3–4). | None | [RA3AP_conj](../angelic-processes/utp_ap_healthy.thy#L50), [RA3AP_disj](../angelic-processes/utp_ap_healthy.thy#L53) |
| RA2 and RA3AP commute (thesis T.6.2.7). | None | [RA2_RA3AP_commute](../angelic-processes/utp_ap_healthy.thy#L98) |
| `P is H`, `PBMH_ades` and `RA3AP`. | `P is AP` | [AP_is_H](../angelic-processes/utp_ap_healthy.thy#L433), [AP_is_PBMH_ades](../angelic-processes/utp_ap_healthy.thy#L423), [AP_is_RA3AP](../angelic-processes/utp_ap_healthy.thy#L402) |
| `NDAP P is AP`. | `P is AP` | [NDAP_AP_closure](../angelic-processes/utp_ap_nd.thy#L31) |

### Normal forms

Paper T36 / thesis T.6.2.8, [AP_design_form](../angelic-processes/utp_ap_healthy.thy#L186), holds for arbitrary `P`:

```text
AP P = (RA3AP ∘ RA2 ∘ A)(¬F(P) ⊢ T(P))
```

Paper T37 / thesis T.6.2.9, [AP_wait_cond_design](../angelic-processes/utp_ap_healthy.thy#L204), expands this into a design, also without premises:

```text
AP P = (true ◁ s.wait ▷ ¬B(F(P)))
       ⊢ (J ◁ s.wait ▷ C(T(P)))
```

For AP-healthy `P`, this is a representation of `P` itself. When the initial state is waiting, the contract preserves it through `J`. Otherwise the precondition excludes the normalised failure component and the postcondition supplies trace-extending choices.

## Correspondence with RAD

H1 maps RAD into AP; RA1 maps AP into RAD. These operate on the same predicates, with no encoding or decoding.

| Source | Premises | Law | Implementation |
| --- | --- | --- | --- |
| Support | `P is RAD` | `H1 P is AP` | [H1_RAD_AP_closure](../angelic-processes/utp_ap_rad.thy#L67) |
| Support | `P is AP` | `RA1 P is RAD` | [RA1_AP_RAD_closure](../angelic-processes/utp_ap_rad.thy#L159) |
| Paper T40 / thesis T.6.3.2 | None | `RA1(AP P) = (RA ∘ A)(¬F(P) ⊢ T(P)) = RAD P` | [RA1_AP_design](../angelic-processes/utp_ap_rad.thy#L135), [RA1_AP_RAD](../angelic-processes/utp_ap_rad.thy#L155) |
| Paper T41 / thesis T.6.3.3 | None | `RA1(H1(RAD P)) = RAD P` | [RA1_H1_RAD](../angelic-processes/utp_ap_rad.thy#L172) |
| Paper T42 / thesis T.6.3.4 | None | `AP P ⊑ H1(RA1(AP P))` | [H1_RA1_AP_refine](../angelic-processes/utp_ap_rad.thy#L184) |
| Paper T43 / thesis T.6.3.5 | None | `H1(RA1(NDAP(AP P))) = NDAP(AP P)` | [H1_RA1_NDAP_AP](../angelic-processes/utp_ap_nd.thy#L188) |
| Support | `P is AP`; `Q is RAD` | `RA1 P ⊑ Q ⟷ P ⊑ H1 Q` | [AP_RAD_galois](../angelic-processes/utp_ap_rad.thy#L201) |

Paper T39 / thesis T.6.3.1, [H1_RAD_design](../angelic-processes/utp_ap_rad.thy#L10), calculates the RAD-to-AP image for arbitrary `P`:

```text
H1(RAD P) = (true ◁ s.wait ▷ ¬RA1(B(F(P))))
            ⊢ RA3AP(C(T(P)))
```

Paper L10, [H1_RA_A_true_design](../angelic-processes/utp_ap_rad.thy#L80), gives its true-precondition form:

```text
H1((RA ∘ A)(true ⊢ T(P))) = (true ⊢ RA3AP(C(T(P))))
```

The RAD round trip is exact; the unrestricted AP round trip is a refinement. T43 recovers equality for the NDAP/AP image. Accordingly, transport through RAD can identify distinct divergent AP predicates.

## Process operators

| Paper / thesis definition | Formula | Implementation |
| --- | --- | --- |
| D50 / D131 | `P ⊔AP Q = P ∧ Q` | [achoice_AP](../angelic-processes/utp_ap_ops.thy#L9), [AP_angelic_choice](../angelic-processes/utp_ap_ops.thy#L16) |
| D51 / D132 | `P ⊓AP Q = P ∨ Q` | [dchoice_AP](../angelic-processes/utp_ap_ops.thy#L99), [AP_demonic_choice](../angelic-processes/utp_ap_ops.thy#L106) |
| D52 / D133 | `Chaos_AP = AP(false ⊢ true)` | [Chaos_AP](../angelic-processes/utp_ap_ops.thy#L162) |
| D53 / D134 | `ChaosCSP_AP = AP(¬RA1(true) ⊢ true)` | [ChaosCSP_AP](../angelic-processes/utp_ap_ops.thy#L216) |
| D54 / D135 | `Choice_AP = AP(true ⊢ ac_non_empty)` | [Choice_AP](../angelic-processes/utp_ap_ops.thy#L303) |
| D55 / D136 | `Stop_AP = AP(true ⊢ stop_post)` | [Stop_AP](../angelic-processes/utp_ap_ops.thy#L347) |
| D56 / D137 | `Skip_AP = AP(true ⊢ skip_post)` | [Skip_AP](../angelic-processes/utp_ap_ops.thy#L377) |
| D57 / D138 | `PrefixSkip_AP a = AP(true ⊢ prefix_post a)` | [PrefixSkip_AP](../angelic-processes/utp_ap_ops.thy#L935) |
| Paper §7.4.7 / thesis §6.4.7 | Sequential composition uses `;;DA`. | [angelic_design_seq](../angelic-designs/utp_ades_ops.thy#L260) |
| Paper §7.4.8 / thesis §6.4.8 | `a →AP P = PrefixSkip_AP a ;;DA P` | [Prefix_AP](../angelic-processes/utp_ap_ops.thy#L967) |

The shared `stop_post`, `skip_post` and `prefix_post` formulas are in [RAD: primitive definitions](RAD.md#singleton-choice-and-primitive-definitions). There is no separately defined AP external-choice operator in these theories.

Paper L11 / thesis L.6.4.1, [Chaos_AP_design](../angelic-processes/utp_ap_ops.thy#L174), and thesis L.6.4.2, [ChaosCSP_AP_design](../angelic-processes/utp_ap_ops.thy#L242), expose the difference between the two divergence processes:

```text
Chaos_AP    = s.wait ⊢ J
ChaosCSP_AP = (s.wait ∨ ¬RA1(true)) ⊢ (s.wait ∧ J)
```

Both are AP-healthy. `Chaos_AP` is the AP bottom ([bottom_AP_is_Chaos](../angelic-processes/utp_ap_ops.thy#L169)). The RAD bottom maps to `ChaosCSP_AP`, as T51 below states.

### Choice and primitive mapping laws

All primitive mapping rows have no extra premises. Prefix rows use list traces.

| Source | Premises | Law | Implementation |
| --- | --- | --- | --- |
| Paper T45 / thesis T.6.4.3 | `P`, `Q` both RAD | `RA1(H1 P ⊔AP H1 Q) = P ⊔RAD Q` | [RA1_H1_angelic_choice](../angelic-processes/utp_ap_ops.thy#L73) |
| Paper T46 / thesis T.6.4.4 | `P`, `Q` both AP | `P ⊔AP Q ⊑ H1(RA1 P ⊔RAD RA1 Q)` | [H1_RA1_angelic_choice_refine](../angelic-processes/utp_ap_ops.thy#L81) |
| Paper T48 / thesis T.6.4.7 | `P`, `Q` both RAD | `RA1(H1 P ⊓AP H1 Q) = P ⊓RAD Q` | [RA1_H1_demonic_choice](../angelic-processes/utp_ap_ops.thy#L135) |
| Paper T49 / thesis T.6.4.8 | `P`, `Q` both AP | `P ⊓AP Q ⊑ H1(RA1 P ⊓RAD RA1 Q)` | [H1_RA1_demonic_choice_refine](../angelic-processes/utp_ap_ops.thy#L143) |
| Paper T50 / thesis T.6.4.9 | `P is AP` | `P ⊔AP Chaos_AP = P` | [Chaos_AP_angelic_choice_unit](../angelic-processes/utp_ap_ops.thy#L200) |
| Paper T51–52 / thesis T.6.4.10–11 | None | `H1 Chaos_RAD = ChaosCSP_AP`; `RA1 ChaosCSP_AP = Chaos_RAD` | [H1_Chaos_RAD](../angelic-processes/utp_ap_ops.thy#L278), [RA1_ChaosCSP_AP](../angelic-processes/utp_ap_ops.thy#L295) |
| Paper T53–54 / thesis T.6.4.12–13 | None | `H1 Choice_RAD = Choice_AP`; `RA1 Choice_AP = Choice_RAD` | [H1_Choice_RAD](../angelic-processes/utp_ap_ops.thy#L333), [RA1_Choice_AP](../angelic-processes/utp_ap_ops.thy#L339) |
| Paper T55–56 / thesis T.6.4.14–15 | None | `H1 Stop_RAD = Stop_AP`; `RA1 Stop_AP = Stop_RAD` | [H1_Stop_RAD](../angelic-processes/utp_ap_ops.thy#L363), [RA1_Stop_AP](../angelic-processes/utp_ap_ops.thy#L369) |
| Paper T57–58 / thesis T.6.4.16–17 | None | `H1 Skip_RAD = Skip_AP`; `RA1 Skip_AP = Skip_RAD` | [H1_Skip_RAD](../angelic-processes/utp_ap_ops.thy#L393), [RA1_Skip_AP](../angelic-processes/utp_ap_ops.thy#L399) |
| Paper L12–13 / thesis L.6.4.4–5 | List traces | `H1(PrefixSkip_RAD a) = PrefixSkip_AP a`; `RA1(PrefixSkip_AP a) = PrefixSkip_RAD a` | [H1_PrefixSkip_RAD](../angelic-processes/utp_ap_ops.thy#L953), [RA1_PrefixSkip_AP](../angelic-processes/utp_ap_ops.thy#L959) |

### Sequential composition and prefix

Paper T59 / thesis T.6.4.18, [AP_seq_design](../angelic-processes/utp_ap_ops.thy#L788), assumes `P`, `Q` both AP:

```text
P ;;DA Q = AP(pre ⊢ post)

pre  = ¬(F(P) ;;A true)
       ∧ ¬(RA1(T(P)) ;;A (¬s.wait ∧ RA2(F(Q))))

post = RA1(T(P)) ;;A
       (J ◁ s.wait ▷ RA2(¬F(Q) ⇒ RA1(T(Q))))
```

The first precondition excludes failure in `P`; the second excludes a terminating handover to a failing `Q`. Waiting outcomes are retained by `J`. The inner `;;A` is distinct from the outer `;;DA`.

| Source | Premises | Law | Implementation |
| --- | --- | --- | --- |
| Paper T60 / thesis T.6.4.19 | `P`, `Q` both RAD | `RA1(H1 P ;;DA H1 Q) ⊑ P ;;RAD Q` | [RA1_H1_seq_refine](../angelic-processes/utp_ap_ops.thy#L813) |
| Paper T61 / thesis T.6.4.20 | `P`, `Q` both AP | `P ;;DA Q ⊑ H1(RA1 P ;;RAD RA1 Q)` | [H1_RA1_seq_refine](../angelic-processes/utp_ap_ops.thy#L838) |
| Paper T62 / thesis T.6.4.21 | `P`, `Q` both RAD and NDRAD | `RA1(H1 P ;;DA H1 Q) = P ;;RAD Q` | [RA1_H1_seq](../angelic-processes/utp_ap_ops.thy#L900) |

Here `;;RAD` names the same underlying design operator on RAD operands. The premises establish when transport preserves the result exactly.

Thesis T.6.4.23, [Prefix_AP_design](../angelic-processes/utp_ap_ops.thy#L987), assumes `P is AP` and list traces:

```text
a →AP P = AP(¬prefix_handover a (B(F(P)))
                ⊢ prefix_continuation a (C(T(P))))
```

The helper predicates are defined in [utp_rad_seq.thy](../reactive-angelic-designs/utp_rad_seq.thy). [Prefix_Skip_AP](../angelic-processes/utp_ap_ops.thy#L980) proves `a →AP Skip_AP = PrefixSkip_AP a` without extra premises.

### Operator closure

| Operation | Exact premises | Result | Implementation |
| --- | --- | --- | --- |
| Angelic / demonic choice (thesis T.6.4.1, 5) | `P`, `Q` both AP | Result is AP. | [AP_angelic_closure](../angelic-processes/utp_ap_ops.thy#L53), [AP_demonic_closure](../angelic-processes/utp_ap_ops.thy#L111) |
| Primitive processes | None | Chaos, ChaosCSP, Choice, Stop, Skip and primitive prefix are AP. | [Chaos_AP_is_AP](../angelic-processes/utp_ap_ops.thy#L166), [ChaosCSP_AP_is_AP](../angelic-processes/utp_ap_ops.thy#L220), [Choice_AP_is_AP](../angelic-processes/utp_ap_ops.thy#L307), [Stop_AP_is_AP](../angelic-processes/utp_ap_ops.thy#L351), [Skip_AP_is_AP](../angelic-processes/utp_ap_ops.thy#L381), [PrefixSkip_AP_is_AP](../angelic-processes/utp_ap_ops.thy#L938) |
| Sequential composition | `P`, `Q` both AP | Result is AP. | [AP_seq_closure](../angelic-processes/utp_ap_ops.thy#L807) |
| Compound prefix | `P is AP`; list traces | Result is AP. | [Prefix_AP_closure](../angelic-processes/utp_ap_ops.thy#L973) |
| Angelic choice (paper T44 / thesis T.6.4.2) | `P`, `Q` both NDAP | Result is NDAP. | [NDAP_angelic_closure](../angelic-processes/utp_ap_nd.thy#L136) |
| Demonic choice (paper T47 / thesis T.6.4.6) | `P`, `Q` both NDAP | Result is NDAP. | [NDAP_demonic_closure](../angelic-processes/utp_ap_nd.thy#L144) |
| Sequential composition (paper T63 / thesis T.6.4.22) | `P`, `Q` both AP and NDAP | Result is NDAP. | [NDAP_seq_closure](../angelic-processes/utp_ap_nd.thy#L157) |

T63 does not assume associativity and does not use the standalone associativity audit. Neither closure nor the mapping laws establish unrestricted reassociation.

## Non-divergence

NDAP is conjunction with `Choice_AP`. Paper T38 / thesis T.6.2.10, [NDAP_design_form](../angelic-processes/utp_ap_nd.thy#L49), assumes `P is AP`:

```text
NDAP P = true ⊢ RA3AP(C(T(P)))
```

[NDAP_wait_cond_form](../angelic-processes/utp_ap_nd.thy#L83) expands the postcondition as `J ◁ s.wait ▷ C(T(P))`. [NDAP_AP_true_design](../angelic-processes/utp_ap_nd.thy#L94) equivalently gives `NDAP P = AP(true ⊢ T(P))` under the same AP premise. [NDAP_is_H3](../angelic-processes/utp_ap_nd.thy#L76) proves ordinary H3 healthiness of this non-divergent image.

The additional correspondence [RA1_NDAP_NDRAD](../angelic-processes/utp_ap_nd.thy#L198) has no premises:

```text
RA1(NDAP(AP P)) = NDRAD(RAD P)
```

These results link the two notions of non-divergence; NDAP healthiness alone does not supply AP healthiness where a theorem explicitly requires both.

## Worked examples

Prefix rows use list traces. The example theory is [utp_ap_examples.thy](../angelic-processes/utp_ap_examples.thy).

| Paper / thesis | Calculation / role | Implementation |
| --- | --- | --- |
| Ex22 | Expands `H1 Chaos_RAD` into the ChaosCSP contract. | [H1_Chaos_RAD_example](../angelic-processes/utp_ap_examples.thy#L13) |
| Ex23 | Expands `H1 Skip_RAD` into its waiting-conditioned contract. | [H1_Skip_RAD_example](../angelic-processes/utp_ap_examples.thy#L23) |
| Ex24 | RA1 maps the expanded ChaosCSP contract back to Chaos_RAD. | [RA1_H1_Chaos_RAD_example](../angelic-processes/utp_ap_examples.thy#L32) |
| Ex25 | `H1 ∘ RA1` maps the AP bottom to the ChaosCSP contract. | [H1_RA1_bottom_AP_example](../angelic-processes/utp_ap_examples.thy#L40) |
| Ex26 / Ex44 | `(Stop_AP ⊔AP Skip_AP) ;;DA Chaos_AP = Stop_AP`. | [Stop_Skip_seq_Chaos_AP](../angelic-processes/utp_ap_examples.thy#L51) |
| Ex27 / Ex45 | `a →AP Chaos_AP = Chaos_AP`: divergence can erase the prefix. | [Prefix_Chaos_AP](../angelic-processes/utp_ap_examples.thy#L108) |
| L14 / L.6.4.6 | `a →AP ChaosCSP_AP = AP(¬prefix_diverge_post a ⊢ prefix_offer_post a)`. | [Prefix_ChaosCSP_AP](../angelic-processes/utp_ap_examples.thy#L119) |
| Ex28 / Ex46 | `(a →AP Chaos_AP) ⊔AP (b →AP Skip_AP) = b →AP Skip_AP`. No `a ≠ b` premise. | [Prefix_Chaos_Skip_angelic_choice](../angelic-processes/utp_ap_examples.thy#L186) |

## Supporting files and research

| File | Contents |
| --- | --- |
| [utp_ap_healthy](../angelic-processes/utp_ap_healthy.thy) | AP healthiness, waiting laws, normal forms and component support. |
| [utp_ap_rad](../angelic-processes/utp_ap_rad.thy) | H1/RA1 correspondence, closure and the Galois law. |
| [utp_ap_ops](../angelic-processes/utp_ap_ops.thy) | Operators, sequential and prefix calculations, transport laws. |
| [utp_ap_nd](../angelic-processes/utp_ap_nd.thy) | NDAP, non-divergent transport and closure. |

[AP parallel](AP_PARALLEL.md) documents the research operator [ap_par](../angelic-processes/utp_ap_parallel.thy#L121):

```text
ap_par P M Q = H1(rad_par (RA1 P) M (RA1 Q))
```

[ap_par_AP](../angelic-processes/utp_ap_parallel.thy#L127) proves unconditional AP closure. [ap_par_RA1](../angelic-processes/utp_ap_parallel.thy#L132) proves its exact RAD image; [ap_par_H1](../angelic-processes/utp_ap_parallel.thy#L137) relates RAD operands transported through H1. The merge premises and further mapping laws belong in the parallel guide, not the paper coverage. [AP_feasible](../angelic-processes/utp_ap_healthy.thy#L507) is also implementation research support: it requires a successful outcome at every started, non-waiting input, and is distinct from trace-growth productivity.
