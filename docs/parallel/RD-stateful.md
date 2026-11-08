# Stateful reactive design parallel

[Parallel by merge](README.md) · [Ordinary RD](RD.md) · [D](D.md) · [AD](AD.md)

The [isabelle-utp core](https://github.com/isabelle-utp/UTP-Reactive-Designs/blob/main/utp_rdes_parallel.thy)
is retained unchanged. The local development follows it with
[stateful merge healthiness, closure and laws](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy),
and the [unit-state bridge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy),
which defines a unit-state input merge for the upstream operator. These theories
use the stateful reactive-design alphabet and its SRD/NSRD healthiness.

## Generic merge healthiness and closure

[SRDM](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L26)
packages sufficient conditions on the actual merge used in `P ∥[M] Q`:

```text
SRDM ≡ RD1m ∘ RD2 ∘ R3hm ∘ R2m
```

[SRDM_fixed_iff](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L80)
equates `M is SRDM` with the five upstream conditions `R1m`, `R2m`, `R3hm`,
`RD1m` and `RD2`. These express output trace growth, independence from the
common history, prior waiting, prior divergence and output termination
healthiness. `R2m` already implies `R1m`, so
[SRDM_intro](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L99)
requires only the other four conditions;
[SRDM_healths](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L94)
recovers all five. This is a package of sufficient conditions for closure,
not a claim that every merge preserving SRD must satisfy them.

| Property of SRDM | Result |
| --- | --- |
| Idempotent and monotone | [SRDM_Idempotent](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L108), [SRDM_Monotonic](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L114) |
| Distributes over disjunction | [SRDM_disj](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L125) |
| Healthy merges closed under disjunction and conjunction | [SRDM_disj_closed](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L128), [SRDM_conj_closed](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L133) |
| Preserves merge symmetry | [SymMerge_SRDM](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L147) |

| Parallel result | Operand premises | Merge premises | Closure lemma | File |
| --- | --- | --- | --- | --- |
| `P ∥[M] Q is R1` | None | `M is R1m` | [R1_par_by_merge](../../deps/UTP-Reactive/utp_rea_parallel.thy#L191) | [utp_rea_parallel.thy](../../deps/UTP-Reactive/utp_rea_parallel.thy) |
| `P ∥[M] Q is R2` | Both R2 | `M is R2m` | [R2_par_by_merge](../../deps/UTP-Reactive/utp_rea_parallel.thy#L202) | [utp_rea_parallel.thy](../../deps/UTP-Reactive/utp_rea_parallel.thy) |
| `P ∥[M] Q is R3h` | Both R3h | `M is R3hm` | [R3h_par_by_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L37) | [utp_rdes_parallel.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy) |
| `P ∥[M] Q is RD1` | Both R1 and RD1 | `M is R1m` and `M is RD1m` | [RD1_par_by_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L79) | [utp_rdes_parallel.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy) |
| `P ∥[M] Q is RD2` | None | `M is RD2` | [RD2_par_by_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L96) | [utp_rdes_parallel.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy) |
| `P ∥[M] Q is SRD` | Both SRD | R1m, R2m, R3hm, RD1m and RD2 | [SRD_par_by_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L112) | [utp_rdes_parallel.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy) |
| `P ∥[M] Q is SRD` | Both SRD | `M is SRDM` | [SRDM_par_by_merge](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L249) | [utp_srdes_parallel_laws.thy](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy) |
| `P ∥[M] Q is RD3` | None | `M is RD3` | [RD3_par_by_merge](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L243) | [utp_srdes_parallel_laws.thy](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy) |
| `P ∥[M] Q is NSRD` | Both SRD | `M is SRDM` and `M is RD3` | [NSRD_par_by_merge](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L254) | [utp_srdes_parallel_laws.thy](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy) |

These rules use `M` directly and permit dependence on control flags.
`RD3(M) = M ;; II_R` supplies right-completion when normality is required.

## Upstream RD merge construction

[RDM](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L140) characterises
the input merge: trace growth, independence from the common history, and
independence from all prior, branch and output `ok`/`wait` flags.
[RDM_intro](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L178) supplies
the introduction rule; [RDM_unrests](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L185)
and [RDM_R2m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L194)
recover its components.

Upstream's [nmerge_rd](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L126)
adds control behaviour. Its [merge_rd](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L132)
then appends reactive skip:

```text
M_R(M) ≡ N_R(M) ;; II_R
P ∥R[M] Q ≡ P ∥[M_R(M)] Q
```

| Merge expression | Property | Premise | Result |
| --- | --- | --- | --- |
| `N_R(M)` | R1m | None | [nmerge_rd_is_R1m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L142) |
| `N_R(M)` | R2m | `M is R2m` | [nmerge_rd_is_R2m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L150) |
| `N_R(M)` | R3hm | None | [nmerge_rd_is_R3hm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L154) |
| `N_R(M)` | RD1m | None | [nmerge_rd_is_RD1m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L157) |
| `M_R(M)` | RD3, hence RD2 | None | [merge_rd_is_RD3](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L160), [merge_rd_is_RD2](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L163) |
| `M_R(M)` | SRDM | `M is RDM` | [merge_rd_is_SRDM](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L287) |

| Parallel result | Operand premises | Merge premises | Result |
| --- | --- | --- | --- |
| `P ∥R[M] Q is SRD` | Both SRD | `M is RDM` | [rdes_parallel_SRD](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L313) |
| `P ∥R[M] Q is NSRD` | Both SRD | `M is RDM` | [rdes_parallel_NSRD](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L318), recovering upstream [par_rdes_NSRD](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L166) |

The completion bridge uses [R2m_RD3_closed](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L154)
and commutation of RD3 with [RD1m](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L56)
and [R3hm](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L60).
The constructed closure laws then follow from the generic SRDM rules above.

RDM constrains the flag-independent input to this construction; SRDM constrains
the actual merge in generic parallel. The completed merge adds flag-dependent behaviour.
[merge_rd_eval](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L344)
exposes termination, waiting and divergence. Waiting hides the output program
state; divergence retains an existential merge witness whose trace the final
trace extends.

## Lifted merge

[unit_state_rd_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L13)
takes `j :: ('t::trace × 'a) merge` and produces a merge on the upstream RD
alphabet with program state fixed to `()`. It excludes `ok` and `wait`, uses
trace contributions relative to the prior history, and requires output trace
growth. The evaluation is
[unit_state_rd_merge_eval](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L23), and
[unit_state_rd_merge_RDM](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L47) shows the input is RDM, so
[merge_rd_eval](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L344)
and the constructed closure laws above apply to `M_R(unit_state_rd_merge j)`.

The [unit-state correspondence](RD.md#correspondence-with-upstream-rd-parallel)
identifies this completed merge with ordinary `∥RD[j]`, preserving the
extension observation.

## Conditional algebra and deferred work

[rdes_parallel_Chaos_iff](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L495)
characterises Chaos for SRD operands and an RDM input merge: every active prior
observation must admit a divergent branch pair with a merge witness at the
prior trace. There is no unconditional Chaos zero law for arbitrary `j`.

The proof uses the following rules without an operand healthiness premise.
The divergence rules require an active prior observation.

| Fact | Lemma |
| --- | --- |
| Characterise a divergent output (`¬ok'`) by a feasible divergent branch pair | [rdes_parallel_divergent_eval](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L467) |
| A feasible divergent pair admits any output extending its merged trace | [rdes_parallel_divergentI](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L479) |
| An RDM merge witness cannot precede the prior trace | [RDM_trace_growth](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L271) |

Associativity of the completed stateful operator is outside the current scope.

The [plan](../../PLAN.md#stage-2--drd-law-parity--pending) tracks remaining RD
laws. [RAD parallel](RAD.md) uses ordinary RD directly; this stateful
comparison is separate from its construction.
