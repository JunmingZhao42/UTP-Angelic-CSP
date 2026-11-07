# Reactive design parallel

[Parallel by merge](README.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md)

This guide covers ordinary reactive designs with the paper's process healthiness
conditions: R1, R2, R3c, RD1 and RD2. The paper calls the last two CSP1 and CSP2;
its R3 corresponds to Isabelle's R3c. See the [paper correspondence](../paper/RAD.md#63-relationship-with-csp).

The operator is generic parallel by merge, `P ∥[M] Q`, on complete reactive
observations. Its merge is supplied directly. The broader stateful construction,
lifting and associativity results are documented in [Stateful RD parallel](RD-stateful.md).

## Generic merge healthiness and closure

| Process healthiness (Isabelle) | Paper notation | Meaning | Merge condition |
| --- | --- | --- | --- |
| R1 | R1 | Output trace extends the prior trace | [R1m](../../deps/UTP-Reactive/utp_rea_parallel.thy#L13) |
| R2 | R2 | Independence from the common trace history | [R2m](../../deps/UTP-Reactive/utp_rea_parallel.thy#L23) |
| R3c | R3 | Reactive skip when the prior process is waiting | [R3cm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L24) |
| RD1 | CSP1 | Prior divergence guarantees only trace growth | [RD1m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L77) |
| RD2 | CSP2 | Cannot require nontermination | [RD2](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L373), applied to the merge |

The ordinary waiting condition R3cm and the combined ORDm interface reside in
`utp_rdes_parallel_laws.thy`; the RAD parallel theory imports them.
Shared merge laws also live there. Stateful merge healthiness and completed-operator
laws are kept in [utp_srdes_parallel_laws.thy](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy).

| Parallel result | Operand premises | Merge premises | Closure lemma | File |
| --- | --- | --- | --- | --- |
| `P ∥[M] Q is R1` | None | `M is R1m` | [R1_par_by_merge](../../deps/UTP-Reactive/utp_rea_parallel.thy#L191) | [utp_rea_parallel.thy](../../deps/UTP-Reactive/utp_rea_parallel.thy) |
| `P ∥[M] Q is R2` | Both R2 | `M is R2m` | [R2_par_by_merge](../../deps/UTP-Reactive/utp_rea_parallel.thy#L202) | [utp_rea_parallel.thy](../../deps/UTP-Reactive/utp_rea_parallel.thy) |
| `P ∥[M] Q is R3c` | Both R3c | `M is R3cm` | [R3cm_par_by_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L378) | [utp_rdes_parallel_laws.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy) |
| `P ∥[M] Q is RD1` | Both R1 and RD1 | `M is R1m` and `M is RD1m` | [RD1_par_by_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L79) | [utp_rdes_parallel.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy) |
| `P ∥[M] Q is RD2` | None | `M is RD2` | [RD2_par_by_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L96) | [utp_rdes_parallel.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy) |

R2m already supplies output trace growth, so the combined interface needs four
merge conditions. Their combined transformer is [ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L27):

```text
ORDm ≡ RD1m ∘ R3cm ∘ R2m ∘ RD2
```

[ORDm_healthy_iff](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L113) equates its fixed points with R2m, R3cm,
RD1m and RD2. [ORDm_R1m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L126) recovers R1m.
The package is [idempotent](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L98) and [monotone](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L101).

| Parallel result | Operand premises | Merge premises | Closure lemma | File |
| --- | --- | --- | --- | --- |
| `P ∥[M] Q is RD` | Both RD | `M is ORDm` | [RD_par_by_ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L399) | [utp_rdes_parallel_laws.thy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy) |

Here [RD](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L425) combines the five process conditions above.
ORDm supplies sufficient merge conditions for closure; the theorem does not
assert their necessity.

## Generic merge symmetry

[ORDm_SymMerge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L275)
preserves merge symmetry. [ORDm_parallel_comm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L417)
gives `P ∥[ORDm M] Q = Q ∥[ORDm M] P` when `M is SymMerge`,
with no operand-healthiness premises.

## Generic merge associativity

[AssocMerge](../../deps/UTP/utp_concurrency.thy#L215) expresses cyclic equality
of two merge applications; [AssocMerge_cyclic_eval](../../deps/UTP/utp_concurrency.thy#L377)
gives its pointwise form. Symmetry turns this into ordinary parallel
associativity.

| Result | Merge premises | Lemma |
| --- | --- | --- |
| `AssocMerge (R2m M)` | `AssocMerge M` | [AssocMerge_R2m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L324) |
| `AssocMerge (R3cm M)` | `AssocMerge M` | [AssocMerge_R3cm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L309) |
| `AssocMerge (RD1m M)` | `M is R1m`, `AssocMerge M` | [AssocMerge_RD1m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L291) |
| `AssocMerge (ORDm M)` | `AssocMerge (RD2 M)` | [ORDm_AssocMerge_RD2](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L351) |
| `AssocMerge (ORDm M)` | `M is RD2`, `AssocMerge M` | [ORDm_AssocMerge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L362) |
| Parallel with `ORDm M` is associative | `M is RD2`, `M is SymMerge`, `AssocMerge M` | [ORDm_parallel_assoc](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L424) |

R2m supplies the trace-growth premise needed by RD1m in the composite.
The combined rule requires associativity after RD2; an already RD2-healthy
input therefore needs only `AssocMerge M`. These are sufficient conditions.
The parallel law holds for arbitrary relational operands.

## Lifted merge and laws

The local [merge_rdes_raw](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L22)
takes `j :: ('t::trace × 'a) merge`, where `'a` contains extension observations
such as refusals. It applies j to traces and extensions, sets output `ok` to
the conjunction of branch flags, and sets output `wait` to their disjunction.
[merge_rdes](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L34)
then applies ORDm and completes with upstream's
[RD3c](../../deps/UTP-Reactive-Designs/utp_rdes_normal.thy#L13), `P ;; II_C`, as
H3m completes the design merge with design skip:

```text
merge_rdes j ≡ RD3c (ORDm (merge_rdes_raw j))
merge_des j  ≡ H3m (HDm (merge_des_raw j))
```

RD3c commutes with ORDm ([ORDm_RD3c_commute](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L221)), so completing
an ORDm-healthy merge keeps it ORDm-healthy ([RD3c_ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L227)).

[merge_rdes_eval](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L74)
exposes four cases. Prior divergence permits trace growth; a waiting prior is
preserved. At an active prior, j sees trace contributions relative to the
common history. If both branches are ok, j constrains the output trace and
extension, `ok'` holds and `wait'` is the disjunction of branch flags. If a
branch diverges, j must admit some trace no longer than the output trace; the
output flags and extension are unconstrained. As in upstream `M_R`, divergent
outputs are closed under trace extension.

[rdes_lift_par](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L170)
abbreviates `P ∥[merge_rdes j] Q` as `P ∥RD[j] Q`.

| Property or law | Premises | Result |
| --- | --- | --- |
| Lifted merge is ORDm-healthy | None | [merge_rdes_ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L124) |
| Component merge healthiness | None | [merge_rdes_healths](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L127) |
| Monotonicity in j | `j ⊑ k` | [merge_rdes_mono](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L137) |
| Merge symmetry | `j is SymMerge` | [merge_rdes_SymMerge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L159) |
| `P ∥RD[j] Q is RD` | Both operands RD | [rdes_lift_parallel_RD](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L177) |
| Parallel commutativity | `j is SymMerge` | [rdes_lift_parallel_comm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L185) |
| Parallel associativity | `j is SymMerge`, `AssocMerge j`; all operands RD and NDRD | [rdes_lift_parallel_assoc_nondiv](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L201) |

### Correspondence with upstream RD parallel

[to_unit_state](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L57)
adds `st = ()` while preserving `ok`, `wait`, trace and the extension observation.
[unit_state_rd_merge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L13)
applies the same `j` to trace contributions and extension observations on
the stateful alphabet with `st = ()`. It is RDM by
[unit_state_rd_merge_RDM](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L47).
The completed merges agree pointwise by
[merge_rdes_unit_state](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L119).
Consequently,
[rdes_lift_parallel_unit_state_eq](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L154)
identifies `P ∥RD[j] Q` with upstream
`P ∥R[unit_state_rd_merge j] Q` after transporting the operands and result
through the unit-state alphabet map. It has no premises on `P`, `Q` or `j`.
The extension observation remains available, including for refusals; only
the separate program state is fixed to `()`.

The completed merge is not associative in general. Completion lets a diverged
intermediate result extend its trace, so it may then synchronise with traces
that its branches did not perform. For RD operands,
[NDRD_healthy_iff](../../deps/UTP-Reactive-Designs/utp_rdes_triples.thy#L745)
equates `P is NDRD` with `pre_R P = true_r`. Such operands never diverge
from an active prior, so completion has no effect on them and associativity
follows from the uncompleted merge; the proof of
[rdes_lift_parallel_assoc_nondiv](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L201)
shows both steps locally. Associativity for a
wider class, such as prefix-closed operands, is open.

Except for associativity, the algebraic laws hold for arbitrary relational
operands. The specialised RAD correspondence remains deferred. The upstream
completion premises and the unit-state instance are recorded in [Stateful RD](RD-stateful.md).
