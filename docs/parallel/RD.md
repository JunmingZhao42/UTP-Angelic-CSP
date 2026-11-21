# Reactive design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md)

Source: [`utp_rdes_parallel_laws.thy`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy),
[`utp_rdes_parallel_lift.thy`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy) and
[`utp_rdes_parallel_unit_state.thy`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy).
[Shared notation](README.md#shared-notation).

We first give laws for any ordinary reactive design merge `M`, then lift a
state merge `j` to obtain `P ∥RD[j] Q`.
RD uses `R1`, `R2`, `R3c`, `RD1` and
`RD2`; the paper calls the last three R3, CSP1 and CSP2
([paper correspondence](../paper/RAD.md#63-relationship-with-csp)).
The broader stateful construction is covered in [Stateful RD](RD-stateful.md).

- [Reactive design parallel](#reactive-design-parallel)
  - [Generic merge healthiness and closure](#generic-merge-healthiness-and-closure)
    - [Generic merge algebra](#generic-merge-algebra)
  - [Lifted merge and laws](#lifted-merge-and-laws)
    - [Correspondence with upstream RD parallel](#correspondence-with-upstream-rd-parallel)

## Generic merge healthiness and closure

Each process healthiness condition has a merge counterpart. Here `tr` and
`wait` belong to the prior observation, `trL`, `trR` to the branches, and
`tr'` to the output. Substitutions are simultaneous:

```isabelle
R1m  M ≡ M ∧ tr ≤ tr'
R2m  M ≡ R1m (M[0, tr' − tr, trL − tr, trR − tr / tr, tr', trL, trR])
R3cm M ≡ (RD1m skipₘ) ◁ wait ▷ M
RD1m M ≡ M ∨ (¬ok ∧ tr ≤ tr')
RD2  M ≡ M ;; J

ORDm ≡ RD1m ∘ R3cm ∘ R2m ∘ RD2
NDRDm M ≡ M ∧ (ok ∧ ¬wait ∧ okL ∧ okR ⟶ ok')
```

[`skipₘ`](../../deps/UTP/utp_concurrency.thy#L68) preserves the prior whole
observation, so `RD1m skipₘ` is the merge form of the reactive skip
[`II_C`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L50).
Upstream [`R3m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L230) uses plain `skipₘ`
in its waiting branch; `R3cm` is its RD version, as `R3c` uses `II_C` where `R3`
uses `II`. `R2m` includes `R1m`, so `ORDm` needs no separate `R1m` component
([`ORDm_R1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L125)).

On merges, `RD2` is Design's `H2m`, with `J` at the reactive observation type,
and `RD1m` after `R2m` is `H1m` before it.
So `ORDm` is Design's `HDm` followed by the reactive conditions
([`ORDm_HDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L144)):

```isabelle
ORDm M = R3cm (R2m (HDm M))
```

All five conditions are idempotent and monotonic:
[`R1m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L40),
[`R2m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L83),
[`R3cm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L49),
[`RD1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L37) and
[`RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L393).
Their definitions are inherited from Isabelle/UTP except for `R3cm`.
[`NDRDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L413)
is also idempotent and monotone, with fixed points characterised by
[`NDRDm_healthy_iff`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L429).

The five core conditions `R1m`, `R2m`, `R3cm`, `RD1m` and `RD2` commute
pairwise without premises. In particular, the four components of `ORDm` can be
applied in any order:

| Commuting pair | Premises | Lemma |
| --- | --- | --- |
| `R2m`, `R3cm` | - | [`R2m_R3cm_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L63) |
| `R2m`, `RD1m` | - | [`RD1m_R2m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L60) |
| `R2m`, `RD2` | - | [`RD2_R2m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L72) |
| `R3cm`, `RD1m` | - | [`RD1m_R3cm_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L57) |
| `R3cm`, `RD2` | - | [`RD2_R3cm_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L69) |
| `RD1m`, `RD2` | - | [`RD2_RD1m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L66) |

[`R1m_R2m_commute`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L160)
covers `R1m` with `R2m`; the other three `R1m` pairs were checked in Isabelle
but are not installed as named lemmas.
The additional `NDRDm` commutes with `R1m`, `R2m`, `R3cm` and `RD1m`
([`NDRDm_R1m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L458) and the three lemmas after it), but
**not with `RD2` or `ORDm` in general**; these negative results are not
installed as Isabelle lemmas.

| Law for `P ∥[M] Q` | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| `is R1` | - | [`R1m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L13) | [`R1_par_by_merge`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L191) |
| `is R2` | Both `R2` | [`R2m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L23) | [`R2_par_by_merge`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L202) |
| `is R3c` (R3) | Both `R3c` | [`R3cm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L24) | [`R3c_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L481) |
| `is RD1` (CSP1) | Both `R1`, `RD1` | [`R1m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L13), [`RD1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L77) | [`RD1_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L79) |
| `is RD2` (CSP2) | - | [`RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L373) | [`RD2_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L96) |
| `is RD` | Both `RD` | `ORDm` | [`RD_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L502) |

[`RD`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L425) combines the five
process conditions above. These merge premises are sufficient for closure;
the laws do not assert their necessity.

### Generic merge algebra

Associativity of a merge is the cyclic equation given by
[`AssocMerge_iff`](../../deps/UTP/utp_concurrency_assoc.thy#L15); symmetry turns
it into ordinary parallel associativity.

| Merge property | Premises on `M` | Lemma |
| --- | --- | --- |
| `ORDm M is SymMerge` | `SymMerge` | [`ORDm_SymMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L294) |
| `AssocMerge (R2m M)` | `AssocMerge M` | [`AssocMerge_R2m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L342) |
| `AssocMerge (R3cm M)` | `AssocMerge M` | [`AssocMerge_R3cm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L327) |
| `AssocMerge (RD1m M)` | `R1m`, `AssocMerge M` | [`AssocMerge_RD1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L309) |
| `AssocMerge (RD2 M)` | `AssocMerge M`, `J(u,v) ∧ M(x,v,r,z) ⟹ ∃w. M(x,u,r,w) ∧ J(w,z)` | [`AssocMerge_RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L370) |
| `AssocMerge (ORDm M)` | `AssocMerge (RD2 M)` | [`ORDm_AssocMerge_RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L395) |

In the `RD2` row, `J(u,v)` says `v` is `u` with `ok` possibly raised from false
to true. So lowering the left branch's `ok` may only lower the output's `ok`.

Symmetry and associativity:

| Law | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| `P ∥[ORDm M] Q = Q ∥[ORDm M] P` | - | `M is SymMerge` | [`ORDm_parallel_comm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L520) |
| `(P ∥[M] Q) ∥[M] R =`<br>`P ∥[M] (Q ∥[M] R)` | All `RD`, `NDRD` | `M is SymMerge`, `M is NDRDm`, `AssocMerge (merge_guard G_RD M)` | [`par_by_merge_assoc_NDRD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L533) |

`G_RD` is the guard from [Generic](Generic.md#associativity-on-nondivergent-operands):
a started, non-waiting prior gives a terminating result.

With [`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30), the merge
rules above make `∥[ORDm M]` associative for any operands when `M is SymMerge`
and `AssocMerge (RD2 M)`. The lifted `∥RD[j]` needs `NDRD` operands only because
of its `RD3c` completion; see [below](#lifted-merge-and-laws).

## Lifted merge and laws

[`merge_rdes_raw`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L22)
applies `j :: ('t::trace × 'a) merge` to traces and extension observations,
such as refusals. It sets `ok' = okL ∧ okR` and `wait' = waitL ∨ waitR`.
We apply `ORDm`, then complete with
[`RD3c`](../../deps/UTP-Reactive-Designs/utp_rdes_normal.thy#L13), `P ;; II_C`:

```isabelle
merge_rdes ≡ RD3c ∘ ORDm ∘ merge_rdes_raw

P ∥RD[j] Q ≡ P ∥[merge_rdes j] Q
```

This parallels Design's completion with `H3m`.
`RD3c` commutes with `ORDm`
([`ORDm_RD3c_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L240)),
so completion preserves `ORDm`
([`RD3c_ORDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L246)).
[`rdes_lift_par`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L170)
provides the `∥RD[j]` notation.

[`merge_rdes_eval`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L74)
exposes four cases. Prior divergence permits trace growth; a started, waiting
prior is preserved. At an active prior, `j` sees trace contributions relative
to the common history. If both branches terminate, `j` constrains the output
trace and extension, `ok'` holds and `wait' = waitL ∨ waitR`. If a branch
diverges, `j` must admit a trace no longer than the output trace; the output
flags and extension are unconstrained.

The lifted merge inherits these properties:

| Property of `merge_rdes j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `ORDm` | - | [`merge_rdes_ORDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L124) |
| `R1m`, `R2m`, `R3cm`, `RD1m`, `RD2` | - | [`merge_rdes_healths`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L127) |
| `NDRDm` | - | [`merge_rdes_NDRDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L243) |
| `SymMerge` | `SymMerge` | [`merge_rdes_SymMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L159) |
| `merge_rdes j ⊑ merge_rdes k` | `j ⊑ k` | [`merge_rdes_mono`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L137) |

So `∥RD[j]` preserves reactive design healthiness:

| Result of `P ∥RD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `RD` | Both `RD` | [`rdes_lift_parallel_RD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L177) |
| `NDRD` | Both `RD`, `NDRD` | [`rdes_lift_parallel_NDRD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L185) |

Its algebraic laws:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `P ∥RD[j] Q = Q ∥RD[j] P` | - | `SymMerge` | [`rdes_lift_parallel_comm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L205) |
| `(P ∥RD[j] Q) ∥RD[j] R =`<br>`P ∥RD[j] (Q ∥RD[j] R)` | All `RD`, `NDRD` | `SymMerge`, `AssocMerge` | [`rdes_lift_parallel_assoc_nd`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L267) |

Completion can extend a divergent intermediate trace, so `merge_rdes j` is
not associative in general. The uncompleted merge is associative when
`AssocMerge j`
([`ORDm_merge_rdes_raw_AssocMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L215));
the completed merge retains this property under `G_RD`
([`merge_rdes_guard_AssocMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L252)).
For RD operands, [`NDRD_healthy_iff`](../../deps/UTP-Reactive-Designs/utp_rdes_triples.thy#L745)
equates `NDRD` with `pre_R P = true_r`: these operands never diverge from an
active prior. Associativity for a wider class, such as prefix-closed operands,
remains open.

### Correspondence with upstream RD parallel

Ordinary RD parallel agrees with upstream parallel at `st = ()`, preserving
all other observations, including refusals. Write `U` for
[`unit_state_relation`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L137)
and `M = unit_state_rd_merge j`, using
[`unit_state_rd_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L13).

| Law | Premises | Lemma |
| --- | --- | --- |
| `M is RDM` | - | [`unit_state_rd_merge_RDM`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L47) |
| Completed merges agree under [`to_unit_state`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L57) | - | [`merge_rdes_unit_state`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L119) |
| `U (P ∥RD[j] Q) =`<br>`U P ∥R[M] U Q` | - | [`rdes_lift_parallel_unit_state_eq`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L154) |

See [Stateful RD](RD-stateful.md) for broader completion premises and
[RAD](RAD.md) for choice-set lifting and RD/RAD mapping laws.
