# Reactive design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md)

Source files:

- [`utp_rdes_parallel_laws.thy`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy)
- [`utp_rdes_parallel_lift.thy`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy)
- [`utp_rdes_parallel_unit_state.thy`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy)

[Shared notation](README.md#shared-notation).

We lift a state merge `j` to obtain `P ∥RD[j] Q`, and give each law for any
ordinary reactive design merge `M`, with its instance for `∥RD[j]`.

- RD uses `R1`, `R2`, `R3c`, `RD1` and `RD2`; the paper calls the last three R3,
  CSP1 and CSP2 ([paper correspondence](../paper/RAD.md#63-relationship-with-csp)).
- The broader stateful construction is covered in [Stateful RD](RD-stateful.md).

Contents:

- [Merge conditions](#merge-conditions)
- [The lifted merge](#the-lifted-merge)
- [Closure](#closure)
- [Symmetry and associativity](#symmetry-and-associativity)
- [Zero laws](#zero-laws)
- [Correspondence with upstream RD parallel](#correspondence-with-upstream-rd-parallel)

## Merge conditions

Each process healthiness condition has a merge counterpart. Here `tr` and `wait`
belong to the prior observation, `trL`, `trR` to the branches, and `tr'` to the
output. Substitutions are simultaneous:

```isabelle
R1m  M ≡ M ∧ tr ≤ tr'
R2m  M ≡ R1m (M[0, tr' − tr, trL − tr, trR − tr / tr, tr', trL, trR])
R3cm M ≡ (RD1m skipₘ) ◁ wait ▷ M
RD1m M ≡ M ∨ (¬ok ∧ tr ≤ tr')
RD2  M ≡ M ;; J

ORDm ≡ RD1m ∘ R3cm ∘ R2m ∘ RD2
NDRDm M ≡ M ∧ (ok ∧ ¬wait ∧ okL ∧ okR ⟶ ok')
```

- [`skipₘ`](../../deps/UTP/utp_concurrency.thy#L105) preserves the prior whole observation, so `RD1m skipₘ` is the merge
  form of the reactive skip [`II_C`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L50).
- Upstream [`R3m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L230) uses plain `skipₘ` in the waiting branch; `R3cm` is the RD
  version, as `R3c` uses `II_C` where `R3` uses `II`.
- `R2m` includes `R1m`, so `ORDm` needs no separate `R1m` component
  ([`ORDm_R1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L125)).
- On merges, `RD2` is Design's `H2m`, with `J` at the reactive observation type,
  and `RD1m` after `R2m` is `H1m` before `R2m`. So `ORDm` is Design's `HDm` followed
  by the reactive conditions ([`ORDm_HDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L144)):

```isabelle
ORDm M = R3cm (R2m (HDm M))
```

All five conditions are idempotent and monotone:
[`R1m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L40),
[`R2m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L83),
[`R3cm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L49),
[`RD1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L37) and
[`RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L393).

- Their definitions are inherited from Isabelle/UTP except for `R3cm`.
- [`NDRDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L413) is also idempotent and monotone, with fixed points characterised by
  [`NDRDm_healthy_iff`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L429).

The five core conditions `R1m`, `R2m`, `R3cm`, `RD1m` and `RD2` commute pairwise
without premises. In particular, the four components of `ORDm` can be applied in
any order:

| Commuting pair | Premises | Lemma |
| --- | --- | --- |
| `R2m`, `R3cm` | - | [`R2m_R3cm_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L63) |
| `R2m`, `RD1m` | - | [`RD1m_R2m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L60) |
| `R2m`, `RD2` | - | [`RD2_R2m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L72) |
| `R3cm`, `RD1m` | - | [`RD1m_R3cm_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L57) |
| `R3cm`, `RD2` | - | [`RD2_R3cm_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L69) |
| `RD1m`, `RD2` | - | [`RD2_RD1m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L66) |

- [`R1m_R2m_commute`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L160) covers `R1m` with `R2m`; the other three `R1m` pairs were
  checked in Isabelle but are not installed as named lemmas.
- `NDRDm` commutes with `R1m`, `R2m`, `R3cm` and `RD1m` ([`NDRDm_R1m_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L458)
  and the three lemmas that follow), but **not with `RD2` or `ORDm` in general**;
  these negative results are not installed as Isabelle lemmas.

## The lifted merge

[`merge_rdes_raw`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L22) applies `j :: ('t::trace × 'a) merge` to traces and extension
observations, such as refusals. The raw merge sets `ok' = okL ∧ okR` and
`wait' = waitL ∨ waitR`. We apply `ORDm`, then complete with [`RD3c`](../../deps/UTP-Reactive-Designs/utp_rdes_normal.thy#L13),
`P ;; II_C`:

```isabelle
merge_rdes ≡ RD3c ∘ ORDm ∘ merge_rdes_raw

P ∥RD[j] Q ≡ P ∥[merge_rdes j] Q
```

- The completion parallels Design's completion with `H3m`.
- `RD3c` commutes with `ORDm` ([`ORDm_RD3c_commute`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L240)), so completion preserves
  `ORDm` ([`RD3c_ORDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L246)).
- [`rdes_lift_par`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L170) provides the `∥RD[j]` notation.

[`merge_rdes_eval`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L74) exposes four cases:

- prior divergence permits trace growth;
- a started, waiting prior is preserved;
- at an active prior with both branches terminating, `j` constrains the output
  trace and extension, `ok'` holds and `wait' = waitL ∨ waitR`;
- at an active prior with a diverging branch, `j` must admit a trace no longer
  than the output trace; the output flags and extension are unconstrained.

At an active prior, `j` sees trace contributions relative to the common history.

`merge_rdes` is monotone in `j`: `j ⊑ k` gives `merge_rdes j ⊑ merge_rdes k`
([`merge_rdes_mono`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L137)).

## Closure

Each closure rule holds for any `M` that satisfies its merge premises. For every
`j`, `merge_rdes j` satisfies each merge premise, which gives the closure law for
`∥RD[j]`:

| `P ∥[M] Q` is | Operand premises | Merge premises | Lemma | `merge_rdes j` | `P ∥RD[j] Q` |
| --- | --- | --- | --- | --- | --- |
| `R1` | - | [`R1m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L13) | [`R1_par_by_merge`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L191) | [`merge_rdes_healths`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L127) | - |
| `R2` | Both `R2` | [`R2m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L23) | [`R2_par_by_merge`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L202) | [`merge_rdes_healths`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L127) | - |
| `R3c` (R3) | Both `R3c` | [`R3cm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L24) | [`R3c_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L481) | [`merge_rdes_healths`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L127) | - |
| `RD1` (CSP1) | Both `R1`, `RD1` | [`R1m`](../../deps/UTP-Reactive/utp_rea_parallel.thy#L13), [`RD1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L77) | [`RD1_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L76) | [`merge_rdes_healths`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L127) | - |
| `RD2` (CSP2) | - | [`RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L373) | [`RD2_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L93) | [`merge_rdes_healths`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L127) | - |
| `RD` | Both `RD` | `ORDm` | [`RD_par_by_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L502) | [`merge_rdes_ORDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L124) | [`rdes_lift_parallel_RD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L177) |

[`RD`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L425) combines the five process conditions above. These merge premises are
sufficient for closure; the laws do not assert their necessity.

For `∥RD[j]`, parallel also preserves nondivergence:

| Result of `P ∥RD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `NDRD` | Both `RD`, `NDRD` | [`rdes_lift_parallel_NDRD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L185) |

## Symmetry and associativity

Associativity of a merge is the cyclic equation given by [`AssocMerge_iff`](../../deps/UTP/utp_concurrency_assoc.thy#L15);
symmetry turns the cyclic equation into ordinary parallel associativity.

`ORDm M` is symmetric when `M` is ([`ORDm_SymMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L294)). The components preserve
merge associativity:

| Merge property | Premises on `M` | Lemma |
| --- | --- | --- |
| `AssocMerge (R2m M)` | `AssocMerge M` | [`AssocMerge_R2m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L342) |
| `AssocMerge (R3cm M)` | `AssocMerge M` | [`AssocMerge_R3cm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L327) |
| `AssocMerge (RD1m M)` | `R1m`, `AssocMerge M` | [`AssocMerge_RD1m`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L309) |
| `AssocMerge (RD2 M)` | `AssocMerge M`, `J(u,v) ∧ M(x,v,r,z) ⟹ ∃w. M(x,u,r,w) ∧ J(w,z)` | [`AssocMerge_RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L370) |
| `AssocMerge (ORDm M)` | `AssocMerge (RD2 M)` | [`ORDm_AssocMerge_RD2`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L395) |

In the `RD2` row, `J(u,v)` says `v` is `u` with `ok` possibly raised from false to
true. So lowering the left branch's `ok` may only lower the output's `ok`.

With premises on `j`, the lifted merge has these properties:

| Property of `merge_rdes j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `SymMerge` | `SymMerge` | [`merge_rdes_SymMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L159) |
| `NDRDm` | - | [`merge_rdes_NDRDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L293) |
| `AssocMerge` on nondivergent branches | `AssocMerge` | [`merge_rdes_guard_AssocMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L302) |

Each law holds for any `M` with the merge premises, and for `∥RD[j]` with the
premises on `j`:

| Law for `P ∥[M] Q` | Operand premises | Merge premises | Lemma | Premises on `j` | `P ∥RD[j] Q` |
| --- | --- | --- | --- | --- | --- |
| `P ∥[M] Q = Q ∥[M] P` | - | `M is SymMerge` | [`par_by_merge_comm`](../../deps/UTP/utp_concurrency.thy#L414) | `SymMerge` | [`rdes_lift_parallel_comm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L205) |
| `(P ∥[M] Q) ∥[M] R =`<br>`P ∥[M] (Q ∥[M] R)` | All `RD`, `NDRD` | `M is SymMerge`, `M is NDRDm`, `AssocMerge (merge_guard G_RD M)` | [`par_by_merge_assoc_NDRD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L526) | `SymMerge`, `AssocMerge` | [`rdes_lift_parallel_assoc_nd`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L317) |

- The `NDRD` associativity row instantiates
  [`par_by_merge_assoc_guard`](Generic.md#associativity-on-nondivergent-operands)
  with the nondivergence guard `λx z. ok x ∧ ¬wait x ⟶ ok z`, written inline in
  the lemma; this guide calls the guard `G_RD`. A started, non-waiting prior gives
  a terminating result.
- With [`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30), the merge rules above make `∥[ORDm M]`
  associative for any operands when `M is SymMerge` and `AssocMerge (RD2 M)`.
- The lifted `∥RD[j]` needs `NDRD` operands only because of the `RD3c`
  completion, as below.

For normal operands, `∥RD[j]` is associative when `j` absorbs extensions:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `(P ∥RD[j] Q) ∥RD[j] R =`<br>`P ∥RD[j] (Q ∥RD[j] R)` | All `NRD` | `SymMerge`, `AssocMerge`, absorbing | [`rdes_lift_parallel_assoc_nrd`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L334) |

Completion can extend a divergent intermediate trace, so `merge_rdes j` is not
associative in general.

- **Nondivergent operands.** The uncompleted merge is associative when
  `AssocMerge j` ([`ORDm_merge_rdes_raw_AssocMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L265)); the completed merge
  retains this property under `G_RD`, as in the table above. For RD
  operands, [`NDRD_healthy_iff`](../../deps/UTP-Reactive-Designs/utp_rdes_triples.thy#L745) equates `NDRD` with `pre_R P = true_r`: these
  operands never diverge from an active prior.
- **Normal operands.** [`rdes_lift_parallel_assoc_nrd`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L334) allows divergence for
  normal operands ([`NRD`](../../deps/UTP-Reactive-Designs/utp_rdes_normal.thy#L157)), which allow every extension after a divergence.
  Completion lets a divergent intermediate result end with any extension `u` of
  the merged trace of that intermediate result; the other bracketing produces `u`
  only if a divergent input can reach `u`.

So `j` must absorb extensions. Writing `p ⊗ q` for the results `j` merges from
inputs `p` and `q`, and `↑A` for their trace extensions with any state:

```isabelle
↑(p ⊗ q) ⊆ ↑p ⊗ q
```

- Interleaving with a unit state satisfies the premise.
- Determinism and totality are not enough: with exclusive or on time traces, `P`
  diverging at time 1 and `Q`, `R` terminating at time 1, `(P ∥ Q) ∥ R` can
  terminate at time 0 but `P ∥ (Q ∥ R)` cannot.
- A synchronising merge fails as well: if `Q` terminates at `⟨⟩` and `R` diverges
  after `⟨a⟩`, then `Q ∥ R` has no observation while `(P ∥ Q) ∥ R` has one.

## Zero laws

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `P ∥RD[j] ⊤RD =`<br>`⊤RD ∥RD[j] P = ⊤RD` | `P is RD` | - | [`rdes_lift_parallel_miracle`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L218) |
| `P ∥RD[j] ⊥RD =`<br>`⊥RD ∥RD[j] P = ⊥RD` | `P is RD`, `(P ∧ tr' = tr) is H4` | merges empty traces | [`rdes_lift_parallel_chaos`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L228) |

Here Miracle and Chaos are the top and bottom of RD, [`top_RD`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L659) `⊤RD = RD false`
and [`bottom_RD`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L656) `⊥RD = RD true`; the upstream `Miracle` and `Chaos` are their
SRD versions. Their forms:

| Fact | Premises | Lemma |
| --- | --- | --- |
| `⊥RD = R(false ⊢ true)` | - | [`bottom_RD_design`](../../deps/UTP-Reactive-Designs/utp_rdes_designs.thy#L150) |
| `⊤RD = R(true ⊢ false)` | - | [`top_RD_design`](../../deps/UTP-Reactive-Designs/utp_rdes_designs.thy#L154) |
| `⊥RD = (¬(ok ∧ wait) ∧ tr ≤ tr') ∨ (ok ∧ wait ∧ II)` | - | [`bottom_RD_eval`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L691) |
| `⊤RD = (¬ok ∧ tr ≤ tr') ∨ (ok ∧ wait ∧ II)` | - | [`top_RD_eval`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L698) |

Both zero-law proofs use `RD_eq_active`: every RD process lies between `⊥RD` and
`⊤RD`, which agree at unstarted and waiting priors, so only active priors need
checking.

| Fact | Premises | Lemma |
| --- | --- | --- |
| `⊥RD is RD`, `⊤RD is RD` | - | [`bottom_RD_is_RD`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L662), [`top_RD_is_RD`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L665) |
| `⊥RD ⊑ P` | `P is RD` | [`bottom_RD_lower`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L668) |
| `P ⊑ ⊤RD` | `P is RD` | [`top_RD_upper`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L678) |
| `P = Q` if they agree at every active prior (`ok ∧ ¬wait`) | `P`, `Q` both `RD` | [`RD_eq_active`](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L706) |

Feasibility is not enough for the Chaos law, unlike D. Chaos diverges at the prior
trace, but the output must still extend the trace that `j` merges. So `P` needs an
observation at the prior trace, and `j` must merge empty traces into an empty
trace:

```isabelle
(P ∧ tr' = tr) is H4
∀s sL sR. ∃s'. j((0,s), (0,sL), (0,sR), (0,s'))
```

- With interleaving, a `P` that must perform an event first gives a parallel that
  cannot end at the prior trace.
- Waiting, terminating or diverging at once all qualify.
- The Circus Chaos law asks for the same through CACC
  ([related work](related-work.md)).

## Correspondence with upstream RD parallel

Ordinary RD parallel agrees with upstream parallel at `st = ()`, preserving all
other observations, including refusals. Write `U` for [`unit_state_relation`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L137)
and `M = unit_state_rd_merge j`, using [`unit_state_rd_merge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L13).

| Law | Premises | Lemma |
| --- | --- | --- |
| `M is RDM` | - | [`unit_state_rd_merge_RDM`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L47) |
| Completed merges agree under [`to_unit_state`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L57) | - | [`merge_rdes_unit_state`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L119) |
| `U (P ∥RD[j] Q) =`<br>`U P ∥R[M] U Q` | - | [`rdes_lift_parallel_unit_state_eq`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_unit_state.thy#L154) |

See [Stateful RD](RD-stateful.md) for broader completion premises and
[RAD](RAD.md) for choice-set lifting and RD/RAD mapping laws.
