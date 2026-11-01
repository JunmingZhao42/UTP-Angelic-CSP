# Angelic design parallel by merge

[Overview](README.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md) · [AP](AP.md)

[utp_ades_parallel.thy](../../angelic-designs/utp_ades_parallel.thy)
defines the sole AD operator, `ades_par`, written `P ∥AD[j] Q`. The theory
first states conditions on an arbitrary merge under which parallel by merge
preserves AD healthiness, then lifts a state merge to a merge that meets all
of them, and finally defines `ades_par` and proves its laws. Lemmas are cited
by name; all are in that theory unless a link says otherwise.

## Common notations

The initial observation is usually `(ok0,s0)`.
Branch and merged outputs pair a flag with a choice set, such as `(okL,SL)` and `(okOut,SOut)`.

| Role | Flag | Individual state | Choice set |
| --- | --- | --- | --- |
| Initial | `ok0` | `s0` | — |
| Left branch | `okL` | `sL` | `SL` |
| Right branch | `okR` | `sR` | `SR` |
| Merged output | `okOut` | `sOut` | `SOut` |
| Third branch (associativity) | `okThird` | `sThird` | `SThird` |
| Intermediate result | `okMid` | `sMid` | `SMid` |

| Notation | Meaning |
| --- | --- |
| `P`, `Q`, `R`| Angelic designs |
| `D`, `E` | Ordinary designs |
| `M :: 's ades_merge_rel` | AD merge: relates the prior and both branch outputs to an output |
| `j :: 's merge`; `j(s0,sL,sR,sOut)` | State merge |
| `P ∥[M] Q` | Generic parallel by merge |
| `P ∥[merge_ades j] Q` | Lifted parallel |
| `P ∥AD[j] Q` | AD parallel |
| `D ∥D[j] E` | Ordinary-design parallel |

## Merge observations and slices

A *slice* `merge_slice M l r` fixes both branch outputs of `M`. What remains
relates the prior to the output, so it is an AD relation and AD healthiness
conditions apply to it. A merge is determined by its slices
(`merge_slice_ext`), and parallel by merge is the union of the slices that the
operands reach (`ades_par_by_merge_slices`):

```isabelle
(P ∥[M] Q)(ok0,s0,okOut,SOut)
  iff ∃okL SL okR SR.
       P(ok0,s0,okL,SL)
     ∧ Q(ok0,s0,okR,SR)
     ∧ merge_slice M (okL,SL) (okR,SR) (ok0,s0,okOut,SOut)
```

## Merge healthiness

`Xm` is the merge condition under which parallel by merge preserves `X`. The
design conditions come from
[`utp_des_parallel.thy`](../../deps/UTP-Designs/utp_des_parallel.thy), whose
definitions allow the prior, branch and output alphabets of a merge to differ,
so the same constants serve D and AD. The angelic conditions are new here.

| Condition | Definition | Meaning, per started prior and branch pair |
| --- | --- | --- |
| `H1m` (D) | `M ∨ ¬ok0` | Not started: any output |
| `H2m` (D) | `M ;; J` | Diverging with `SOut` allows terminating with `SOut` |
| `H3m` (D) | `M ;; II_D` | If the merge may diverge at all, any output |
| `HDM` (D) | `H1m ∘ H2m` | Both `H1m` and `H2m` |
| `Am` | A's clauses on the output (below) | Every slice is A: output sets are upward closed, and termination with `{}` is allowed only where divergence with `{}` is |
| `A2m` | `A2m_reduce ∘ A2m_atoms` | The two parts below |
| `A2m_atoms` | — | Every slice whose branch choice sets are singletons is A2 |
| `A2m_reduce` | — | An output allowed for `(SL, SR)` is allowed for every `({x}, {y})` with `x` from `SL` and `y` from `SR`; any state may be drawn from an empty set |

Like `H1m`, `Am` is defined explicitly:

```isabelle
Am M ≡ (λ(m,z). let Z = ac z in
          ¬ ok (prior m)
        ∨ (∃Y⊆Z. M (m, (False, Y)))
        ∨ (ok z ∧ Z ≠ {} ∧ (∃Y⊆Z. M (m, (True, Y)))))
```

Each disjunct is one clause of A's observation form (`A_obs`): not started;
divergence with a subset of the output set; termination with a subset of a
nonempty output set.

`merge_health H` applies `H` to every slice. Each condition has a slice-wise
form at the AD type: `H1m_merge_health`, `H2m_merge_health`,
`H3m_merge_health`, `HDM_merge_health` and `Am_merge_health` prove
`H1m M = merge_health H1 M` and likewise for H2, H3, **H** and A. There is no
`A3m`: A3 closure follows from `H1m` and `H3m`. `A2m` is not "A2 on every slice", which the lifted
merge fails; the two parts are the conditions the A2 rule needs. `Am` and `A2m`
are idempotent and monotone (`Am_Idempotent`, `Am_Monotonic`, `A2m_Idempotent`,
`A2m_Monotonic`), and `A2m_fixed` splits `M is A2m` into its two parts.

## Parallel by merge preserves AD healthiness

These rules hold for an arbitrary merge `M`. The H rules are D's, stated for
merges whose alphabets differ.

| Result | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| H1 | `P is H1`, `Q is H1` | `M is H1m` | [`H1_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel.thy) |
| H2 | None | `M is H2m` | [`H2_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel.thy) |
| H3 | None | `M is H3m` | [`H3_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel.thy) |
| A | `P is H1`, `Q is H1` | `M is Am` | `A_par_by_merge` |
| A2 | `P is A2`, `Q is A2` | `M is A2m` | `A2_par_by_merge` |
| A3 | `P is H1`, `Q is H1` | `M is H1m`, `M is H3m` | `A3_par_by_merge` |

The A3 rule combines the H1 and H3 rules with
[`H1_H3_impl_A3`](../../angelic-designs/utp_ades_healthy.thy): under H3, failure
at one output admits every output, so failure at every singleton gives failure
at the empty set. The A2 rule uses `ades_par_by_merge_singletons`: with A2
operands and `A2m_reduce`, parallel by merge is determined by singleton branch
outputs.

These are sufficient conditions. Which premises are also necessary is open
(PLAN Stage 1).

## Lifting a state merge

The construction converts a state merge into an AD merge. In the completed
merge, every pair of branch states must have some merged state; coverage of the
output set is required only when both branch observations terminate. This
follows the ordinary design merge `merge_des j = HDM (merge_des_raw j) ;; II_D`
(see the [D guide](D.md)).

`ades_lift_merge` is the raw lift and `merge_ades` the completed merge. The raw
lift is:

```isabelle
ades_lift_merge(j)((ok0,s0), (okL,SL), (okR,SR), (okOut,SOut))
  = SL ≠ {} ∧ SR ≠ {}
    ∧ (okOut = (okL ∧ okR))
    ∧ (∀sL∈SL. ∀sR∈SR. ∃sOut∈SOut. j(s0,sL,sR,sOut))
```

It requires witnesses in its output choice set even when a branch diverges.
Completing with design skip releases the final choice set in that case, while
retaining an intermediate witness:

```isabelle
merge_ades j ≡ H1m (ades_lift_merge j) ;; II_D
```

By `merge_ades_obs`, the completed merge is:

```isabelle
merge_ades(j)((ok0,s0), (okL,SL), (okR,SR), (okOut,SOut))
  = ¬ok0 ∨
    (SL ≠ {} ∧ SR ≠ {}
     ∧ (∀sL∈SL. ∀sR∈SR. ∃sOut. j(s0,sL,sR,sOut))
     ∧ ((okL ∧ okR) ⇒
        (okOut ∧ (∀sL∈SL. ∀sR∈SR. ∃sOut∈SOut. j(s0,sL,sR,sOut)))))
```

| Merge input | Output requirement |
| --- | --- |
| `ok0=False` | None |
| Started, both branch flags true | Nonempty `SL`, `SR`; `okOut=True`; every branch-state pair has a witness in `SOut` |
| Started, at least one branch flag false | Nonempty `SL`, `SR`; every branch-state pair has some merged state; no constraint on `okOut` or `SOut` |

The output set can be empty when either branch admits nontermination.

`merge_ades j` meets every merge condition, for every `j`: `merge_ades_is_H1m`,
`merge_ades_is_H2m`, `merge_ades_is_HDM`, `merge_ades_is_H3m`,
`merge_ades_is_Am` and `merge_ades_is_A2m`. `merge_ades_completion` gives the
rewrite `merge_ades j ;; II_D = merge_ades j`. The recipe's equivalence with the
earlier construction is recorded in the
[stage log](../reviews/README.md#stage-1-ad-recipe-and-closure).

## AD parallel

`ades_par`, written `P ∥AD[j] Q`, applies `A3` to the lifted parallel
composition:

```isabelle
P ∥AD[j] Q = A3 (P ∥[merge_ades j] Q)
```

Closure of lifted parallel follows from the generic rules and the facts about
`merge_ades j`, for every `j`:

| Healthiness | Operand premises | Lifted lemma | AD lemma |
| --- | --- | --- | --- |
| A | `P is H1`, `Q is H1` | `ades_par_lifted_A_closure` | `ades_par_A_closure` |
| A2 | `P is A2`, `Q is A2` | `ades_par_lifted_A2_closure` | `ades_par_A2_closure` |
| A3 | `P is H1`, `Q is H1` (lifted); none (AD) | `ades_par_lifted_A3_closure` | `ades_par_A3_closure` |

For H1-healthy operands, the A3 wrapper is redundant: `ades_par_eq_lifted`
proves `P ∥AD[j] Q = P ∥[merge_ades j] Q`. The wrapper keeps A3 closure for
arbitrary operands, and `A3_preserves_A2` carries A2 through it without an H1
premise.

A2 closure needs neither A nor H1 on the operands. `ades_par_lifted_obs_A2`
evaluates lifted parallel for A2 operands through singleton branch outputs and
keeps operand feasibility explicit when `ok0=False`; `ades_par_lifted_obs` uses
A and A2 to simplify that case. `ades_par_obs_A2` and `ades_par_eval` give the
corresponding forms for `ades_par`, and `ades_par_normalise_A` proves
`P ∥AD[j] Q = A P ∥AD[j] A Q` for A2 operands.

## `ac2p`/`d2ac` mapping laws

All laws hold for any state merge `j`.

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `P`, `Q` both `A`, `A2` | `ac2p (P ∥AD[j] Q) = (ac2p P) ∥D[j] (ac2p Q)` | `ades_par_ac2p` |
| `D`, `E` both `H` | `(d2ac D) ∥AD[j] (d2ac E) = d2ac (D ∥D[j] E)` | `ades_par_d2ac` |
| `P`, `Q` both `A`, `A2` | `P ∥AD[j] Q = d2ac ((ac2p P) ∥D[j] (ac2p Q))` | `ades_par_d2ac_ac2p` |
| `D`, `E` both `H` | `D ∥D[j] E = ac2p ((d2ac D) ∥AD[j] (d2ac E))` | `ades_par_ac2p_d2ac` |
| `P`, `Q` both `A`, `A2` | `ac2p (P ∥[merge_ades j] Q) = (ac2p P) ∥D[j] (ac2p Q)` | `ades_par_lifted_ac2p` |
| `D`, `E` both `H` | `(d2ac D) ∥[merge_ades j] (d2ac E) = d2ac (D ∥D[j] E)` | `ades_par_lifted_d2ac` |

## Algebraic laws

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P1 ⊑ P2`, `Q1 ⊑ Q2` | `(P1 ∥AD[j] Q1) ⊑ (P2 ∥AD[j] Q2)` | `ades_par_mono` |
| Commutativity | `j is SymMerge` | `P ∥AD[j] Q = Q ∥AD[j] P` | `ades_par_comm` |
| Associativity | `P`, `Q`, `R` all `A2`; `j is SymMerge`; `AssocMerge j`; `mergeable j` | `(P ∥AD[j] Q) ∥AD[j] R = P ∥AD[j] (Q ∥AD[j] R)` | `ades_par_assoc` |

These are sufficient conditions; necessity has not been established.

`merge_ades_SymMerge` proves that `j is SymMerge` implies
`merge_ades j is SymMerge`, so commutativity needs no operand healthiness.

`ades_par_assoc` uses A2-healthy operands and the state-merge premises of
[`des_par_assoc_state`](../../deps/UTP-Designs/utp_des_parallel.thy):
`j is SymMerge`, `AssocMerge j` and
[`mergeable`](../../deps/UTP/utp_concurrency.thy) `j`. The proof normalises
the operands with `ades_par_normalise_A` (`A_preserves_A2` keeps them A2), maps
them to designs with `ac2p` and `d2ac`, and applies the design law.
Associativity outside A2 has not been established. The [D guide](D.md)
explains the premises; mergeability prevents an intermediate terminating pair
from becoming infeasible before it meets a divergent branch.

### Nontermination and Chaos

`ades_par_lifted_diverge` proves that accepting one nonterminating output
permits every output flag and choice set at the same initial observation. A
started lifted parallel admits all outputs when one branch supplies a
nonterminating observation with a nonempty choice set, the other supplies any
observation with a nonempty choice set, and every pair of their branch states
has some merged state. The branch observations must exist even though the
output guarantee is released.

In particular, when `j` has some merged state at every initial state
(`∀s0. ∃sL sR sOut. j(s0,sL,sR,sOut)`):

```text
Chaos ∥[merge_ades j] Chaos = Chaos
Chaos ∥AD[j] Chaos = Chaos
```

These are `ades_par_lifted_chaos` and `ades_par_chaos`. Chaos is the predicate
`true`, equivalently a design with false precondition. No A3 completion or
mergeability premise is needed for the lifted Chaos law.

## Skip merge example

The skip state merge requires `sOut = s0`. For H1-healthy operands,
`ades_par_skip_eval` gives:

```text
(P ∥AD[skipₘ] Q)(ok0,s0,okOut,SOut)
  iff ¬ok0 ∨ (∃okL SL okR SR.
       SL ≠ {} ∧ SR ≠ {}
     ∧ P(True,s0,okL,SL) ∧ Q(True,s0,okR,SR)
     ∧ ((okL ∧ okR) ⇒ (okOut ∧ s0 ∈ SOut)))
```

When both branch flags are true, `SOut` must contain `s0`. Otherwise, every
output is admitted, including the empty set, regardless of the state-space size.

| Property | Premises | Lemma |
| --- | --- | --- |
| Commutativity | None | `ades_par_skip_comm` |
| Associativity | `P`, `Q`, `R` all A2 | `ades_par_skip_assoc` |

The skip merge is symmetric, rotation invariant and mergeable, so no additional merge
premise is needed in the specialised associativity theorem.
