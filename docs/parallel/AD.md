# Angelic design parallel by merge

[Overview](README.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md) · [AP](AP.md)

[utp_ades_parallel.thy](../../angelic-designs/utp_ades_parallel.thy)
defines the sole AD operator, `ades_par`, written `P ∥AD[j] Q`.

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
| `j :: 's merge`; `j(s0,sL,sR,sOut)` | State merge |
| `P ∥[merge_ades j] Q` | Lifted parallel |
| `P ∥AD[j] Q` | AD parallel |
| `D ∥D[j] E` | Ordinary-design parallel |

## Lifting state merge

The construction converts a state merge into an angelic design merge. In the
completed merge, every pair of
branch states must have some merged state; coverage of the output set is
required only when both branch observations terminate. This follows the
ordinary design merge `merge_des j = HDM (merge_des_raw j) ;; II_D` (see the
[D guide](D.md)).

The AD prefix identifies the target layer; `ades_lift_merge` is the raw lift,
while `merge_ades` is the completed merge. The recipe starts with
`ades_lift_merge :: 's merge ⇒ 's ades_merge_rel`:

```isabelle
ades_lift_merge(j)((ok0,s0), (okL,SL), (okR,SR), (okOut,SOut))
  = SL ≠ {} ∧ SR ≠ {}
    ∧ (okOut = (okL ∧ okR))
    ∧ (∀sL∈SL. ∀sR∈SR. ∃sOut∈SOut. j(s0,sL,sR,sOut))
```

The raw lift requires witnesses in its output choice set even when a branch
diverges. The final composition with design skip releases the actual final
choice set in that case, while retaining an intermediate witness.

### Design merge healthiness

[`ADH1m`](../../angelic-designs/utp_ades_parallel.thy#L54),
[`ADH2m`](../../angelic-designs/utp_ades_parallel.thy#L57),
[`ADH3m`](../../angelic-designs/utp_ades_parallel.thy#L64), and
[`ADHM`](../../angelic-designs/utp_ades_parallel.thy#L70)
each have type `'s ades_merge_rel ⇒ 's ades_merge_rel`:

```isabelle
ADH1m M = M ∨ ¬ok0
ADH2m M = M ;; J
ADH3m M ≡ M ;; II_D
ADHM M  = ADH1m (ADH2m M)
```

These follow the ordinary-design definitions of
[`H1m`](../../deps/UTP-Designs/utp_des_parallel.thy#L20) and
[`H2m`](../../deps/UTP-Designs/utp_des_parallel.thy#L25), adapted to the AD merge
types with an input state and output choice sets. Likewise, `ADHM` follows
[`HDM`](../../deps/UTP-Designs/utp_des_parallel.thy#L35).

`ADH1m` removes constraints when not started. `ADH2m` uses the ordinary design
relation `J` to allow a false output flag to become true, preserving the choice
set. These handle H1/H2 behaviour; they do not impose A1, A2, or A3.

`ADH3m` expresses the ordinary H3 right-skip fixed-point property on the
AD merge type: `M is ADH3m` means `M ;; II_D = M`. It is distinct from
angelic A3. `ADH3m_idem` proves idempotence. `ADHM` continues to combine
ADH1m and ADH2m; its definition does not include ADH3m.

[`merge_ades`](../../angelic-designs/utp_ades_parallel.thy#L73) is defined by the
raw lift followed by completion:

```isabelle
merge_ades j ≡ ADH1m (ades_lift_merge j) ;; II_D
```

The recipe preserves the previous semantics; its equivalence proof is recorded
in the [recipe audit](../reviews/README.md#stage-1-ad-recipe-and-closure). The old
`lift_merge` compatibility definition has been removed from the main theory.
The lemmas `merge_ades_ADH1m`, `merge_ades_ADH2m`, and `merge_ades_ADHM` prove
merge healthiness for every `j`. `merge_ades_completion` proves
`merge_ades j ;; II_D = merge_ades j`.
The equivalent healthiness statement, `merge_ades j is ADH3m`, is proved
without premises by `merge_ades_ADH3m`.

ADH2m still means composition with `J`: the new construction satisfies it
because `II_D ;; J = II_D`. These merge properties are separate from the
parallel-closure theorems and their operand premises below.

By lemma [`merge_ades_obs`](../../angelic-designs/utp_ades_parallel.thy#L133), the transformed merge is:

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

The branch choice sets remain nonempty, and every branch-state pair has a merged
state, in both started cases. The output set can be empty when either branch
admits nontermination.

## Lifted parallel

`P ∥[merge_ades j] Q` uses the generic UTP
[`par_by_merge`](../../deps/UTP/utp_concurrency.thy#L230) operator with `merge_ades j`.
Its observation form follows from
[`ades_par_by_merge_eval`](../../angelic-designs/utp_ades_parallel.thy#L143):

```isabelle
(P ∥[merge_ades j] Q)(ok0,s0,okOut,SOut)
  iff ∃okL SL okR SR.
       P(ok0,s0,okL,SL)
     ∧ Q(ok0,s0,okR,SR)
     ∧ merge_ades(j)((ok0,s0), (okL,SL), (okR,SR), (okOut,SOut))
```

Both operands share the initial observation. Each accepts a branch output,
and the lifted merge relates those outputs to the final observation.

The `A`, `A2`, and `A3` closure laws hold for arbitrary `j`:

| Healthiness | Operand premises | Conclusion | Lemma  |
| --- | --- | --- | --- |
| `A` | `P is H1`, `Q is H1` | `(P ∥[merge_ades j] Q) is A` | [`ades_par_lifted_A_closure`](../../angelic-designs/utp_ades_parallel.thy#L149) |
| `A2` | `P is A2`, `Q is A2` | `(P ∥[merge_ades j] Q) is A2` | [`ades_par_lifted_A2_closure`](../../angelic-designs/utp_ades_parallel.thy#L225) |
| `A3` | `P is H1`, `Q is H1` | `(P ∥[merge_ades j] Q) is A3` | [`ades_par_lifted_A3_closure`](../../angelic-designs/utp_ades_parallel.thy#L238) |

A3 now holds directly. If a started nonterminating output is accepted at any
choice set, the same branch observations accept every output set, including
the empty set. Thus the singleton-failure premise of A3 already implies its
empty-set conclusion.

A2 closure needs neither A nor H1 on the operands. A2 already guarantees that
an accepted nonempty branch set contains an accepted singleton. The observation
lemma `ades_par_lifted_obs_A2` keeps operand feasibility explicit when `ok0=False`;
that condition is independent of the final choice set. The older
`ades_par_lifted_obs` retains its A/A2 premises and simplifies this unstarted
case using H1. The D/AD correspondence premises remain unchanged.

## AD parallel by merge

[`ades_par`](../../angelic-designs/utp_ades_parallel.thy#L257), written `P ∥AD[j] Q`,
is defined by applying `A3` to the lifted parallel composition `P ∥[merge_ades j] Q`:

```isabelle
P ∥AD[j] Q = A3 (P ∥[merge_ades j] Q)
```

For H1-healthy operands, A3 is redundant: [`ades_par_eq_lifted`](../../angelic-designs/utp_ades_parallel.thy#L262)
proves `P ∥AD[j] Q = P ∥[merge_ades j] Q` for every `j`. The wrapper
retains unconditional A3 closure for arbitrary operands.

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `A` | `P is H1`, `Q is H1` | `(P ∥AD[j] Q) is A` | [`ades_par_A_closure`](../../angelic-designs/utp_ades_parallel.thy#L268) |
| `A2` | `P is A2`, `Q is A2` | `(P ∥AD[j] Q) is A2` | [`ades_par_A2_closure`](../../angelic-designs/utp_ades_parallel.thy#L274) |
| `A3` | None | `(P ∥AD[j] Q) is A3` | [`ades_par_A3_closure`](../../angelic-designs/utp_ades_parallel.thy#L280) |

The wrapped A2 result uses `A3_preserves_A2`; it does not require the wrapper
to be redundant, so no H1 premise is added.

## `ac2p`/`d2ac` mapping laws

All four laws hold for any state merge `j`.

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `P`, `Q` both `A`, `A2` | `ac2p (P ∥AD[j] Q) = (ac2p P) ∥D[j] (ac2p Q)` | [`ades_par_ac2p`](../../angelic-designs/utp_ades_parallel.thy#L344) |
| `D`, `E` both `H` | `(d2ac D) ∥AD[j] (d2ac E) = d2ac (D ∥D[j] E)` | [`ades_par_d2ac`](../../angelic-designs/utp_ades_parallel.thy#L337) |
| `P`, `Q` both `A`, `A2` | `P ∥AD[j] Q = d2ac ((ac2p P) ∥D[j] (ac2p Q))` | [`ades_par_d2ac_ac2p`](../../angelic-designs/utp_ades_parallel.thy#L319) |
| `D`, `E` both `H` | `D ∥D[j] E = ac2p ((d2ac D) ∥AD[j] (d2ac E))` | [`ades_par_ac2p_d2ac`](../../angelic-designs/utp_ades_parallel.thy#L356) |

## Algebraic properties

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P1 ⊑ P2`, `Q1 ⊑ Q2` | `(P1 ∥AD[j] Q1) ⊑ (P2 ∥AD[j] Q2)` | [`ades_par_mono`](../../angelic-designs/utp_ades_parallel.thy#L364) |
| Commutativity | `j is SymMerge` | `P ∥AD[j] Q = Q ∥AD[j] P` | [`ades_par_comm`](../../angelic-designs/utp_ades_parallel.thy#L382) |
| Associativity | `P`, `Q`, `R` all `A2`; `j is SymMerge`; `AssocMerge j`; `mergeable j` | `(P ∥AD[j] Q) ∥AD[j] R = P ∥AD[j] (Q ∥AD[j] R)` | [`ades_par_assoc`](../../angelic-designs/utp_ades_parallel.thy#L394) |

These are sufficient conditions; necessity has not been established.

`merge_ades_SymMerge` proves that `j is SymMerge` implies
`merge_ades j is SymMerge`. Commutativity therefore needs no operand healthiness.

## Associativity premises

[`ades_par_assoc`](../../angelic-designs/utp_ades_parallel.thy#L394)
uses A2-healthy operands and the state-merge premises of
[`des_par_assoc_state`](../../deps/UTP-Designs/utp_des_parallel.thy#L453):
`j is SymMerge`, `AssocMerge j` and
[`mergeable`](../../deps/UTP/utp_concurrency.thy#L62) `j`.
For A2 operands, `ades_par_normalise_A` proves
`P ∥AD[j] Q = A P ∥AD[j] A Q` for every `j`, and `A_preserves_A2`
preserves A2 under this normalisation. The proof then maps the normalised
operands to designs with `ac2p` and `d2ac` and applies the design law.
The correspondence lemmas retain their A/A2 premises. Associativity outside
A2 and necessity of the merge premises have not been established. `D.md`
explains the premises; mergeability prevents an intermediate terminating pair
from becoming infeasible before it meets a divergent branch.

## Nontermination and Chaos

[`ades_par_lifted_diverge`](../../angelic-designs/utp_ades_parallel.thy#L232)
proves that accepting one nonterminating output permits every output flag and
choice set at the same initial observation. A started lifted parallel admits
all outputs when one branch supplies a nonterminating observation with a
nonempty choice set, the other supplies any observation with a nonempty choice
set, and every pair of their branch states has some merged state. The branch
observations must exist even though the output guarantee is released.

In particular, when `j` has some merged state at every initial state
(`∀s0. ∃sL sR sOut. j(s0,sL,sR,sOut)`):

```text
Chaos ∥[merge_ades j] Chaos = Chaos
Chaos ∥AD[j] Chaos = Chaos
```

These are [`ades_par_lifted_chaos`](../../angelic-designs/utp_ades_parallel.thy#L467)
and [`ades_par_chaos`](../../angelic-designs/utp_ades_parallel.thy#L486).
Chaos is the predicate `true`, equivalently a design with false precondition.
No A3 completion or mergeability premise is needed for the lifted Chaos law.

## Lifted mapping laws

Since A3 is redundant for healthy operands, the lifted operator has the same
mapping laws without any additional restriction on `j`:

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `P`, `Q` both A, A2 | `ac2p (P ∥[merge_ades j] Q) = (ac2p P) ∥D[j] (ac2p Q)` | [`ades_par_lifted_ac2p`](../../angelic-designs/utp_ades_parallel.thy#L445) |
| `D`, `E` both H | `(d2ac D) ∥[merge_ades j] (d2ac E) = d2ac (D ∥D[j] E)` | [`ades_par_lifted_d2ac`](../../angelic-designs/utp_ades_parallel.thy#L452) |

## Skip merge example

The skip state merge requires `sOut = s0`. For H1-healthy operands,
[`ades_par_skip_eval`](../../angelic-designs/utp_ades_parallel.thy#L496) gives:

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
| Commutativity | None | [`ades_par_skip_comm`](../../angelic-designs/utp_ades_parallel.thy#L507) |
| Associativity | `P`, `Q`, `R` all A2 | [`ades_par_skip_assoc`](../../angelic-designs/utp_ades_parallel.thy#L511) |

The skip merge is symmetric, rotation invariant and mergeable, so no additional merge
premise is needed in the specialised associativity theorem.
