# Angelic design parallel by merge

[Overview](../PARALLEL.md) · [AD](AD_PARALLEL.md) · [RAD](RAD_PARALLEL.md) · [AP](AP_PARALLEL.md)

[utp_ades_parallel.thy](../angelic-designs/utp_ades_parallel.thy)
defines the sole AD operator, `ades_par`, written `P ∥AD[j] Q`.

## Common Notations
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
We firstly introduce a lifting operation to convert a state merge predicate into an
angelic design merge predicate.

[`lift_merge`](../angelic-designs/utp_ades_parallel.thy#L32) `:: 's merge ⇒ 's ades_merge_rel`
relates the branch choice sets to the merged choice set and equates the final
termination flag with the conjunction of the branch flags:

```isabelle
lift_merge(j)((ok0,s0), (okL,SL), (okR,SR), (okOut,SOut))
  = SL ≠ {} ∧ SR ≠ {} ∧ (okOut = (okL ∧ okR))
    ∧ (∀sL∈SL. ∀sR∈SR. ∃sOut∈SOut. j(s0,sL,sR,sOut))
```

### Design merge healthiness

[`ADH1m`](../angelic-designs/utp_ades_parallel.thy#L54),
[`ADH2m`](../angelic-designs/utp_ades_parallel.thy#L57), and
[`ADHM`](../angelic-designs/utp_ades_parallel.thy#L60)
each have type `'s ades_merge_rel ⇒ 's ades_merge_rel`:

```isabelle
ADH1m M = M ∨ ¬ok0
ADH2m M = M ;; J
ADHM M  = ADH1m (ADH2m M)
```

These follow the ordinary-design definitions of
[`H1m`](../deps/UTP-Designs/utp_des_parallel.thy#L16) and
[`H2m`](../deps/UTP-Designs/utp_des_parallel.thy#L21), adapted to the AD merge
types with an input state and output choice sets. Likewise, `ADHM` follows
[`HDM`](../deps/UTP-Designs/utp_des_parallel.thy#L25).

`ADH1m` removes constraints when not started. `ADH2m` uses the ordinary design
relation `J` to allow a false output flag to become true, preserving the choice
set. These handle H1/H2 behaviour; they do not impose A1, A2, or A3.

[`merge_ades`](../angelic-designs/utp_ades_parallel.thy#L63) abbreviates the healthy lift: `merge_ades j ≡ ADHM (lift_merge j)`.

By lemma [`merge_ades_obs`](../angelic-designs/utp_ades_parallel.thy#L101), the transformed merge is:

```isabelle
merge_ades(j)((ok0,s0), (okL,SL), (okR,SR), (okOut,SOut))
  = ¬ok0 ∨
    (SL ≠ {} ∧ SR ≠ {} ∧ ((okL ∧ okR) ⇒ okOut) ∧
    (∀sL∈SL. ∀sR∈SR. ∃sOut∈SOut. j(s0,sL,sR,sOut)))
```

- If `ok0` is false, the merge imposes no constraints.
- If `ok0` is true, `SL` and `SR` must be nonempty, and each pair
  `(sL,sR) ∈ SL × SR` must have some `sOut ∈ SOut` satisfying `j(s0,sL,sR,sOut)`.
- If `ok0` is true, `(okL ∧ okR) ⇒ okOut`.
- If `ok0` is true, `SOut` cannot be empty (even when `okOut` can be false).

## Lifted parallel

`P ∥[merge_ades j] Q` uses the generic UTP
[`par_by_merge`](../deps/UTP/utp_concurrency.thy#L223) operator with `merge_ades j`.
Its observation form follows from
[`ades_par_by_merge_eval`](../angelic-designs/utp_ades_parallel.thy#L109):

```isabelle
(P ∥[merge_ades j] Q)(ok0,s0,okOut,SOut)
  iff ∃okL SL okR SR.
       P(ok0,s0,okL,SL)
     ∧ Q(ok0,s0,okR,SR)
     ∧ merge_ades(j)((ok0,s0), (okL,SL), (okR,SR), (okOut,SOut))
```

Both operands share the initial observation. Each accepts a branch output,
and the lifted merge relates those outputs to the final observation.

The `A` and `A2` closure laws hold for arbitrary `j`:

| Healthiness | Operand premises | Conclusion | Lemma  |
| --- | --- | --- | --- |
| `A` | `P is H1`, `Q is H1` | `(P ∥[merge_ades j] Q) is A` | [`ades_par_lifted_A_closure`](../angelic-designs/utp_ades_parallel.thy#L115) |
| `A2` | `P`, `Q` both `A`, `A2` | `(P ∥[merge_ades j] Q) is A2` | [`ades_par_lifted_A2_closure`](../angelic-designs/utp_ades_parallel.thy#L174) |
| `A3` |  | Not preserved in general | More explanation in [later section](#when-a3-changes-parallel) |

## AD parallel by merge

[`ades_par`](../angelic-designs/utp_ades_parallel.thy#L187), written `P ∥AD[j] Q`,
is defined by applying `A3` to the lifted parallel composition `P ∥[merge_ades j] Q`:

```isabelle
P ∥AD[j] Q = A3 (P ∥[merge_ades j] Q)
```

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `A` | `P is H1`, `Q is H1` | `(P ∥AD[j] Q) is A` | [`ades_par_A_closure`](../angelic-designs/utp_ades_parallel.thy#L192) |
| `A2` | `P`, `Q` both `A`, `A2` | `(P ∥AD[j] Q) is A2` | [`ades_par_A2_closure`](../angelic-designs/utp_ades_parallel.thy#L198) |
| `A3` | None | `(P ∥AD[j] Q) is A3` | [`ades_par_A3_closure`](../angelic-designs/utp_ades_parallel.thy#L204) |

## `ac2p`/`d2ac` mapping laws

All four laws hold for any state merge `j`.

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `P`, `Q` both `A`, `A2` | `ac2p (P ∥AD[j] Q) = (ac2p P) ∥D[j] (ac2p Q)` | [`ades_par_ac2p`](../angelic-designs/utp_ades_parallel.thy#L249) |
| `D`, `E` both `H` | `(d2ac D) ∥AD[j] (d2ac E) = d2ac (D ∥D[j] E)` | [`ades_par_d2ac`](../angelic-designs/utp_ades_parallel.thy#L242) |
| `P`, `Q` both `A`, `A2` | `P ∥AD[j] Q = d2ac ((ac2p P) ∥D[j] (ac2p Q))` | [`ades_par_d2ac_ac2p`](../angelic-designs/utp_ades_parallel.thy#L224) |
| `D`, `E` both `H` | `D ∥D[j] E = ac2p ((d2ac D) ∥AD[j] (d2ac E))` | [`ades_par_ac2p_d2ac`](../angelic-designs/utp_ades_parallel.thy#L261) |

## Algebraic properties

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P1 ⊑ P2`, `Q1 ⊑ Q2` | `(P1 ∥AD[j] Q1) ⊑ (P2 ∥AD[j] Q2)` | [`ades_par_mono`](../angelic-designs/utp_ades_parallel.thy#L269) |
| Commutativity | `merge_ades j is SymMerge` | `P ∥AD[j] Q = Q ∥AD[j] P` | [`ades_par_comm`](../angelic-designs/utp_ades_parallel.thy#L281) |
| Associativity | `P`, `Q`, `R` all `A`, `A2`; `j is SymMerge`; `AssocMerge j` | `(P ∥AD[j] Q) ∥AD[j] R = P ∥AD[j] (Q ∥AD[j] R)` | [`ades_par_assoc`](../angelic-designs/utp_ades_parallel.thy#L317) |

These are sufficient conditions, not necessary ones.

## When A3 changes parallel

Here we will go through in what cases A3 doesn't hold for `P || Q` using just lifted merge.

Some abbrevations that might go handy: assume `P` and `Q` are H1-healthy; `j` is arbitrary. Define the lifted parallel’s
nontermination and termination observations:

```isabelle
Failure(s0,SOut) = (P ∥[merge_ades j] Q)(ok0=True, s0, okOut=False, SOut)
Success(s0,SOut) = (P ∥[merge_ades j] Q)(ok0=True, s0, okOut=True,  SOut)
Empty(s0,SOut)   = (SOut = {} ∧ ∀sOut. Failure (s0, {sOut}))
```
 - Note that here `sOut` is a state and `SOut` is a set.
 - `Failure`: lifted parallel admits nontermination (`okOut=False`).
 - `Success`: lifted parallel admits termination (`okOut=True`).
 - `Empty`: `SOut` is the empty choice set; and every singleton admits nontermination.

| Operator | Design form | Lemma |
| --- | --- | --- |
| `P ∥[merge_ades j] Q` | `(¬Failure) ⊢ Success` | [`ades_par_lifted_rdesign`](../angelic-designs/utp_ades_parallel.thy#L345) |
| `P ∥AD[j] Q` | `(¬Failure ∧ ¬Empty) ⊢ Success` | [`ades_par_rdesign`](../angelic-designs/utp_ades_parallel.thy#L364) |

**Recall A3:** If the AD precondition holding at `SOut={}`, the it also needs to hold at some singleton `{sOut}`. Equivalently by contrapositive, if the precondition is false at every singleton, it must be false at `{}` too. 

**Intuition:** 
 - Lifted parallel always rejects the empty output set when started:
nonempty branch sets need an output witness. Its precondition `¬Failure`
therefore holds at `{}`. 

- Here the precondition is ¬Failure. If lifted parallel allows nontermination for every singleton at the same initial state s0, then ¬Failure is false for every singleton. But ¬Failure still holds at {}, so lifted parallel is not A3-healthy.

- Applying A3 changes the precondition to `¬Failure ∧ ¬Empty`. If `SOut ≠ {}`, `Empty` is false, so the design is unchanged. If `SOut = {}` and every singleton admits nontermination at `s0`, `Empty` is true, making the precondition false.

### Iff lemma

For H1-healthy `P` and `Q` and arbitrary `j`,
[`ades_par_ne_lifted_iff`](../angelic-designs/utp_ades_parallel.thy#L371) proves:

```isabelle
P ∥AD[j] Q ≠ P ∥[merge_ades j] Q
  iff ∃s0. Empty(s0,{})
```

### Chaos Example 
For `P = Q = Chaos = False ⊢ True` and `j = True`, `Failure = Success = (SOut ≠ {})`:

```isabelle
Lifted parallel:  (SOut = {}) ⊢ (SOut ≠ {})
AD parallel:      False       ⊢ (SOut ≠ {}) = Chaos
```

These are proved by [`ades_par_lifted_chaos`](../angelic-designs/utp_ades_parallel.thy#L394)
and [`ades_par_chaos`](../angelic-designs/utp_ades_parallel.thy#L401), respectively;
Isabelle writes Chaos as `true`.

## Skip merge example

The skip state merge requires `sOut = s0`. For a started AD parallel,
a nonempty result must contain `s0`; the evaluation below also includes
the empty-set case added by A3.

| Property | Premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| AD parallel evaluation | `P is H1`, `Q is H1` | Evaluation formula below | [`ades_par_skip_eval`](../angelic-designs/utp_ades_parallel.thy#L415) |
| AD parallel commutativity | None | `P ∥AD[skipₘ] Q = Q ∥AD[skipₘ] P` | [`ades_par_skip_comm`](../angelic-designs/utp_ades_parallel.thy#L437) |
| AD parallel associativity | `P`, `Q`, `R` all `A`, `A2` | `(P ∥AD[skipₘ] Q) ∥AD[skipₘ] R = P ∥AD[skipₘ] (Q ∥AD[skipₘ] R)` | [`ades_par_skip_assoc`](../angelic-designs/utp_ades_parallel.thy#L442) |

```isabelle
(P ∥AD[skipₘ] Q)(ok0,s0,okOut,SOut) =
  ¬ok0 ∨ (∃okL SL okR SR.
    SL ≠ {} ∧ SR ≠ {} ∧
    P(True,s0,okL,SL) ∧ Q(True,s0,okR,SR) ∧
    ((s0 ∈ SOut ∧ (okL ∧ okR ⇒ okOut)) ∨
     (SOut = {} ∧ (∀s'. s' = s0) ∧ ¬(okL ∧ okR))))
```

The last clause (`SOut = {} ∧ ...`) is the A3 addition. It accepts the empty
output set when `s0` is the only state in the state space and both branches
admit nonempty choice sets with at least one termination flag false.
This observation is added by A3.
If the state type has at least two values, this clause is always false.
