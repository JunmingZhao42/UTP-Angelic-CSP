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
| `A3` | `P is H1`, `Q is H1`; `merge_excludes_output j` | `(P ∥[merge_ades j] Q) is A3` | [`ades_par_lifted_A3_closure`](../angelic-designs/utp_ades_parallel.thy#L471) |

A3 is not preserved for arbitrary `j`. The [merge-only criterion below](#a3-closure-without-completion)
characterises when closure holds uniformly over healthy operands.

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

## A3 closure without completion

The Boolean condition
[`merge_excludes_output`](../angelic-designs/utp_ades_parallel.thy#L455)
has type `'s merge ⇒ bool`:

```isabelle
merge_excludes_output j ⟷
  (∀s0. ∃sOut. ∀sL sR. ¬ merge_eval j s0 sL sR sOut)
```

For each initial state, there must be an output state that **no branch-state
pair can merge to**. The excluded state can depend on `s0`, but must be uniform
over `sL` and `sR`. Equivalently, `{sOut. ∃sL sR. j(s0,sL,sR,sOut)}` is a proper
subset of the state space for every `s0`. Excluding a different output for each
branch pair is insufficient.

This condition leaves `lift_merge`, `merge_ades`, and `ades_par` unchanged.
It gives the following results without normality:

| Premises | Conclusion | Lemma |
| --- | --- | --- |
| `P`, `Q` both H1; `merge_excludes_output j` | `(P ∥[merge_ades j] Q) is A3` | [`ades_par_lifted_A3_closure`](../angelic-designs/utp_ades_parallel.thy#L471) |
| Same | `P ∥AD[j] Q = P ∥[merge_ades j] Q` | [`ades_par_eq_lifted`](../angelic-designs/utp_ades_parallel.thy#L479) |

The operands do not need to satisfy A2 or A3 for this closure result.
For A/A2 operands, the existing A and A2 closure laws therefore give all three
healthiness conditions directly on the lifted parallel.

### Why this condition is exact

For H1 operands, [`ades_par_lifted_A3_iff`](../angelic-designs/utp_ades_parallel.thy#L460)
specialises the earlier difference criterion to:

```isabelle
(P ∥[merge_ades j] Q) is A3 ⟷
  (∀s0. ∃sOut.
    ¬ (P ∥[merge_ades j] Q)(True,s0,False,{sOut}))
```

The lifted parallel always rejects started empty observations. A3 therefore
requires, at each initial state, at least one singleton that rejects the
nontermination observation. An output excluded by `j` supplies such a singleton
regardless of the operands. This does not forbid the excluded state from being
an extra member of a larger accepted choice set.

Conversely, choose `P = Q = Chaos`. These operands satisfy A, A2, and A3, and
[`ades_par_lifted_chaos_obs`](../angelic-designs/utp_ades_parallel.thy#L507) gives:

```isabelle
(Chaos ∥[merge_ades j] Chaos)(True,s0,False,{sOut})
  ⟷ (∃sL sR. j(s0,sL,sR,sOut))
```

If `j` reaches every output at some `s0`, every singleton admits nontermination
there, while the empty set is rejected. Thus A3 fails.
[`merge_excludes_output_iff_A3_closure`](../angelic-designs/utp_ades_parallel.thy#L530)
proves that `merge_excludes_output j` is **necessary and sufficient** for closure
for every pair of A/A2/A3-healthy operands. It is therefore the weakest condition
on `j` alone guaranteeing closure for that entire class. For a particular pair
of operands, the operand-dependent criterion above can hold even when this
merge-only condition fails.

### Examples and normality

| State merge | Satisfies the condition? |
| --- | --- |
| `skipₘ`: `sOut = s0` | Exactly when the state type has at least two values; exclude any state different from `s0`. |
| Naturals: `sOut = Suc (sL + sR)` | Yes: exclude `0`. This merge is total and uses both branch states. |
| Right projection: `sOut = sR` | No: every output is reachable. |
| Always-true merge | No: every output is reachable. |

The first three cases are proved in
[`merge_excludes_output_skip_iff`](../angelic-designs/utp_ades_parallel.thy#L574),
[`merge_excludes_output_Suc_add`](../angelic-designs/utp_ades_parallel.thy#L578), and
[`merge_excludes_output_right_projection`](../angelic-designs/utp_ades_parallel.thy#L583).

**Normality alone does not suffice for the current lift.** Chaos is normal,
yet its lifted parallel with the always-true merge is not A3-healthy
([`normal_operands_not_lifted_A3`](../angelic-designs/utp_ades_parallel.thy#L564)).

Nor does the new condition force normality. On Boolean states, Chaos parallel
with `skipₘ` is A3-healthy and has design form
`(s0 ∉ SOut) ⊢ (s0 ∈ SOut)`. Its precondition depends on the output choice set;
[`ades_par_lifted_skip_not_normal`](../angelic-designs/utp_ades_parallel.thy#L591)
proves that the result is not normal.

### Mapping and algebraic laws

For H1 operands, under `merge_excludes_output j`, `ades_par_eq_lifted` lets the
existing mapping and algebraic laws transfer to lifted parallel, retaining any
further operand and merge premises. In particular:

| Additional premises | Equality | Lemma |
| --- | --- | --- |
| `P`, `Q` both A, A2 | `ac2p (P ∥[merge_ades j] Q) = (ac2p P) ∥D[j] (ac2p Q)` | [`ades_par_lifted_ac2p`](../angelic-designs/utp_ades_parallel.thy#L485) |
| `D`, `E` both H | `(d2ac D) ∥[merge_ades j] (d2ac E) = d2ac (D ∥D[j] E)` | [`ades_par_lifted_d2ac`](../angelic-designs/utp_ades_parallel.thy#L492) |

The other two mapping equalities follow by the same rewrite. Associativity
still requires the state-merge associativity premise; the excluded-output
condition does not imply it.

## A monotone idempotent merge healthiness

Fix a function `w :: 's ⇒ 's` selecting an excluded output for each initial
state. The transformer [`A3j w`](../angelic-designs/utp_ades_parallel.thy#L614)
has type `'s merge ⇒ 's merge` and is given observationally by:

```isabelle
merge_eval (A3j w j) s0 sL sR sOut ⟷
  merge_eval j s0 sL sR sOut ∧ sOut ≠ w s0
```

It removes exactly those merge tuples whose output is `w s0`, preserving all
other tuples. Keep `w` fixed when comparing or repeatedly transforming merges;
the monotonicity theorem does not cover choosing a different witness from
each input merge.

| Property | Law | Lemma |
| --- | --- | --- |
| Idempotence | `A3j w (A3j w j) = A3j w j` | [`A3j_idem`](../angelic-designs/utp_ades_parallel.thy#L622) |
| Monotonicity in UTP refinement | `j ⊑ k ⟹ A3j w j ⊑ A3j w k` | [`A3j_mono`](../angelic-designs/utp_ades_parallel.thy#L628) |
| Strengthening | `j ⊑ A3j w j` | [`A3j_refine`](../angelic-designs/utp_ades_parallel.thy#L634) |
| Fixed points | `j is A3j w ⟷ (∀s0 sL sR. ¬ j(s0,sL,sR,w s0))` | [`A3j_healthy_iff`](../angelic-designs/utp_ades_parallel.thy#L640) |
| Sufficient merge condition | `merge_excludes_output (A3j w j)` | [`A3j_excludes_output`](../angelic-designs/utp_ades_parallel.thy#L644) |

Consequently, [`ades_par_lifted_A3j_closure`](../angelic-designs/utp_ades_parallel.thy#L652)
proves:

```isabelle
P is H1 ⟹ Q is H1 ⟹ j is A3j w ⟹
  (P ∥[merge_ades j] Q) is A3
```

Every `A3j w j` is itself `A3j w`-healthy, so the same closure holds when any
supplied merge is first transformed. In particular,
[`ades_par_A3j_eq_lifted`](../angelic-designs/utp_ades_parallel.thy#L658) gives,
for H1 operands:

```isabelle
P ∥AD[A3j w j] Q = P ∥[merge_ades (A3j w j)] Q
```

This removes the need for outer A3 **for the transformed merge**. It does not
assert equality with parallel using the original `j`; the transformer may
have removed behaviours. The `ac2p`/`d2ac` laws apply with `A3j w j` on the
ordinary-design side as well. Operand normality is not required.

For fixed `w`, this is a sufficient subclass of `merge_excludes_output`.
The family covers the whole Boolean condition:

```isabelle
merge_excludes_output j ⟷ (∃w. j is A3j w)
```

This is proved by
[`merge_excludes_output_iff_A3j`](../angelic-designs/utp_ades_parallel.thy#L666).

### Choosing the witness and preserving other laws

- For Boolean `skipₘ`, choose `w = Not`: the merge is already healthy and remains
  unchanged. Generally, skip is healthy exactly when `∀s0. w s0 ≠ s0`
  ([`A3j_skip_healthy_iff`](../angelic-designs/utp_ades_parallel.thy#L683)).
- For the natural-number merge `sOut = Suc (sL + sR)`, choose `w = (λ_. 0)`;
  this also leaves the merge unchanged
  ([`A3j_Suc_add_healthy`](../angelic-designs/utp_ades_parallel.thy#L687)).
- `A3j id` is a concrete transformer of type `merge ⇒ merge`, requiring no
  additional choice. It forbids `sOut = s0`, however, so it turns `skipₘ` into
  the false merge ([`A3j_id_skip`](../angelic-designs/utp_ades_parallel.thy#L691)).

[`A3j_SymMerge`](../angelic-designs/utp_ades_parallel.thy#L671) proves that
symmetry is preserved. Totality and state-merge associativity can be lost.
For example, transform natural-number addition by excluding `0`. The left
bracketing of `(1,0,0)` still reaches `1`, whereas the right bracketing cannot
merge its inner pair `(0,0)` at all. Both the original associativity and this
counterexample are checked in
[`A3j_add_boundary`](../angelic-designs/utp_ades_parallel.thy#L699).
Associativity of parallel therefore still needs the corresponding condition
on the transformed merge.
