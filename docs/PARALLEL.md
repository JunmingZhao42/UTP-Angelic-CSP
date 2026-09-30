# Angelic design parallel by merge

The two AD parallel files serve different purposes:

| Theory | Purpose | File structure |
| --- | --- | --- |
| [utp_ades_parallel.thy](../angelic-designs/utp_ades_parallel.thy#L8) | Defines parallel for an AD merge `M`, which sees the choice sets and `ok` flags. | Parallel → merge healthiness and closure → healthiness composition → algebra |
| [utp_ades_parallel_lifted.thy](../angelic-designs/utp_ades_parallel_lifted.thy#L9) | Lifts a state merge `j` to choice sets, in order to prove the `ac2p` and `d2ac` laws. | Lifting → raw correspondence → completed parallel and conversions → algebra → skip example |

Below, `P`, `Q` are angelic designs; `D`, `E` are ordinary designs.
[∥AD\[M\]](../angelic-designs/utp_ades_parallel.thy#L39) is generic AD parallel, [∥AD³\[j\]](../angelic-designs/utp_ades_parallel_lifted.thy#L116) is parallel using `j` with `A3` applied afterwards, and [∥D\[j\]](../deps/UTP-Designs/utp_des_parallel.thy#L264) is ordinary-design parallel.

## 1. Generic parallel: `utp_ades_parallel.thy`

### Parallel and observations

[ades_par](../angelic-designs/utp_ades_parallel.thy#L39) uses the supplied merge directly:

```
(P ∥AD[M] Q)(x,out) ↔ ∃p,q. P(x,p) ∧ Q(x,q) ∧ M(x,p,q,out)
```

Here `x` is the initial observation; `p`, `q` are branch results; `out` is
the merged result. Results contain an `ok` flag and a choice set.

### Merge healthiness and closure

[A0m](../angelic-designs/utp_ades_parallel.thy#L82),
[A1m](../angelic-designs/utp_ades_parallel.thy#L123) and
[A2m](../angelic-designs/utp_ades_parallel.thy#L173) apply A0, A1 and A2 to the merged result,
keeping both branch observations fixed. [A3m w](../angelic-designs/utp_ades_parallel.thy#L225)
uses the same witness `w(s0)` for every pair of branch results at initial
state `s0`. All four are monotonic and idempotent. The following lemmas
show when parallel is healthy:

| Healthiness | Operand premises | Merge premises | Conclusion | Lemma |
| --- | --- | --- | --- | --- |
| `A0` | None | `M is A0m` | `(P ∥AD[M] Q) is A0` | [ades_par_A0_closure](../angelic-designs/utp_ades_parallel.thy#L115) |
| `A1` | `P is H1`, `Q is H1` | `M is A1m` | `(P ∥AD[M] Q) is A1` | [ades_par_A1_closure](../angelic-designs/utp_ades_parallel.thy#L165) |
| `A2` | None | `M is A2m` | `(P ∥AD[M] Q) is A2` | [ades_par_A2_closure](../angelic-designs/utp_ades_parallel.thy#L208) |
| `A3` | `P is H1`, `Q is H1` | `M is A3m w` | `(P ∥AD[M] Q) is A3` | [ades_par_A3_closure](../angelic-designs/utp_ades_parallel.thy#L278) |
| `A` | `P is H1`, `Q is H1` | `M is A0m`, `M is A1m` | `(P ∥AD[M] Q) is A` | [ades_par_A_closure](../angelic-designs/utp_ades_parallel.thy#L295) |

### Combining merge healthiness conditions

The [preservation lemmas](../angelic-designs/utp_ades_parallel.thy#L308)
show that `A2m` and `A3m w` preserve both `A0m` and `A1m` healthiness.
They also commute. Thus, if `M is A0m` and `M is A1m`, then
`A3m w (A2m M)` satisfies all four merge conditions.

### Algebra


| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂`, `M₁ ⊑ M₂` | `(P₁ ∥AD[M₁] Q₁) ⊑ (P₂ ∥AD[M₂] Q₂)` | [ades_par_mono](../angelic-designs/utp_ades_parallel.thy#L385) |
| Disjunction in the left operand | None | `(P ∨ Q) ∥AD[M] R = (P ∥AD[M] R) ∨ (Q ∥AD[M] R)` | [ades_par_disj_left](../angelic-designs/utp_ades_parallel.thy#L391) |
| Disjunction in the right operand | None | `P ∥AD[M] (Q ∨ R) = (P ∥AD[M] Q) ∨ (P ∥AD[M] R)` | [ades_par_disj_right](../angelic-designs/utp_ades_parallel.thy#L395) |
| Commutativity | `M is SymMerge` | `P ∥AD[M] Q = Q ∥AD[M] P` | [ades_par_comm](../angelic-designs/utp_ades_parallel.thy#L411) |
| Associativity | `M is SymMerge`, `AssocMerge M` | `(P ∥AD[M] Q) ∥AD[M] R = P ∥AD[M] (Q ∥AD[M] R)` | [ades_par_assoc](../angelic-designs/utp_ades_parallel.thy#L455) |

The other direction of commutativity/associativity properties. The converse results quantify over all operands:

| Property | Premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| Commutativity implies merge symmetry | `P ∥AD[M] Q = Q ∥AD[M] P` for every `P`, `Q` | `M is SymMerge` | [ades_par_comm_iff](../angelic-designs/utp_ades_parallel.thy#L416) |
| Associativity implies the merge condition | `M is SymMerge`; `(P ∥AD[M] Q) ∥AD[M] R = P ∥AD[M] (Q ∥AD[M] R)` for every `P`, `Q`, `R` | `AssocMerge M` | [ades_par_assoc_iff](../angelic-designs/utp_ades_parallel.thy#L462) |

## 2. Lifting: `utp_ades_parallel_lifted.thy`

### From state merges to choice sets

[lift_merge](../angelic-designs/utp_ades_parallel_lifted.thy#L15) uses `j`
to relate choice sets as follows. Here `s0` is the initial state,
`X`, `Y` are branch choice sets, `Z` is the final choice set, and
`j(s0,sL,sR,sOut)` abbreviates `merge_eval j s0 sL sR sOut`.

```
M_j(s0,X,Y,Z) = X ≠ {} ∧ Y ≠ {}
               ∧ (∀sL∈X. ∀sR∈Y. ∃sOut∈Z. j(s0,sL,sR,sOut))
```

Each branch pair must have a merged result in `Z`. The definition also
handles startup and termination through the `ok` flags.

### Merge healthiness and closure

The lifted merge satisfies both merge conditions needed for A closure:

| Healthiness | Premises on `j` | Conclusion | Lemma |
| --- | --- | --- | --- |
| `A0m` | None | `lift_merge j is A0m` | [lift_merge_is_A0m](../angelic-designs/utp_ades_parallel_lifted.thy#L33) |
| `A1m` | None | `lift_merge j is A1m` | [lift_merge_is_A1m](../angelic-designs/utp_ades_parallel_lifted.thy#L37) |

[ades_par_lifted](../angelic-designs/utp_ades_parallel_lifted.thy#L116) applies A3 after parallel:

```
P ∥AD³[j] Q = A3 (P ∥AD[lift_merge j] Q)
```

For H1-healthy operands, completion [only changes empty final sets](../angelic-designs/utp_ades_parallel_lifted.thy#L144),
admitting them when every singleton permits failure. The closure laws below
need no condition on `j`, no H3 premise, and no A2m or A3m merge premise.

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `A` before completion | `P is H1`, `Q is H1` | `(P ∥AD[lift_merge j] Q) is A` | [ades_par_lift_merge_A_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L123) |
| `A2` before completion | `P`, `Q` both `A`, `A2` | `(P ∥AD[lift_merge j] Q) is A2` | [ades_par_lift_merge_A2_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L103) |
| `A` after completion | `P is H1`, `Q is H1` | `(P ∥AD³[j] Q) is A` | [ades_par_lifted_A_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L128) |
| `A2` after completion | `P`, `Q` both `A`, `A2` | `(P ∥AD³[j] Q) is A2` | [ades_par_lifted_A2_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L134) |
| `A3` after completion | None | `(P ∥AD³[j] Q) is A3` | [ades_par_lifted_A3_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L140) |

### ac2p/d2ac mapping laws

`ac2p` maps angelic designs to ordinary designs; `d2ac` maps back.
All four laws hold for any state merge `j`.

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `P`, `Q` both `A`, `A2` | `ac2p (P ∥AD[lift_merge j] Q) = ac2p P ∥D[j] ac2p Q` | [lift_merge_ac2p](../angelic-designs/utp_ades_parallel_lifted.thy#L83) |
| `P`, `Q` both `A`, `A2` | `ac2p (P ∥AD³[j] Q) = ac2p P ∥D[j] ac2p Q` | [ades_par_lifted_ac2p](../angelic-designs/utp_ades_parallel_lifted.thy#L265) |
| `D`, `E` both `H` | `d2ac D ∥AD³[j] d2ac E = d2ac (D ∥D[j] E)` | [ades_par_lifted_d2ac](../angelic-designs/utp_ades_parallel_lifted.thy#L258) |
| `P`, `Q` both `A`, `A2` | `P ∥AD³[j] Q = d2ac (ac2p P ∥D[j] ac2p Q)` | [ades_par_lifted_d2ac_ac2p](../angelic-designs/utp_ades_parallel_lifted.thy#L239) |

### Algebra

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂` | `(P₁ ∥AD³[j] Q₁) ⊑ (P₂ ∥AD³[j] Q₂)` | [ades_par_lifted_mono](../angelic-designs/utp_ades_parallel_lifted.thy#L277) |
| Commutativity | `lift_merge j is SymMerge` | `P ∥AD³[j] Q = Q ∥AD³[j] P` | [ades_par_lifted_comm](../angelic-designs/utp_ades_parallel_lifted.thy#L284) |
| Associativity | `P`, `Q`, `R` all `A`, `A2`; state associativity below | `(P ∥AD³[j] Q) ∥AD³[j] R = P ∥AD³[j] (Q ∥AD³[j] R)` | [ades_par_lifted_assoc](../angelic-designs/utp_ades_parallel_lifted.thy#L295) |

State associativity keeps the initial state `s0` fixed in both merge steps:

```
(∃sMid. j(s0,sL,sR,sMid) ∧ j(s0,sMid,sThird,sOut))
  ↔ (∃sMid. j(s0,sR,sThird,sMid) ∧ j(s0,sL,sMid,sOut))
```

The condition holds for every `s0`, `sL`, `sR`, `sThird` and `sOut`.
No H3 or additional A3 premise is needed. Completed parallel does not
generally distribute over disjunction.

### Skip merge example

The skip state merge requires `sOut = s0`. Its set lifting therefore
requires `s0 ∈ Z` whenever the computation has started.

| Property | Premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| Merge observation | None | `¬ok0 ∨ (X ≠ {} ∧ Y ≠ {} ∧ (okL ∧ okR ⇒ okOut) ∧ s0 ∈ Z)` | [lift_merge_skip_eval](../angelic-designs/utp_ades_parallel_lifted.thy#L334) |
| Merge symmetry | None | `lift_merge skipₘ is SymMerge` | [lift_merge_skip_SymMerge](../angelic-designs/utp_ades_parallel_lifted.thy#L343) |
| Completed associativity | `P`, `Q`, `R` all `A`, `A2` | `(P ∥AD³[skipₘ] Q) ∥AD³[skipₘ] R = P ∥AD³[skipₘ] (Q ∥AD³[skipₘ] R)` | [ades_par_lifted_skip_assoc](../angelic-designs/utp_ades_parallel_lifted.thy#L323) |

The examples use [ades_bool_choice](../angelic-designs/utp_ades_parallel_lifted.thy#L346),
a design that terminates and requires its chosen Boolean to be in the
result set. It is both [A-healthy](../angelic-designs/utp_ades_parallel_lifted.thy#L356)
and [A2-healthy](../angelic-designs/utp_ades_parallel_lifted.thy#L360).

| Completed skip example | Behaviour when started | Lemma |
| --- | --- | --- |
| Two successful Boolean choices | `okOut ∧ s0 ∈ Z` | [skip_completed_success](../angelic-designs/utp_ades_parallel_lifted.thy#L371) |
| Chaos and a successful Boolean choice | `s0 ∈ Z`; termination is unconstrained | [skip_completed_failure](../angelic-designs/utp_ades_parallel_lifted.thy#L382) |

## Related theories

[utp_ades_parallel_choice.thy](../angelic-designs/utp_ades_parallel_choice.thy)
contains the angelic-choice laws.
[RAD parallel](../reactive-angelic-designs/utp_rad_parallel.thy) and
[AP parallel](../angelic-processes/utp_ap_parallel.thy) provide their own
merge constructors and closure laws. Basic-merge examples involving traces and waiting are
in the [RAD examples](../reactive-angelic-designs/utp_rad_parallel_examples.thy)
and [AP examples](../angelic-processes/utp_ap_parallel_examples.thy).
Correspondence with reactive-design parallel remains to be proved.
