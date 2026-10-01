# Angelic design parallel by merge

[Overview](../PARALLEL.md) · [AD](AD_PARALLEL.md) · [RAD](RAD_PARALLEL.md) · [AP](AP_PARALLEL.md)

[utp_ades_parallel_lifted.thy](../angelic-designs/utp_ades_parallel_lifted.thy)
defines the sole AD operator, `ades_par`, written `P ∥AD³[j] Q`.
Write `L(P,j,Q) = P ∥[lift_merge j] Q` for its internal parallel before A3.
`D ∥D[j] E` is ordinary-design parallel.

### From state merges to choice sets

[lift_merge](../angelic-designs/utp_ades_parallel_lifted.thy#L47) uses `j`
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

For fixed branch observations, the lifted merge is A0- and A1-healthy
(`lift_merge_slice_A0`, `lift_merge_slice_A1`). A2 closure follows from the
operands; it does not require an A2-healthy merge.

[ades_par](../angelic-designs/utp_ades_parallel_lifted.thy#L181) applies A3 after parallel:

```
P ∥AD³[j] Q = A3 (L(P,j,Q))
```

For H1-healthy operands, completion [only changes empty final sets](../angelic-designs/utp_ades_parallel_lifted.thy),
admitting them when every singleton permits failure. The closure laws below
need no condition on `j`, no H3 premise, and no additional merge-healthiness premise.

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `A` after completion | `P is H1`, `Q is H1` | `(P ∥AD³[j] Q) is A` | [ades_par_A_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L193) |
| `A2` after completion | `P`, `Q` both `A`, `A2` | `(P ∥AD³[j] Q) is A2` | [ades_par_A2_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L199) |
| `A3` after completion | None | `(P ∥AD³[j] Q) is A3` | [ades_par_A3_closure](../angelic-designs/utp_ades_parallel_lifted.thy#L205) |

### ac2p/d2ac mapping laws

`ac2p` maps angelic designs to ordinary designs; `d2ac` maps back.
All three laws hold for any state merge `j`.

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `P`, `Q` both `A`, `A2` | `ac2p (P ∥AD³[j] Q) = ac2p P ∥D[j] ac2p Q` | [ades_par_ac2p](../angelic-designs/utp_ades_parallel_lifted.thy#L258) |
| `D`, `E` both `H` | `d2ac D ∥AD³[j] d2ac E = d2ac (D ∥D[j] E)` | [ades_par_d2ac](../angelic-designs/utp_ades_parallel_lifted.thy#L251) |
| `P`, `Q` both `A`, `A2` | `P ∥AD³[j] Q = d2ac (ac2p P ∥D[j] ac2p Q)` | [ades_par_d2ac_ac2p](../angelic-designs/utp_ades_parallel_lifted.thy#L232) |

### Algebra

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂` | `(P₁ ∥AD³[j] Q₁) ⊑ (P₂ ∥AD³[j] Q₂)` | [ades_par_mono](../angelic-designs/utp_ades_parallel_lifted.thy#L270) |
| Commutativity | `lift_merge j is SymMerge` | `P ∥AD³[j] Q = Q ∥AD³[j] P` | [ades_par_comm](../angelic-designs/utp_ades_parallel_lifted.thy#L277) |
| Associativity | `P`, `Q`, `R` all `A`, `A2`; state associativity below | `(P ∥AD³[j] Q) ∥AD³[j] R = P ∥AD³[j] (Q ∥AD³[j] R)` | [ades_par_assoc](../angelic-designs/utp_ades_parallel_lifted.thy#L289) |

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
| Merge observation | None | `¬ok0 ∨ (X ≠ {} ∧ Y ≠ {} ∧ (okL ∧ okR ⇒ okOut) ∧ s0 ∈ Z)` | [lift_merge_skip_eval](../angelic-designs/utp_ades_parallel_lifted.thy#L328) |
| Merge symmetry | None | `lift_merge skipₘ is SymMerge` | [lift_merge_skip_SymMerge](../angelic-designs/utp_ades_parallel_lifted.thy#L337) |
| Completed associativity | `P`, `Q`, `R` all `A`, `A2` | `(P ∥AD³[skipₘ] Q) ∥AD³[skipₘ] R = P ∥AD³[skipₘ] (Q ∥AD³[skipₘ] R)` | [ades_par_skip_assoc](../angelic-designs/utp_ades_parallel_lifted.thy#L317) |

The examples use [ades_bool_choice](../angelic-designs/utp_ades_parallel_lifted.thy#L340),
a design that terminates and requires its chosen Boolean to be in the
result set. It is both [A-healthy](../angelic-designs/utp_ades_parallel_lifted.thy)
and [A2-healthy](../angelic-designs/utp_ades_parallel_lifted.thy).

| Completed skip example | Behaviour when started | Lemma |
| --- | --- | --- |
| Two successful Boolean choices | `okOut ∧ s0 ∈ Z` | [skip_completed_success](../angelic-designs/utp_ades_parallel_lifted.thy#L365) |
| Chaos and a successful Boolean choice | `s0 ∈ Z`; termination is unconstrained | [skip_completed_failure](../angelic-designs/utp_ades_parallel_lifted.thy#L376) |
