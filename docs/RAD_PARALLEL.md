# Reactive angelic design parallel by merge

[Overview](../PARALLEL.md) · [AD](AD_PARALLEL.md) · [RAD](RAD_PARALLEL.md) · [AP](AP_PARALLEL.md)

[utp_rad_parallel.thy](../reactive-angelic-designs/utp_rad_parallel.thy)
defines the sole RAD operator, `rad_par`. The merge transformer `RADm` makes
its final RAD completion redundant for operands healthy under both RAD and A2.

## Common Notations

| Role | Complete observation | Flag | Individual state | Choice set |
| --- | --- | --- | --- | --- |
| Initial | `x` | `ok0` | `s0` | — |
| Left branch | `p` | `okL` | `sL` | `X` |
| Right branch | `q` | `okR` | `sR` | `Y` |
| Merged output | `z` | `okOut` | `sOut` | `Z` |

| Notation | Meaning |
| --- | --- |
| `P`, `Q`, `R` | Reactive angelic predicates |
| `D`, `E` | Ordinary reactive predicates |
| `M :: ('t::trace, 'e set) rp merge`; `M(x,p,q,z)` | Merge on complete observations (`ok`, waiting, trace, refusals); evaluated by `merge_eval` |
| `L(P,M,Q)` | Lifted parallel `P ∥[rad_lift_merge M] Q` |
| `rad_par P M Q` | RAD parallel |
| `M is RADm` | `RADm M = M` |

`RD` is the flat reactive-design theory using `R3c`.

## Lifting reactive merge

[rad_lift_merge](../reactive-angelic-designs/utp_rad_parallel.thy#L276) converts an ordinary merge into a RAD merge. Writing
`obs(ok,s)` for the complete ordinary observation reconstructed by `rad2csp_obs`:

```text
rad_lift_merge M ((ok0,s0),(okL,X),(okR,Y),(okOut,Z))
  iff X ≠ {} ∧ Y ≠ {}
    ∧ (∀sL∈X. ∀sR∈Y. ∃sOut∈Z.
         M(obs(ok0,s0), obs(okL,sL), obs(okR,sR), obs(okOut,sOut)))
```

By [rad_lift_merge_obs](../reactive-angelic-designs/utp_rad_parallel.thy#L301), every branch-state pair needs some permitted output
in `Z`. The merge controls flags, waiting, traces and refusals.

| Property | Premise | Conclusion | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `M ⊑ N` | `rad_lift_merge M ⊑ rad_lift_merge N` | [rad_lift_merge_mono](../reactive-angelic-designs/utp_rad_parallel.thy#L310) |
| Symmetry | `M is SymMerge` | `rad_lift_merge M is SymMerge` | [rad_lift_merge_SymMerge](../reactive-angelic-designs/utp_rad_parallel.thy#L316) |

### Reactive merge healthiness

[RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L170) has type `('t::trace, 'a) rp merge ⇒ ('t, 'a) rp merge`:

```isabelle
RADm M = RD1m (R3cm (R2m (RD2 M)))
```

It reuses the ordinary library's `RD1m`, `R2m` and `RD2`, and adds [R3cm](../reactive-angelic-designs/utp_rad_parallel.thy#L101).
For the RAD lift, instantiate `'a` to `'e set` (the refusal set).

| Component | Effect on the merge |
| --- | --- |
| `RD1m` | Adds every output extending the initial trace when `ok(x)` is false. |
| `R2m` | Requires `tr(x) ≤ tr(z)` and evaluates the merge after removing the initial trace from the branch and output traces, with initial trace zero. |
| `RD2` | Allows a false output `ok` to become true, holding the remaining observation fixed. |
| `R3cm` | When `wait(x)` holds, replaces the merge by `z = x ∨ (¬ok(x) ∧ tr(x) ≤ tr(z))`; otherwise retains it. |

The components are monotone, idempotent and pairwise commuting.

| Property | Law | Lemma |
| --- | --- | --- |
| Idempotence | `RADm (RADm M) = RADm M` | [RADm_idem](../reactive-angelic-designs/utp_rad_parallel.thy#L173) |
| Monotonicity | `M ⊑ N ⟹ RADm M ⊑ RADm N` | [RADm_mono](../reactive-angelic-designs/utp_rad_parallel.thy#L178) |
| Healthy image | `RADm M is RADm` | [RADm_healthy](../reactive-angelic-designs/utp_rad_parallel.thy#L181) |
| Fixed points | `M is RADm ⟷ (M is RD1m ∧ M is R3cm ∧ M is R2m ∧ M is RD2)` | [RADm_healthy_iff](../reactive-angelic-designs/utp_rad_parallel.thy#L197) |
| Ordinary closure | `D is RD ⟹ E is RD ⟹ M is RADm ⟹ (D ∥[M] E) is RD` | [RD_par_by_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L242) |

`RADm` is sufficient; no normality or excluded-output witness is required.
Applying it may change the merge policy.

## Lifted parallel

```text
L(P,M,Q)(ok0,s0,okOut,Z)
  iff ∃okL X okR Y.
       P(ok0,s0,okL,X) ∧ Q(ok0,s0,okR,Y)
     ∧ rad_lift_merge M ((ok0,s0),(okL,X),(okR,Y),(okOut,Z))
```

The outer existential chooses accepted branch outputs; the merge then checks
every pair of states inside their choice sets.

| Healthiness | Operand premises | Merge premise | Conclusion | Lemma |
| --- | --- | --- | --- | --- |
| `A2` | `P`, `Q` both RAD and A2 | None | `L(P,M,Q) is A2` | [rad_par_raw_A2](../reactive-angelic-designs/utp_rad_parallel.thy#L355) |
| `RAD` | `P`, `Q` both RAD and A2 | `M is RADm` | `L(P,M,Q) is RAD` | [rad_par_raw_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L474) |

## RAD parallel by merge

[rad_par](../reactive-angelic-designs/utp_rad_parallel.thy#L400) defines:

```isabelle
rad_par P M Q = RAD (L(P,M,Q))
```

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `RAD` | None | `rad_par P M Q is RAD` | [rad_par_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L406) |
| `A2` | `P`, `Q` both RAD and A2 | `rad_par P M Q is A2` | [rad_par_A2](../reactive-angelic-designs/utp_rad_parallel.thy#L430) |

## `rad_ac2p`/`rad_p2ac` mapping laws

For arbitrary `M`:

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| None | `rad_p2ac (D ∥[M] E) = L(rad_p2ac D,M,rad_p2ac E)` | [rad_par_raw_p2ac](../reactive-angelic-designs/utp_rad_parallel.thy#L326) |
| `P`, `Q` both RAD and A2 | `rad_ac2p (L(P,M,Q)) = rad_ac2p P ∥[M] rad_ac2p Q` | [rad_par_raw_ac2p](../reactive-angelic-designs/utp_rad_parallel.thy#L366) |
| None | `rad_par (rad_p2ac D) M (rad_p2ac E) = rad_p2ac (RD (D ∥[M] E))` | [rad_par_p2ac](../reactive-angelic-designs/utp_rad_parallel.thy#L410) |
| `P`, `Q` both RAD and A2 | `rad_par P M Q = rad_p2ac (RD (rad_ac2p P ∥[M] rad_ac2p Q))` | [rad_par_form](../reactive-angelic-designs/utp_rad_parallel.thy#L416) |
| `P`, `Q` both RAD and A2 | `rad_ac2p (rad_par P M Q) = RD (rad_ac2p P ∥[M] rad_ac2p Q)` | [rad_par_ac2p](../reactive-angelic-designs/utp_rad_parallel.thy#L424) |

When **`M is RADm`**, the RD completion disappears:

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `D`, `E` both RD | `rad_par (rad_p2ac D) M (rad_p2ac E) = rad_p2ac (D ∥[M] E)` | [rad_par_p2ac_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L503) |
| `P`, `Q` both RAD and A2 | `rad_par P M Q = rad_p2ac (rad_ac2p P ∥[M] rad_ac2p Q)` | [rad_par_form_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L496) |
| `P`, `Q` both RAD and A2 | `rad_ac2p (rad_par P M Q) = rad_ac2p P ∥[M] rad_ac2p Q` | [rad_par_ac2p_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L490) |

| Healthiness bridge | Premises | Lemma |
| --- | --- | --- |
| `rad_p2ac (RD D) = RAD (rad_p2ac D)` | None | [rad_p2ac_RD](../reactive-angelic-designs/utp_rad_parallel.thy#L389) |
| `rad_ac2p P is RD` | `P` both RAD and A2 | [rad_ac2p_RD](../reactive-angelic-designs/utp_rad_parallel.thy#L463) |

RAD rejects empty final sets ([RAD_empty](../reactive-angelic-designs/utp_rad_parallel.thy#L44)), so AD's `d2ac` and A3 completion
cannot be reused ([rad_d2ac_not_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L49), [A3_not_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L59)).

## Algebraic properties

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂` | `rad_par P₁ M Q₁ ⊑ rad_par P₂ M Q₂` | [rad_par_mono](../reactive-angelic-designs/utp_rad_parallel.thy#L510) |
| Commutativity | `M is SymMerge` | `rad_par P M Q = rad_par Q M P` | [rad_par_comm_merge](../reactive-angelic-designs/utp_rad_parallel.thy#L524) |
| Associativity | `P`, `Q`, `R` all RAD and A2; `M is RADm`, `M is SymMerge`, `AssocMerge M` | `rad_par (rad_par P M Q) M R = rad_par P M (rad_par Q M R)` | [rad_par_assoc](../reactive-angelic-designs/utp_rad_parallel.thy#L550) |
| Symmetry preservation | `M is SymMerge` | `RADm M is SymMerge` | [RADm_SymMerge](../reactive-angelic-designs/utp_rad_parallel.thy#L258) |

Associativity must hold for the healthy merge; preservation by `RADm` is not
proved. [rad_par_assoc_state](../reactive-angelic-designs/utp_rad_parallel.thy#L529) alternatively takes the pointwise condition:

```text
(∃u. M(x,p,q,u) ∧ M(x,u,r,z)) = (∃u. M(x,q,r,u) ∧ M(x,p,u,z)).
```

## RAD closure without completion

Assume `P`, `Q` are both RAD and A2. All equalities use the same merge on both sides.

| Merge premise | Equality | Lemma |
| --- | --- | --- |
| `M is RADm` | `rad_par P M Q = L(P,M,Q)` | [rad_par_eq_raw](../reactive-angelic-designs/utp_rad_parallel.thy#L480) |
| None | `rad_par P (RADm M) Q = L(P,RADm M,Q)` | [rad_par_RADm_eq_raw](../reactive-angelic-designs/utp_rad_parallel.thy#L485) |

Alternatively, [rad_par_raw_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L439) gives raw RAD closure whenever
`rad_ac2p P ∥[M] rad_ac2p Q is RD` is established separately.

## Basic merge example

[rad_basic_merge](../reactive-angelic-designs/utp_rad_parallel.thy#L559) requires equal branch/output traces extending the initial
trace, combines waiting by disjunction, leaves refusals unconstrained, and
requires `okL ∧ okR ⇒ okOut`. Its state constraints also apply on failure.
The original trace-agreement and singleton laws remain available as
[rad_lift_basic_trace_agreement](../reactive-angelic-designs/utp_rad_parallel.thy#L577), [rad_lift_basic_singletons](../reactive-angelic-designs/utp_rad_parallel.thy#L587) and [rad_lift_basic_same](../reactive-angelic-designs/utp_rad_parallel.thy#L593).

The seed is **not** RADm-healthy ([rad_basic_merge_not_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L611)).
Use `RADm rad_basic_merge` to obtain a healthy merge:

| Initial observation | Behaviour of the transformed merge | Lemma |
| --- | --- | --- |
| `¬ok(x)` | Exactly `tr(x) ≤ tr(z)` | [RADm_unstarted](../reactive-angelic-designs/utp_rad_parallel.thy#L264) |
| `ok(x) ∧ wait(x)` | Exactly `z = x`, including refusals | [RADm_basic_merge_waiting](../reactive-angelic-designs/utp_rad_parallel.thy#L641) |
| `ok(x) ∧ ¬wait(x)`; both branch traces extend `tr(x)` | Same as the original basic merge | [RADm_basic_merge_running](../reactive-angelic-designs/utp_rad_parallel.thy#L633) |

The branch-prefix premises hold for outputs of R1-healthy operands.
The seed is RD2-healthy ([rad_basic_merge_RD2](../reactive-angelic-designs/utp_rad_parallel.thy#L621)); [rad_basic_merge_R2m](../reactive-angelic-designs/utp_rad_parallel.thy#L625)
proves only a conditional evaluation equality.

### Post-state-dependent failure

Take `D = RD true` and the healthy merge
`M = RADm (λ(m,out). rea_vars.more out = {})`, which constrains the final refusal set.
For `ok(x) ∧ ¬wait(x)`, [RADm_post_ref_example](../reactive-angelic-designs/utp_rad_parallel.thy#L661) proves:

```text
(D ∥[M] D)(x,z) iff tr(x) ≤ tr(z) ∧ ref(z) = {}.
```

The equation also holds at `ok(z) = False`: the failure slice, and hence its
negation as an assumption, depends on final refusals. The raw `rad_p2ac` law
transfers this example to RAD and A2 operands.
