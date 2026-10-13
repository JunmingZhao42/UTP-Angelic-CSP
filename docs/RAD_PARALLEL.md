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

| Representation | Type or equation |
| --- | --- |
| Individual reactive state | `('t, 'e) rad_state = ('t, 'e set) rea_vars_ext` |
| Fields of each state | `wait`, `tr`, `more` (the refusal set) |
| RAD | `('t, 'e) rad_state angelic_design` |
| Direct mappings | `p2ac`, `ac2p`, `d2ac` |

The outer design supplies `ok`; each member of the final choice set has its own
refusal set. The [representation audit](../reactive-angelic-designs/utp_rad_representation.thy)
proves that the direct mappings and raw parallel agree with the former record
representation under the state bijection.

## Lifting reactive merge

[rad_lift_merge](../reactive-angelic-designs/utp_rad_parallel.thy#L276) converts an ordinary merge into a RAD merge. Writing
`obs(ok,s) = ⦇okᵥ = ok, … = s⦈` for the complete ordinary observation:

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
| `A2` | `P`, `Q` both RAD and A2 | None | `L(P,M,Q) is A2` | [rad_par_raw_A2](../reactive-angelic-designs/utp_rad_parallel.thy#L336) |
| `RAD` | `P`, `Q` both RAD and A2 | `M is RADm` | `L(P,M,Q) is RAD` | [rad_par_raw_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L455) |

## RAD parallel by merge

[rad_par](../reactive-angelic-designs/utp_rad_parallel.thy#L381) defines:

```isabelle
rad_par P M Q = RAD (L(P,M,Q))
```

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `RAD` | None | `rad_par P M Q is RAD` | [rad_par_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L387) |
| `A2` | `P`, `Q` both RAD and A2 | `rad_par P M Q is A2` | [rad_par_A2](../reactive-angelic-designs/utp_rad_parallel.thy#L411) |

## `ac2p`/`p2ac` mapping laws

For arbitrary `M`:

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| None | `p2ac (D ∥[M] E) = L(p2ac D,M,p2ac E)` | [rad_par_raw_p2ac](../reactive-angelic-designs/utp_rad_parallel.thy#L326) |
| `P`, `Q` both RAD and A2 | `ac2p (L(P,M,Q)) = ac2p P ∥[M] ac2p Q` | [rad_par_raw_ac2p](../reactive-angelic-designs/utp_rad_parallel.thy#L347) |
| None | `rad_par (p2ac D) M (p2ac E) = p2ac (RD (D ∥[M] E))` | [rad_par_p2ac](../reactive-angelic-designs/utp_rad_parallel.thy#L391) |
| `P`, `Q` both RAD and A2 | `rad_par P M Q = p2ac (RD (ac2p P ∥[M] ac2p Q))` | [rad_par_form](../reactive-angelic-designs/utp_rad_parallel.thy#L397) |
| `P`, `Q` both RAD and A2 | `ac2p (rad_par P M Q) = RD (ac2p P ∥[M] ac2p Q)` | [rad_par_ac2p](../reactive-angelic-designs/utp_rad_parallel.thy#L405) |

When **`M is RADm`**, the RD completion disappears:

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| `D`, `E` both RD | `rad_par (p2ac D) M (p2ac E) = p2ac (D ∥[M] E)` | [rad_par_p2ac_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L484) |
| `P`, `Q` both RAD and A2 | `rad_par P M Q = p2ac (ac2p P ∥[M] ac2p Q)` | [rad_par_form_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L477) |
| `P`, `Q` both RAD and A2 | `ac2p (rad_par P M Q) = ac2p P ∥[M] ac2p Q` | [rad_par_ac2p_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L471) |

| Healthiness bridge | Premises | Lemma |
| --- | --- | --- |
| `p2ac (RD D) = RAD (p2ac D)` | None | [rad_p2ac_RD](../reactive-angelic-designs/utp_rad_parallel.thy#L370) |
| `ac2p P is RD` | `P` both RAD and A2 | [rad_ac2p_RD](../reactive-angelic-designs/utp_rad_parallel.thy#L444) |

RAD rejects empty final sets ([RAD_empty](../reactive-angelic-designs/utp_rad_parallel.thy#L44)), so AD's `d2ac` and A3 completion
cannot be reused ([rad_d2ac_not_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L49), [A3_not_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L59)).

## Algebraic properties

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂` | `rad_par P₁ M Q₁ ⊑ rad_par P₂ M Q₂` | [rad_par_mono](../reactive-angelic-designs/utp_rad_parallel.thy#L491) |
| Commutativity | `M is SymMerge` | `rad_par P M Q = rad_par Q M P` | [rad_par_comm_merge](../reactive-angelic-designs/utp_rad_parallel.thy#L505) |
| Associativity | `P`, `Q`, `R` all RAD and A2; `M is RADm`, `M is SymMerge`, `AssocMerge M` | `rad_par (rad_par P M Q) M R = rad_par P M (rad_par Q M R)` | [rad_par_assoc](../reactive-angelic-designs/utp_rad_parallel.thy#L531) |
| Symmetry preservation | `M is SymMerge` | `RADm M is SymMerge` | [RADm_SymMerge](../reactive-angelic-designs/utp_rad_parallel.thy#L258) |

Associativity must hold for the healthy merge; preservation by `RADm` is not
proved. [rad_par_assoc_state](../reactive-angelic-designs/utp_rad_parallel.thy#L510) alternatively takes the pointwise condition:

```text
(∃u. M(x,p,q,u) ∧ M(x,u,r,z)) = (∃u. M(x,q,r,u) ∧ M(x,p,u,z)).
```

## RAD closure without completion

Assume `P`, `Q` are both RAD and A2. All equalities use the same merge on both sides.

| Merge premise | Equality | Lemma |
| --- | --- | --- |
| `M is RADm` | `rad_par P M Q = L(P,M,Q)` | [rad_par_eq_raw](../reactive-angelic-designs/utp_rad_parallel.thy#L461) |
| None | `rad_par P (RADm M) Q = L(P,RADm M,Q)` | [rad_par_RADm_eq_raw](../reactive-angelic-designs/utp_rad_parallel.thy#L466) |

Alternatively, [rad_par_raw_RAD](../reactive-angelic-designs/utp_rad_parallel.thy#L420) gives raw RAD closure whenever
`ac2p P ∥[M] ac2p Q is RD` is established separately.

## Basic merge example

[rad_basic_merge](../reactive-angelic-designs/utp_rad_parallel.thy#L540) requires equal branch/output traces extending the initial
trace, combines waiting by disjunction, leaves refusals unconstrained, and
requires `okL ∧ okR ⇒ okOut`. Its state constraints also apply on failure.
The original trace-agreement and singleton laws remain available as
[rad_lift_basic_trace_agreement](../reactive-angelic-designs/utp_rad_parallel.thy#L557), [rad_lift_basic_singletons](../reactive-angelic-designs/utp_rad_parallel.thy#L567) and [rad_lift_basic_same](../reactive-angelic-designs/utp_rad_parallel.thy#L573).

The seed is **not** RADm-healthy ([rad_basic_merge_not_RADm](../reactive-angelic-designs/utp_rad_parallel.thy#L591)).
Use `RADm rad_basic_merge` to obtain a healthy merge:

| Initial observation | Behaviour of the transformed merge | Lemma |
| --- | --- | --- |
| `¬ok(x)` | Exactly `tr(x) ≤ tr(z)` | [RADm_unstarted](../reactive-angelic-designs/utp_rad_parallel.thy#L264) |
| `ok(x) ∧ wait(x)` | Exactly `z = x`, including refusals | [RADm_basic_merge_waiting](../reactive-angelic-designs/utp_rad_parallel.thy#L620) |
| `ok(x) ∧ ¬wait(x)`; both branch traces extend `tr(x)` | Same as the original basic merge | [RADm_basic_merge_running](../reactive-angelic-designs/utp_rad_parallel.thy#L612) |

The branch-prefix premises hold for outputs of R1-healthy operands.
The seed is RD2-healthy ([rad_basic_merge_RD2](../reactive-angelic-designs/utp_rad_parallel.thy#L601)); [rad_basic_merge_R2m](../reactive-angelic-designs/utp_rad_parallel.thy#L604)
proves only a conditional evaluation equality.

### Post-state-dependent failure

Take `D = RD true` and the healthy merge
`M = RADm (λ(m,out). rea_vars.more out = {})`, which constrains the final refusal set.
For `ok(x) ∧ ¬wait(x)`, [RADm_post_ref_example](../reactive-angelic-designs/utp_rad_parallel.thy#L640) proves:

```text
(D ∥[M] D)(x,z) iff tr(x) ≤ tr(z) ∧ ref(z) = {}.
```

The equation also holds at `ok(z) = False`: the failure slice, and hence its
negation as an assumption, depends on final refusals. The raw `p2ac` law
transfers this example to RAD and A2 operands.
