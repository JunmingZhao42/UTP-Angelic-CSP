# Reactive angelic design parallel by merge

[Overview](../PARALLEL.md) · [AD](AD_PARALLEL.md) · [RAD](RAD_PARALLEL.md) · [AP](AP_PARALLEL.md)

| Theory | Purpose |
| --- | --- |
| [utp_rad_parallel.thy](../reactive-angelic-designs/utp_rad_parallel.thy) | Generic parallel with `RADOKM` merge healthiness. |
| [utp_rad_parallel_lifted.thy](../reactive-angelic-designs/utp_rad_parallel_lifted.thy) | Ordinary reactive merge lifting and `rad_ac2p`/`rad_p2ac` mapping laws. |

## 1. Generic parallel

[rad_par](../reactive-angelic-designs/utp_rad_parallel.thy#L496) uses the completed merge: `rad_par P N Q = P ∥[RADOKM N] Q`.
[RADOKM](../reactive-angelic-designs/utp_rad_parallel.thy#L404) is [monotonic](../reactive-angelic-designs/utp_rad_parallel.thy#L422) and [idempotent](../reactive-angelic-designs/utp_rad_parallel.thy#L429).
Here `N` is a merge on angelic observations.

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `RAD` | `P`, `Q` both `RAD` | `rad_par P N Q is RAD` | [rad_par_RAD_closure](../reactive-angelic-designs/utp_rad_parallel.thy#L652) |
| `RA2` | `P`, `Q` both `RA2` | `rad_par P N Q is RA2` | [rad_par_RA2_closure](../reactive-angelic-designs/utp_rad_parallel.thy#L555) |

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂`, `N₁ ⊑ N₂` | `rad_par P₁ N₁ Q₁ ⊑ rad_par P₂ N₂ Q₂` | [rad_par_mono](../reactive-angelic-designs/utp_rad_parallel.thy#L680) |
| Commutativity | `N is SymMerge` | `rad_par P N Q = rad_par Q N P` | [rad_par_comm](../reactive-angelic-designs/utp_rad_parallel.thy#L686) |
| Associativity | `RADOKM N is SymMerge`, `AssocMerge (RADOKM N)` | `rad_par (rad_par P N Q) N R = rad_par P N (rad_par Q N R)` | [rad_par_assoc](../reactive-angelic-designs/utp_rad_parallel.thy#L695) |

## 2. Lifting ordinary reactive merges

[rad_lift_merge](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L44) takes an ordinary merge `M` on complete reactive
observations, including `ok`, trace, waiting and refusals. Nonempty branch
sets must have a permitted output in the final set for every branch pair.
Write `L(P,M,Q) = P ∥AD[rad_lift_merge M] Q` for parallel before completion.

### Merge healthiness and closure

[rad_par_lifted](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L156) applies RAD afterwards:

```
rad_par_lifted P M Q = RAD (L(P,M,Q))
```

| Healthiness | Operand premises | Additional premise | Conclusion | Lemma |
| --- | --- | --- | --- | --- |
| `A2` before completion | `P`, `Q` both `RAD`, `A2` | None | `L(P,M,Q) is A2` | [rad_lift_merge_A2](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L116) |
| `RAD` after completion | None | None | `rad_par_lifted P M Q is RAD` | [rad_par_lifted_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L162) |
| `A2` after completion | `P`, `Q` both `RAD`, `A2` | None | `rad_par_lifted P M Q is A2` | [rad_par_lifted_A2](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L186) |
| `RAD` before completion | `P`, `Q` both `RAD`, `A2` | `rad_ac2p P ∥[M] rad_ac2p Q is RD` | `L(P,M,Q) is RAD` | [rad_lift_merge_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L246) |

[rad_lower_merge](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L197) restricts to singleton observations and recovers
`M` after lifting. The operator `rad_lift_health H = rad_lift_merge ∘ H ∘ rad_lower_merge`
inherits [rad_lift_health_idem](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L230) and [rad_lift_health_mono](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L235)
from `H`. These facts alone do not establish RAD closure or equivalence with `RADOKM`.

### rad_ac2p/rad_p2ac mapping laws

`D`, `E` below are ordinary reactive predicates. All laws hold for arbitrary `M`.
`RD` is the flat reactive-design theory using `R3c`; these laws do not concern
the library's stateful `SRD`/`rdes_par` operator.

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| None | `rad_p2ac (D ∥[M] E) = L(rad_p2ac D,M,rad_p2ac E)` | [rad_lift_merge_p2ac](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L99) |
| `P`, `Q` both `RAD`, `A2` | `rad_ac2p L(P,M,Q) = rad_ac2p P ∥[M] rad_ac2p Q` | [rad_lift_merge_ac2p](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L107) |
| None | `rad_par_lifted (rad_p2ac D) M (rad_p2ac E) = rad_p2ac (RD (D ∥[M] E))` | [rad_par_lifted_p2ac](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L166) |
| `P`, `Q` both `RAD`, `A2` | `rad_par_lifted P M Q = rad_p2ac (RD (rad_ac2p P ∥[M] rad_ac2p Q))` | [rad_par_lifted_form](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L172) |
| `P`, `Q` both `RAD`, `A2` | `rad_ac2p (rad_par_lifted P M Q) = RD (rad_ac2p P ∥[M] rad_ac2p Q)` | [rad_par_lifted_ac2p](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L180) |

[rad_p2ac_RD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L145) gives `rad_p2ac (RD D) = RAD (rad_p2ac D)`.
If the mapped ordinary parallel is already RD-healthy, the outer RD disappears
by [rad_par_lifted_ac2p_RD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L255). RAD rejects empty final sets, so AD's
`d2ac`/A3 completion cannot be reused here; see [rad_d2ac_not_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L18)
and [A3_not_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L28).

### Basic merge example

[rad_basic_merge](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L288) requires equal branch/output traces extending
the initial trace, combines waiting by disjunction, leaves refusals unconstrained,
and requires `okL ∧ okR ⇒ okOut`. State constraints still apply on failure.

| Property | Premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| Trace agreement | Lifted merge accepted; `sL ∈ X`, `sR ∈ Y` | `tr(sL) = tr(sR)` | [rad_lift_basic_trace_agreement](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L306) |
| Singleton branches | Both branches and output have `ok = True` | Some `sOut ∈ Z` satisfies `basic_merge_state s0 sL sR sOut` | [rad_lift_basic_singletons](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L316) |
| Initial state | Successful singleton branches/output all contain `s0` | The lifted merge accepts | [rad_lift_basic_same](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L322) |

Sufficient ordinary merge conditions for RD closure, and their relationship
to `RADOKM`, remain open. The basic-merge checks do not discharge that obligation.
