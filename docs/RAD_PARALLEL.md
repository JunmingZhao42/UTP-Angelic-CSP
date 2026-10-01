# Reactive angelic design parallel by merge

[Overview](../PARALLEL.md) · [AD](AD_PARALLEL.md) · [RAD](RAD_PARALLEL.md) · [AP](AP_PARALLEL.md)

[utp_rad_parallel_lifted.thy](../reactive-angelic-designs/utp_rad_parallel_lifted.thy)
defines the sole RAD operator, `rad_par`.

[rad_lift_merge](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L70) takes an ordinary merge `M` on complete reactive
observations, including `ok`, trace, waiting and refusals. Nonempty branch
sets must have a permitted output in the final set for every branch pair.
Write `L(P,M,Q) = P ∥[rad_lift_merge M] Q` for parallel before completion.

### Merge healthiness and closure

[rad_par](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L182) applies RAD afterwards:

```
rad_par P M Q = RAD (L(P,M,Q))
```

| Healthiness | Operand premises | Additional premise | Conclusion | Lemma |
| --- | --- | --- | --- | --- |
| `A2` before completion | `P`, `Q` both `RAD`, `A2` | None | `L(P,M,Q) is A2` | [rad_lift_merge_A2](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L142) |
| `RAD` after completion | None | None | `rad_par P M Q is RAD` | [rad_par_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L188) |
| `A2` after completion | `P`, `Q` both `RAD`, `A2` | None | `rad_par P M Q is A2` | [rad_par_A2](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L212) |
| `RAD` before completion | `P`, `Q` both `RAD`, `A2` | `rad_ac2p P ∥[M] rad_ac2p Q is RD` | `L(P,M,Q) is RAD` | [rad_lift_merge_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L220) |

### rad_ac2p/rad_p2ac mapping laws

`D`, `E` below are ordinary reactive predicates. All laws hold for arbitrary `M`.
`RD` is the flat reactive-design theory using `R3c`; these laws do not concern
the library's stateful `SRD`/`rdes_par` operator.

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| None | `rad_p2ac (D ∥[M] E) = L(rad_p2ac D,M,rad_p2ac E)` | [rad_lift_merge_p2ac](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L125) |
| `P`, `Q` both `RAD`, `A2` | `rad_ac2p L(P,M,Q) = rad_ac2p P ∥[M] rad_ac2p Q` | [rad_lift_merge_ac2p](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L133) |
| None | `rad_par (rad_p2ac D) M (rad_p2ac E) = rad_p2ac (RD (D ∥[M] E))` | [rad_par_p2ac](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L192) |
| `P`, `Q` both `RAD`, `A2` | `rad_par P M Q = rad_p2ac (RD (rad_ac2p P ∥[M] rad_ac2p Q))` | [rad_par_form](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L198) |
| `P`, `Q` both `RAD`, `A2` | `rad_ac2p (rad_par P M Q) = RD (rad_ac2p P ∥[M] rad_ac2p Q)` | [rad_par_ac2p](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L206) |

[rad_p2ac_RD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L171) gives `rad_p2ac (RD D) = RAD (rad_p2ac D)`.
If the mapped ordinary parallel is already RD-healthy, the outer RD disappears
by [rad_par_ac2p_RD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L229). RAD rejects empty final sets, so AD's
`d2ac`/A3 completion cannot be reused here; see [rad_d2ac_not_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L44)
and [A3_not_RAD](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L54).

### Basic merge example

[rad_basic_merge](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L238) requires equal branch/output traces extending
the initial trace, combines waiting by disjunction, leaves refusals unconstrained,
and requires `okL ∧ okR ⇒ okOut`. State constraints still apply on failure.

| Property | Premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| Trace agreement | Lifted merge accepted; `sL ∈ X`, `sR ∈ Y` | `tr(sL) = tr(sR)` | [rad_lift_basic_trace_agreement](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L256) |
| Singleton branches | Both branches and output have `ok = True` | Some `sOut ∈ Z` satisfies `basic_merge_state s0 sL sR sOut` | [rad_lift_basic_singletons](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L266) |
| Initial state | Successful singleton branches/output all contain `s0` | The lifted merge accepts | [rad_lift_basic_same](../reactive-angelic-designs/utp_rad_parallel_lifted.thy#L272) |

Sufficient ordinary merge conditions for raw RD closure remain open.
The basic-merge checks do not discharge that obligation.

### Algebra

| Property | Premises | Law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂` | `rad_par P₁ M Q₁ ⊑ rad_par P₂ M Q₂` | `rad_par_mono` |
| Commutativity | `rad_lift_merge M is SymMerge` | `rad_par P M Q = rad_par Q M P` | `rad_par_comm` |

Associativity needs an ordinary-layer law accounting for RD completion;
state-merge associativity alone is not established as sufficient here.
