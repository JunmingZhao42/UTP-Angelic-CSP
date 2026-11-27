# Shared choice-set canonicity

[Parallel by merge](README.md) · [AD](AD.md) · [RAD](RAD.md) · [AP](AP.md)

Source files:

- [`utp_ades_parallel_choice_lift.thy`](../../angelic-designs/utp_ades_parallel_choice_lift.thy)
- [`utp_ades_parallel_operator.thy`](../../angelic-designs/utp_ades_parallel_operator.thy)
- [`utp_rad_parallel_operator.thy`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy)

[Shared notation](README.md#shared-notation).

These results concern the [choice-set lift](AD.md#the-lifted-merge)
of an ordinary merge `N`, written `L(N) = ac'_lift_merge N`. They use the shared
choice-set alphabet, not AD healthiness. [RAD](#rad) specialises the same lift;
for AP, canonicity is [open](AP.md#not-covered).

- [The shared lift](#the-shared-lift)
- [RAD](#rad)

## The shared lift

Canonicity shows that the lift is not an arbitrary way to extend an ordinary merge
to choice sets. We compare the lift with other merges `M` on choice sets. We admit
`M` when accepting larger branch sets means accepting smaller nonempty ones too,
since a smaller branch set is a stronger guarantee from that branch. `ABm` states
this condition:

```isabelle
branch_step ≡ acL ≠ {} ∧ acR ≠ {} ∧ acL ⊆ acL' ∧ acR ⊆ acR' ∧
  (ok,s,okL,okR)' = (ok,s,okL,okR)
ABm M ≡ branch_step ;; M
```

- [`branch_step`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L81) is a step on merge inputs, with primes for the step's after-state.
  The step enlarges nonempty branch choice sets, as `pbmh_step` enlarges the output set,
  and leaves the prior and branch flags unchanged. So an `ABm` merge that accepts
  larger branch sets also accepts smaller nonempty ones.
- Shrinking a branch set keeps the lift true while the set stays nonempty, so the
  lift is itself `ABm` ([`ac'_lift_merge_ABm`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L130)). No construction applies `ABm`;
  `ABm` only admits the merges we compare with.

[`singleton_refines`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L141) requires every accepted singleton branch pair to have an
`N` witness in `ac'`, for every prior, all control flags and every output set.

| Result | Premises | Lemma |
| --- | --- | --- |
| On singleton branches, `L(N)` accepts iff `N` has a witness in `ac'` | None | [`choice_lift_singleton`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L152) |
| `L(N) ⊑ M` iff `singleton_refines N M` | `M is ABm` | [`choice_lift_refine_iff`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L186) |
| `P ∥[L(N)] Q ⊑ P ∥[M] Q` | `M is ABm`, `singleton_refines N M` | [`par_choice_lift_canonical`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L201) |
| `P ∥AD[j] Q ⊑ P ∥[H3m (H1m M)] Q` | `M is ABm`, `singleton_refines (merge_des j) M` | [`ades_par_canonical`](../../angelic-designs/utp_ades_parallel_operator.thy#L129) |

- Among `ABm` merges `M` with `singleton_refines N M`, `L(N)` is the least in the
  refinement order. No A2 premise is needed. Since the lift is itself `ABm`, it is
  the least admissible merge.
- Refinement only removes behaviours, so what `P ∥AD[j] Q` cannot do, no admissible
  alternative can do either.
- The last row accounts for AD's additional `H1m` and `H3m` completion.

## RAD

[`merge_rad`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L35) `j` is the shared lift `L(N)` at `N = merge_rdes j`, so the
results above specialise directly to RAD's trace, waiting and refusal alphabet:

| Result | Merge premises | Lemma |
| --- | --- | --- |
| `P ∥RAD[j] Q ⊑ P ∥[M] Q` | `M is ABm`, `singleton_refines (merge_rdes j) M` | [`rad_par_canonical`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L115) |

- No operand healthiness or A2 premise is needed.
- The comparison premises do not assert RAD closure of parallel with the arbitrary
  merge `M`.
