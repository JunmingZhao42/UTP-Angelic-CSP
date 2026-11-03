# Reactive angelic design parallel

[Parallel by merge](README.md) · [AD](AD.md) · [AP](AP.md)

Source: [utp_rad_parallel.thy](../../reactive-angelic-designs/utp_rad_parallel.thy).
[Shared notation](README.md#shared-notation).

## Reactive merge lifting

A RAD state is `('t,'e) rad_state = ('t,'e set) rea_vars_ext`, containing
waiting, trace and refusals; the outer design supplies `ok`.
`M` merges complete ordinary reactive observations. Write `obs(ok,s)`
for such an observation. [rad_lift_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L275) defines the lift used by [rad_par](../../reactive-angelic-designs/utp_rad_parallel.thy#L354).

```text
rad_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  acL ≠ {} ∧ acR ≠ {} ∧
  (∀sL∈acL. ∀sR∈acR. ∃s'∈ac'.
     M(obs(ok,s),obs(okL,sL),obs(okR,sR),obs(ok',s')))

P ∥RAD[M] Q ≡ P ∥[rad_lift_merge M] Q
```

[rad_lift_merge_obs](../../reactive-angelic-designs/utp_rad_parallel.thy#L300) gives the evaluation. Unlike the completed D/AD merges,
this lift applies the ordinary merge directly, including its divergence constraints.

## Reactive merge healthiness

[RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L169) combines the ordinary reactive merge conditions:

```text
RADm M = RD1m (R3cm (R2m (RD2 M)))
```

[RD1m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L77) handles unstarted observations; [R2m](../../deps/UTP-Reactive/utp_rea_parallel.thy#L23) removes the initial trace and requires
trace extension; [RD2](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L373) permits termination after divergence at the same remaining
observation; [R3cm](../../reactive-angelic-designs/utp_rad_parallel.thy#L100) supplies reactive skip while waiting.
The components commute and are monotone and idempotent.
[RADm_healthy_iff](../../reactive-angelic-designs/utp_rad_parallel.thy#L196) characterises their common fixed points.

| Merge property | Premise | Lemma |
| --- | --- | --- |
| `RADm M is RADm` | None | [RADm_healthy](../../reactive-angelic-designs/utp_rad_parallel.thy#L180) |
| `rad_lift_merge M is SymMerge` | `M is SymMerge` | [rad_lift_merge_SymMerge](../../reactive-angelic-designs/utp_rad_parallel.thy#L315) |

| Result of `P ∥RAD[M] Q` | Operand premises | Merge premise | Lemma |
| --- | --- | --- | --- |
| [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | Both RAD+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | None | [rad_par_A2](../../reactive-angelic-designs/utp_rad_parallel.thy#L383) |
| [RAD](../../reactive-angelic-designs/utp_rad_designs.thy#L86) | Both RAD+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | `M is RADm` | [rad_par_RAD](../../reactive-angelic-designs/utp_rad_parallel.thy#L402) |

The corresponding ordinary rule is [RD_par_by_RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L241).
Here RD is the flat reactive-design theory using [R3c](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L202).

## ac2p/p2ac mapping laws

| Operand premises | Merge premise | Equality | Lemma |
| --- | --- | --- | --- |
| None | None | `p2ac D ∥RAD[M] p2ac E = p2ac (D ∥[M] E)` | [rad_par_p2ac](../../reactive-angelic-designs/utp_rad_parallel.thy#L361) |
| `P,Q` both RAD and A2 | None | `P ∥RAD[M] Q = p2ac (ac2p P ∥[M] ac2p Q)` | [rad_par_form](../../reactive-angelic-designs/utp_rad_parallel.thy#L371) |
| `P,Q` both RAD and A2 | None | `ac2p (P ∥RAD[M] Q) = ac2p P ∥[M] ac2p Q` | [rad_par_ac2p](../../reactive-angelic-designs/utp_rad_parallel.thy#L378) |

[rad_ac2p_RD](../../reactive-angelic-designs/utp_rad_parallel.thy#L391) maps RAD+A2 to RD;
[rad_p2ac_RD](../../reactive-angelic-designs/utp_rad_parallel.thy#L341) relates RD and RAD healthiness.
RAD rejects empty output sets ([RAD_empty](../../reactive-angelic-designs/utp_rad_parallel.thy#L43)),
so AD's d2ac/A3 completion does not supply RAD closure
([rad_d2ac_not_RAD](../../reactive-angelic-designs/utp_rad_parallel.thy#L48),
[A3_not_RAD](../../reactive-angelic-designs/utp_rad_parallel.thy#L58)).

## Algebraic properties

- [rad_par_mono](../../reactive-angelic-designs/utp_rad_parallel.thy#L411): monotone in both operands.
- [rad_par_comm_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L424): commutative when `M is SymMerge`.
- [rad_par_assoc](../../reactive-angelic-designs/utp_rad_parallel.thy#L450): associative for RAD+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) operands when `M is RADm`,
  `M is SymMerge` and `AssocMerge M`.
- [rad_par_assoc_state](../../reactive-angelic-designs/utp_rad_parallel.thy#L429): alternatively accepts the pointwise two-fold
  associativity equation on `M`.

[RADm_SymMerge](../../reactive-angelic-designs/utp_rad_parallel.thy#L257) preserves symmetry. Preservation of [AssocMerge](../../deps/UTP/utp_concurrency.thy#L213) by [RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L169) is
not proved: associativity must hold for the healthy merge actually supplied.

## Basic merge

[rad_basic_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L459) requires equal branch/output traces extending the prior
trace, combines waiting by disjunction, leaves refusals unconstrained and
requires `okL ∧ okR ⟶ ok'`. Its constraints also apply after divergence.

The seed is not [RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L169)-healthy ([rad_basic_merge_not_RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L510)).
`RADm rad_basic_merge` permits precisely trace extension before start,
copies the prior observation while started and waiting, and agrees with the
seed while running when both branch traces extend the prior trace
([RADm_unstarted](../../reactive-angelic-designs/utp_rad_parallel.thy#L263), [RADm_basic_merge_waiting](../../reactive-angelic-designs/utp_rad_parallel.thy#L539), [RADm_basic_merge_running](../../reactive-angelic-designs/utp_rad_parallel.thy#L531)).

[RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L169) does not remove every output constraint after divergence:
[RADm_post_ref_example](../../reactive-angelic-designs/utp_rad_parallel.thy#L559) retains a final refusal constraint even with
`ok' = False`. This differs from completed RD parallel.

Representation correspondence with the former records is checked in
[utp_rad_representation.thy](../../reactive-angelic-designs/utp_rad_representation.thy).
