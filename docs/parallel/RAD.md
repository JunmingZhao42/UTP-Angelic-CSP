# Reactive angelic design parallel

[Parallel by merge](README.md) · [AD](AD.md) · [AP](AP.md)

Source: [utp_rad_parallel.thy](../../reactive-angelic-designs/utp_rad_parallel.thy).
[Shared notation](README.md#shared-notation).

## Reactive merge lifting

A RAD state is `('t,'e) rad_state = ('t,'e set) rea_vars_ext`, containing
waiting, trace and refusals; the outer design supplies `ok`.
`M` merges complete ordinary reactive observations. Write `obs(ok,s)`
for such an observation. [rad_lift_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L34) defines the lift used by [rad_par](../../reactive-angelic-designs/utp_rad_parallel.thy#L78).

```text
rad_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  acL ≠ {} ∧ acR ≠ {} ∧
  (∀sL∈acL. ∀sR∈acR. ∃s'∈ac'.
     M(obs(ok,s),obs(okL,sL),obs(okR,sR),obs(ok',s')))

P ∥RAD[M] Q ≡ P ∥[rad_lift_merge M] Q
```

[merge_rad](../../reactive-angelic-designs/utp_rad_parallel.thy#L255) names the
instance `rad_lift_merge (merge_rdes j)` for
`j :: ('t × 'e set) merge`. The generic lift and parallel operator accept
any ordinary merge `M`.

[rad_lift_merge_obs](../../reactive-angelic-designs/utp_rad_parallel.thy#L53) gives the evaluation. Unlike the completed D/AD merges,
this lift applies the ordinary merge directly, including its divergence constraints.

## Reactive merge healthiness

[ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L27) combines the ordinary reactive merge conditions:

```text
ORDm ≡ RD1m ∘ R3cm ∘ R2m ∘ RD2
```

[RD1m](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L77) handles unstarted observations; [R2m](../../deps/UTP-Reactive/utp_rea_parallel.thy#L23) removes the initial trace and requires
trace extension; [RD2](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L373) permits termination after divergence at the same remaining
observation; [R3cm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L24) supplies reactive skip while waiting.
The components commute and are monotone and idempotent.
[ORDm_healthy_iff](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L113) characterises their common fixed points.

| Merge property | Premise | Lemma |
| --- | --- | --- |
| `ORDm M is ORDm` | None | [ORDm_healthy](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L95) |
| `rad_lift_merge M is SymMerge` | `M is SymMerge` | [rad_lift_merge_SymMerge](../../reactive-angelic-designs/utp_rad_parallel.thy#L66) |

| Result of `P ∥RAD[M] Q` | Operand premises | Merge premise | Lemma |
| --- | --- | --- | --- |
| [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | Both RAD+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | None | [rad_par_A2](../../reactive-angelic-designs/utp_rad_parallel.thy#L115) |
| [RAD](../../reactive-angelic-designs/utp_rad_designs.thy#L92) | Both RAD+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | `M is ORDm` | [rad_par_RAD](../../reactive-angelic-designs/utp_rad_parallel.thy#L127) |

The corresponding ordinary rule is [RD_par_by_ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L399).
Here RD is the flat reactive-design theory using [R3c](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L202).

## ac2p/p2ac mapping laws

| Operand premises | Merge premise | Equality | Lemma |
| --- | --- | --- | --- |
| None | None | `p2ac D ∥RAD[M] p2ac E = p2ac (D ∥[M] E)` | [rad_par_p2ac](../../reactive-angelic-designs/utp_rad_parallel.thy#L85) |
| None | None | `p2ac D ∥[merge_rad j] p2ac E = p2ac (D ∥RD[j] E)` | [merge_rad_p2ac](../../reactive-angelic-designs/utp_rad_parallel.thy#L258) |
| `P,Q` both RAD and A2 | None | `P ∥RAD[M] Q = p2ac (ac2p P ∥[M] ac2p Q)` | [rad_par_form](../../reactive-angelic-designs/utp_rad_parallel.thy#L95) |
| `P,Q` both RAD and A2 | None | `ac2p (P ∥RAD[M] Q) = ac2p P ∥[M] ac2p Q` | [rad_par_ac2p](../../reactive-angelic-designs/utp_rad_parallel.thy#L106) |

[rad_ac2p_RD](../../reactive-angelic-designs/utp_rad_csp.thy#L421) maps RAD+A2 to RD;
[rad_p2ac_RD](../../reactive-angelic-designs/utp_rad_csp.thy#L407) relates RD and RAD healthiness.
RAD rejects empty output sets ([RAD_empty](../../reactive-angelic-designs/utp_rad_designs.thy#L269)),
so AD's d2ac/A3 completion does not supply RAD closure
([rad_d2ac_not_RAD](../../reactive-angelic-designs/utp_rad_designs.thy#L277),
[A3_not_RAD](../../reactive-angelic-designs/utp_rad_designs.thy#L287)).

## Algebraic properties

- [rad_par_mono](../../reactive-angelic-designs/utp_rad_parallel.thy#L140): monotone in both operands.
- [rad_par_comm_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L161): commutative when `M is SymMerge`.
- [rad_par_assoc](../../reactive-angelic-designs/utp_rad_parallel.thy#L201): associative for RAD+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) operands when `M is ORDm`,
  `M is SymMerge` and `AssocMerge M`.
- [rad_par_assoc_state](../../reactive-angelic-designs/utp_rad_parallel.thy#L170): alternatively accepts the pointwise two-fold
  associativity equation on `M`.
- [rad_par_lift_assoc](../../reactive-angelic-designs/utp_rad_parallel.thy#L221): with `M = merge_rdes j`, associative
  for RAD+A2 operands whose RD images satisfy `pre_R (ac2p P) = true_r`, when
  `j is SymMerge` and `AssocMerge j`. The lifted merge is not `AssocMerge`.
  [NDRD_healthy_iff](../../deps/UTP-Reactive-Designs/utp_rdes_triples.thy#L745)
  turns the true preconditions into premises for
  [rdes_lift_parallel_assoc_nondiv](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L201),
  which transfers through `ac2p`.

[ORDm_SymMerge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L275) preserves symmetry.
[ORDm_AssocMerge_RD2](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L351)
establishes `AssocMerge (ORDm M)` from `AssocMerge (RD2 M)`;
[ORDm_AssocMerge](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L362)
uses `M is RD2` and `AssocMerge M`. See the [ordinary RD laws](RD.md#generic-merge-associativity)
for the component preservation rules and exact premises.

## Basic merge

[rad_basic_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L268) requires equal branch/output traces extending the prior
trace, combines waiting by disjunction, leaves refusals unconstrained and
requires `okL ∧ okR ⟶ ok'`. Its constraints also apply after divergence.

The seed is not [ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L27)-healthy ([rad_basic_merge_not_ORDm](../../reactive-angelic-designs/utp_rad_parallel.thy#L323)).
`ORDm rad_basic_merge` permits precisely trace extension before start,
copies the prior observation while started and waiting, and agrees with the
seed while running when both branch traces extend the prior trace
([ORDm_unstarted](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L161), [ORDm_basic_merge_waiting](../../reactive-angelic-designs/utp_rad_parallel.thy#L365), [ORDm_basic_merge_running](../../reactive-angelic-designs/utp_rad_parallel.thy#L350)).

[ORDm](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L27) does not remove every output constraint after divergence:
[ORDm_post_ref_example](../../reactive-angelic-designs/utp_rad_parallel.thy#L385) retains a final refusal constraint even with
`ok' = False`. This differs from completed RD parallel.

Representation correspondence with the former records is checked in
[utp_rad_representation.thy](../../reactive-angelic-designs/utp_rad_representation.thy).
