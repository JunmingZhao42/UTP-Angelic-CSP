# Reactive angelic design parallel

[Parallel by merge](README.md) · [AD](AD.md) · [AP](AP.md)

Source: [utp_rad_parallel.thy](../../reactive-angelic-designs/utp_rad_parallel.thy).
[Shared notation](README.md#shared-notation).

## Generic RAD merge healthiness

Each RAD observation has an outer termination flag. The prior carries one
inner state containing waiting, trace and refusals; the branches and final
observation carry sets of these inner states. This is the ordinary RAD
alphabet, without an additional mutable program state.

Each condition below is a transformer from RAD merges to RAD merges.
`M is H` means `H M = M`.

| Transformer | Effect |
| --- | --- |
| [RA1m](../../reactive-angelic-designs/utp_rad_parallel.thy#L22) | Restrict final choices to trace extensions and reject an empty restriction. |
| [RA2m](../../reactive-angelic-designs/utp_rad_parallel.thy#L29) | Remove the common trace history from the prior and both branches; normalise final choices and require a nonempty result. |
| [RA3m](../../reactive-angelic-designs/utp_rad_parallel.thy#L40) | Use reactive skip while the prior is waiting, requiring nonempty branch choice sets. |
| [CSPA1m](../../reactive-angelic-designs/utp_rad_parallel.thy#L49) | Before start, admit trace-feasible final choices when both branch sets are nonempty. |
| [PBMHm](../../angelic-designs/utp_ades_parallel.thy#L159) | Close acceptance upwards from nonempty final choice sets. |
| [RABm](../../angelic-designs/utp_ades_parallel.thy#L165) | Close acceptance downwards in both nonempty branch choice sets. |
| [CSPA2m](../../reactive-angelic-designs/utp_rad_parallel.thy#L59) | Permit output termination whenever the same remaining output is admitted with `ok' = False`. |

All seven transformers are monotone and idempotent and commute pairwise
([RADm_comms](../../reactive-angelic-designs/utp_rad_parallel.thy#L321)).
PBMHm and RABm are defined for general AD merges; CSPA2m abbreviates the design-layer
[H2m](../../deps/UTP-Designs/utp_des_parallel.thy#L24) condition.
[RA1m_RA2m_absorb](../../reactive-angelic-designs/utp_rad_parallel.thy#L138)
shows that RA2m already enforces RA1m, so [RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L318) omits the redundant factor:

```text
RADm ≡ RA2m ∘ RA3m ∘ CSPA1m ∘ PBMHm ∘ RABm ∘ CSPA2m
```

[RADm_healthy_iff](../../reactive-angelic-designs/utp_rad_parallel.thy#L355) characterises the common fixed points. [RADm_Idempotent](../../reactive-angelic-designs/utp_rad_parallel.thy#L366) and
[RADm_Monotonic](../../reactive-angelic-designs/utp_rad_parallel.thy#L369) establish the combined healthiness laws. These are sufficient
merge conditions for closure; they are not claimed to characterise every
merge that preserves RAD.

For combined RA closure, [RAm](../../reactive-angelic-designs/utp_rad_parallel.thy#L287) uses:

```text
RAm ≡ RA2m ∘ RA3m ∘ RABm
```

[RAm_healthy_iff](../../reactive-angelic-designs/utp_rad_parallel.thy#L299) exposes
RA1m, RA2m, RA3m and RABm as its fixed-point conditions. The transformer is
[idempotent](../../reactive-angelic-designs/utp_rad_parallel.thy#L310) and
[monotone](../../reactive-angelic-designs/utp_rad_parallel.thy#L313).

## Component parallel closure

All rows concern the supplied RAD merge in `P ∥[M] Q`.

| Result | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| RA1 | None | `M is RA1m` | [rad_par_by_merge_RA1](../../reactive-angelic-designs/utp_rad_parallel.thy#L397) |
| RA2 | Both RA1 and RA2 | `M is RA2m`, `M is RABm` | [rad_par_by_merge_RA2](../../reactive-angelic-designs/utp_rad_parallel.thy#L436) |
| RA3 | Both RA3 | `M is RA3m` | [rad_par_by_merge_RA3](../../reactive-angelic-designs/utp_rad_parallel.thy#L422) |
| RA | Both RA | `M is RAm` | [rad_par_by_merge_RA](../../reactive-angelic-designs/utp_rad_parallel.thy#L503) |
| CSPA1 | Both CSPA1 | `M is CSPA1m` | [rad_par_by_merge_CSPA1](../../reactive-angelic-designs/utp_rad_parallel.thy#L405) |
| CSPA2 | None | `M is CSPA2m` | [rad_par_by_merge_CSPA2](../../reactive-angelic-designs/utp_rad_parallel.thy#L520) |
| PBMH_ades | None | `M is PBMHm` | [PBMH_ades_par_by_merge](../../angelic-designs/utp_ades_parallel.thy#L306) |
| RAD | Both RAD | `M is RADm` | [rad_par_by_merge_RAD](../../reactive-angelic-designs/utp_rad_parallel.thy#L527) |

Trace normalisation uses RABm to restrict branch witnesses to their
trace-extending choices. The combined RA and RAD closure rules have no A2 premise.

## Basic RAD merge

[rad_basic_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L540)
requires nonempty branch choice sets and acts directly on RAD observations.
Waiting uses reactive angelic skip; unstarted observations admit trace-feasible
final sets. In the active case, every branch-state pair needs a final witness
with the same trace contribution and the disjunction of the branch waiting
flags. Refusals are unrestricted, and `okL ∧ okR` requires `ok'`.

Its seven component healthiness proofs establish
[rad_basic_merge_RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L634).
The generic closure rule therefore applies to RAD operands without an A2 premise.

## Reactive merge lifting

A RAD state is `('t,'e) rad_state = ('t,'e set) rea_vars_ext`, containing
waiting, trace and refusals; the outer design supplies `ok`.
`M` merges complete ordinary reactive observations. Write `obs(ok,s)`
for such an observation. [rad_lift_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L645) defines the lift used by [rad_par](../../reactive-angelic-designs/utp_rad_parallel.thy#L847).

The lift instantiates the [shared choice-set construction](AD.md#choice-set-lifting)
with `rad_state` and applies RABm to require nonempty branch sets.

```text
rad_lift_merge ≡ RABm ∘ choice_lift_merge

rad_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  acL ≠ {} ∧ acR ≠ {} ∧
  (∀sL∈acL. ∀sR∈acR. ∃s'∈ac'.
     M(obs(ok,s),obs(okL,sL),obs(okR,sR),obs(ok',s')))

P ∥RAD[M] Q ≡ P ∥[rad_lift_merge M] Q
```

[merge_rad](../../reactive-angelic-designs/utp_rad_parallel.thy#L1016) names the
instance `rad_lift_merge (merge_rdes j)` for
`j :: ('t × 'e set) merge`. The generic lift and parallel operator accept
any ordinary merge `M`.

[rad_lift_merge_obs](../../reactive-angelic-designs/utp_rad_parallel.thy#L650) gives the evaluation.
The lift applies the ordinary merge directly, including its divergence constraints.

## Lifted merge closure

[rad_lift_merge_RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L837) establishes `rad_lift_merge M is RADm` from
`M is ORDm`. The ordinary merge conditions are documented in [RD](RD.md#generic-merge-healthiness-and-closure).

| Result | Operand premises | Merge premise | Lemma |
| --- | --- | --- | --- |
| `rad_lift_merge M is RADm` | None | `M is ORDm` | [rad_lift_merge_RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L837) |
| `merge_rad j is RADm` | None | None | [merge_rad_RADm](../../reactive-angelic-designs/utp_rad_parallel.thy#L1019) |
| `(P ∥RAD[M] Q) is RAD` | Both RAD | `M is ORDm` | [rad_par_RAD](../../reactive-angelic-designs/utp_rad_parallel.thy#L893) |
| `(P ∥RAD[M] Q) is A2` | Both RAD and A2 | None | [rad_par_A2](../../reactive-angelic-designs/utp_rad_parallel.thy#L884) |

## ac2p/p2ac mapping laws

| Operand premises | Merge premise | Equality | Lemma |
| --- | --- | --- | --- |
| None | None | `p2ac D ∥RAD[M] p2ac E = p2ac (D ∥[M] E)` | [rad_par_p2ac](../../reactive-angelic-designs/utp_rad_parallel.thy#L854) |
| None | None | `p2ac D ∥[merge_rad j] p2ac E = p2ac (D ∥RD[j] E)` | [merge_rad_p2ac](../../reactive-angelic-designs/utp_rad_parallel.thy#L1023) |
| `P,Q` both RAD and A2 | None | `P ∥RAD[M] Q = p2ac (ac2p P ∥[M] ac2p Q)` | [rad_par_form](../../reactive-angelic-designs/utp_rad_parallel.thy#L864) |
| `P,Q` both RAD and A2 | None | `ac2p (P ∥RAD[M] Q) = ac2p P ∥[M] ac2p Q` | [rad_par_ac2p](../../reactive-angelic-designs/utp_rad_parallel.thy#L875) |

[rad_ac2p_RD](../../reactive-angelic-designs/utp_rad_csp.thy#L421) maps RAD+A2 to RD;
[rad_p2ac_RD](../../reactive-angelic-designs/utp_rad_csp.thy#L407) relates RD and RAD healthiness.
RAD rejects empty output sets ([RAD_empty](../../reactive-angelic-designs/utp_rad_designs.thy#L534)),
so AD's d2ac/A3 completion does not supply RAD closure
([rad_d2ac_not_RAD](../../reactive-angelic-designs/utp_rad_designs.thy#L542),
[A3_not_RAD](../../reactive-angelic-designs/utp_rad_designs.thy#L552)).

## Algebraic properties

- [rad_par_mono](../../reactive-angelic-designs/utp_rad_parallel.thy#L901): monotone in both operands.
- [rad_par_comm_merge](../../reactive-angelic-designs/utp_rad_parallel.thy#L922): commutative when `M is SymMerge`.
- [rad_par_assoc](../../reactive-angelic-designs/utp_rad_parallel.thy#L962): associative for RAD+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) operands when `M is ORDm`,
  `M is SymMerge` and `AssocMerge M`.
- [rad_par_assoc_state](../../reactive-angelic-designs/utp_rad_parallel.thy#L931): alternatively accepts the pointwise two-fold
  associativity equation on `M`.
- [rad_par_lift_assoc](../../reactive-angelic-designs/utp_rad_parallel.thy#L982): with `M = merge_rdes j`, associative
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
