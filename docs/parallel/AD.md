# Angelic design parallel

[Parallel by merge](README.md) · [D](D.md)

Source: [utp_ades_parallel.thy](../../angelic-designs/utp_ades_parallel.thy).
[Shared notation](README.md#shared-notation).

## Merge healthiness

The [Design conditions](D.md#design-merge-healthiness) apply directly.
The additional transformers are [A0m](../../angelic-designs/utp_ades_parallel.thy#L43), [A1m](../../angelic-designs/utp_ades_parallel.thy#L51) and [A2m](../../angelic-designs/utp_ades_parallel.thy#L77):

- [A0m](../../angelic-designs/utp_ades_parallel.thy#L43) allows termination with `{}` only where divergence with `{}` is accepted.
- [A1m](../../angelic-designs/utp_ades_parallel.thy#L51) permits any output before start. After start, an output is accepted
  through divergence with a subset of `ac'`, or termination with a subset
  when `ok'` holds.
- [A2m](../../angelic-designs/utp_ades_parallel.thy#L77) has two cases. For singleton branch sets, apply [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) to the output:
  `M(ok',{}) ∨ (∃s'∈ac'. M(ok',{s'}))`. Otherwise retain the original
  observation and require this condition at every singleton branch pair.
  An empty branch set permits any state when selecting its representative.

All three are monotone and idempotent. Singleton witnesses do not restrict
accepted outputs to singleton sets: larger sets are accepted through their
members. The prior and branch flags stay fixed during output normalisation.

For an arbitrary `M :: 's ades_merge_rel`:

| Result of `P ∥[M] Q` | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| [A0](../../angelic-designs/utp_ades_healthy.thy#L555) | None | [A0m](../../angelic-designs/utp_ades_parallel.thy#L43) | [A0_par_by_merge](../../angelic-designs/utp_ades_parallel.thy#L161) |
| [A1](../../angelic-designs/utp_ades_healthy.thy#L621) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [A1m](../../angelic-designs/utp_ades_parallel.thy#L51) | [A1_par_by_merge](../../angelic-designs/utp_ades_parallel.thy#L173) |
| [A](../../angelic-designs/utp_ades_healthy.thy#L700) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [A0m](../../angelic-designs/utp_ades_parallel.thy#L43), [A1m](../../angelic-designs/utp_ades_parallel.thy#L51) | [A_par_by_merge](../../angelic-designs/utp_ades_parallel.thy#L208) |
| [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | Both [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | [A2m](../../angelic-designs/utp_ades_parallel.thy#L77) | [A2_par_by_merge](../../angelic-designs/utp_ades_parallel.thy#L224) |
| [A3](../../angelic-designs/utp_ades_healthy.thy#L1448) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [H1m](../../deps/UTP-Designs/utp_des_parallel.thy#L18), [H3m](../../deps/UTP-Designs/utp_des_parallel.thy#L30) | [A3_par_by_merge](../../angelic-designs/utp_ades_parallel.thy#L253) |

These are sufficient closure conditions; converses remain open.
There is no A3m: [A3](../../angelic-designs/utp_ades_healthy.thy#L1448) closure uses [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) and [H3](../../deps/UTP-Designs/utp_des_healths.thy#L554).

## Commutation of merge healthiness

[H1m](../../deps/UTP-Designs/utp_des_parallel.thy#L18) commutes with [A0m](../../angelic-designs/utp_ades_parallel.thy#L43), [A1m](../../angelic-designs/utp_ades_parallel.thy#L51) and [A2m](../../angelic-designs/utp_ades_parallel.thy#L77). [H2m](../../deps/UTP-Designs/utp_des_parallel.thy#L24), [H3m](../../deps/UTP-Designs/utp_des_parallel.thy#L30) and [HDM](../../deps/UTP-Designs/utp_des_parallel.thy#L36) commute with [A0m](../../angelic-designs/utp_ades_parallel.thy#L43) and
[A1m](../../angelic-designs/utp_ades_parallel.thy#L51). The lemmas are [H1m_AD_commute](../../angelic-designs/utp_ades_parallel.thy#L109), [H1m_A2m_commute](../../angelic-designs/utp_ades_parallel.thy#L114),
[H2m_A0m_commute](../../angelic-designs/utp_ades_parallel.thy#L132), [H2m_A1m_commute](../../angelic-designs/utp_ades_parallel.thy#L136), [H3m_A0m_commute](../../angelic-designs/utp_ades_parallel.thy#L140),
[H3m_A1m_commute](../../angelic-designs/utp_ades_parallel.thy#L144) and [HDM_angelic_commute](../../angelic-designs/utp_ades_parallel.thy#L148).

The other six pairs fail to commute in general; their exploratory
counterexample lemmas are not retained in this theory. Conditional commutation
and one-way preservation remain open.

## Lifting a state merge

[ades_lift_merge](../../angelic-designs/utp_ades_parallel.thy#L275) supplies the raw lift; [merge_ades](../../angelic-designs/utp_ades_parallel.thy#L292) completes it, and
[ades_par](../../angelic-designs/utp_ades_parallel.thy#L366) defines the parallel operator:

```isabelle
ades_lift_merge j ((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
  acL ≠ {} ∧ acR ≠ {} ∧ ok' = (okL ∧ okR) ∧
  (∀sL∈acL. ∀sR∈acR. ∃s'∈ac'. j(s,sL,sR,s'))
```
```isabelle
merge_ades j ≡ H3m (H1m (ades_lift_merge j))
P ∥AD[j] Q ≡ P ∥[merge_ades j] Q
```

By [merge_ades_obs](../../angelic-designs/utp_ades_parallel.thy#L318), before start the completed merge accepts everything.
After start it requires nonempty branch sets and a merge witness for every
branch-state pair. If both branches terminate, the output must terminate and
each pair must have a witness in `ac'`. Otherwise the final observation is
unrestricted, while merge feasibility is retained.

For every `j`, the completed merge has:

| Healthiness of `merge_ades j` | Lemma |
| --- | --- |
| [H1m](../../deps/UTP-Designs/utp_des_parallel.thy#L18) | [merge_ades_is_H1m](../../angelic-designs/utp_ades_parallel.thy#L330) |
| [H2m](../../deps/UTP-Designs/utp_des_parallel.thy#L24) | [merge_ades_is_H2m](../../angelic-designs/utp_ades_parallel.thy#L333) |
| [H3m](../../deps/UTP-Designs/utp_des_parallel.thy#L30) | [merge_ades_is_H3m](../../angelic-designs/utp_ades_parallel.thy#L339) |
| [HDM](../../deps/UTP-Designs/utp_des_parallel.thy#L36) | [merge_ades_is_HDM](../../angelic-designs/utp_ades_parallel.thy#L336) |
| [A0m](../../angelic-designs/utp_ades_parallel.thy#L43) | [merge_ades_is_A0m](../../angelic-designs/utp_ades_parallel.thy#L342) |
| [A1m](../../angelic-designs/utp_ades_parallel.thy#L51) | [merge_ades_is_A1m](../../angelic-designs/utp_ades_parallel.thy#L347) |
| [A2m](../../angelic-designs/utp_ades_parallel.thy#L77) | [merge_ades_is_A2m](../../angelic-designs/utp_ades_parallel.thy#L352) |

The resulting parallel closure needs no merge premise:

| Result of `P ∥AD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| [A](../../angelic-designs/utp_ades_healthy.thy#L700) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [ades_par_A_closure](../../angelic-designs/utp_ades_parallel.thy#L437) |
| [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | Both [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | [ades_par_A2_closure](../../angelic-designs/utp_ades_parallel.thy#L443) |
| [A3](../../angelic-designs/utp_ades_healthy.thy#L1448) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [ades_par_A3_closure](../../angelic-designs/utp_ades_parallel.thy#L449) |

There is no outer [A3](../../angelic-designs/utp_ades_healthy.thy#L1448) wrapper.

[ades_par_eval](../../angelic-designs/utp_ades_parallel.thy#L423) evaluates branch sets under [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10).
[ades_par_obs_A2](../../angelic-designs/utp_ades_parallel.thy#L373) reduces them to singleton witnesses under [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10)+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218);
[ades_par_obs](../../angelic-designs/utp_ades_parallel.thy#L400) specialises this to A+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218).
[ades_par_normalise_A](../../angelic-designs/utp_ades_parallel.thy#L415) gives `P ∥AD[j] Q = A P ∥AD[j] A Q`
under [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10)+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218).

## ac2p/d2ac mapping laws

| Operand premises | Merge premise | Equality | Lemma |
| --- | --- | --- | --- |
| `P,Q` both A and A2 | None | `ac2p (P ∥AD[j] Q) = ac2p P ∥D[j] ac2p Q` | [ades_par_ac2p](../../angelic-designs/utp_ades_parallel.thy#L483) |
| `P,Q` both A and A2 | None | `P ∥AD[j] Q = d2ac (ac2p P ∥D[j] ac2p Q)` | [ades_par_d2ac_ac2p](../../angelic-designs/utp_ades_parallel.thy#L459) |
| `D,E` both H | None | `d2ac D ∥AD[j] d2ac E = d2ac (D ∥D[j] E)` | [ades_par_d2ac](../../angelic-designs/utp_ades_parallel.thy#L476) |
| `D,E` both H | None | `D ∥D[j] E = ac2p (d2ac D ∥AD[j] d2ac E)` | [ades_par_ac2p_d2ac](../../angelic-designs/utp_ades_parallel.thy#L495) |

## Algebraic laws

- [ades_par_mono](../../angelic-designs/utp_ades_parallel.thy#L503): monotone in both operands.
- [ades_par_comm](../../angelic-designs/utp_ades_parallel.thy#L556): commutative when `j is SymMerge`; no operand premises.
- [ades_par_assoc](../../angelic-designs/utp_ades_parallel.thy#L566): associative for [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10)+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) operands when `j is SymMerge`,
  `AssocMerge j` and `mergeable j`. The proof transfers the Design law;
  these premises do not establish unrestricted `AssocMerge (merge_ades j)`.
- [ades_par_diverge](../../angelic-designs/utp_ades_parallel.thy#L511): an accepted nonterminating output permits every
  output at the same prior observation.
- [ades_par_chaos](../../angelic-designs/utp_ades_parallel.thy#L522): `Chaos ∥AD[j] Chaos = Chaos` when
  `∀s. ∃sL sR u. j(s,sL,sR,u)`.
- [ades_par_miracle](../../angelic-designs/utp_ades_parallel.thy#L541): `P ∥AD[j] Miracle = Miracle ∥AD[j] P = Miracle`
  for [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) operands and arbitrary `j`.

Chaos is `true`; Miracle is `A false = ¬ok`.
A one-sided AD Chaos-zero law for an arbitrary feasible operand is not installed.
For `skipₘ`, commutativity is unconditional and associativity needs [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10)+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218)
operands ([ades_par_skip_comm](../../angelic-designs/utp_ades_parallel.thy#L635), [ades_par_skip_assoc](../../angelic-designs/utp_ades_parallel.thy#L639)).

## Generic parallel laws

For arbitrary AD merges, use the
[generic concurrency laws](README.md#generic-concurrency-laws) directly.
Their symmetry and associativity premises concern the observation merge
`M`, rather than the state merge `j`.
