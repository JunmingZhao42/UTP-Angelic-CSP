# Angelic process parallel by merge

[Overview](../PARALLEL.md) · [AD](AD_PARALLEL.md) · [RAD](RAD_PARALLEL.md) · [AP](AP_PARALLEL.md)

| Theory | Purpose |
| --- | --- |
| [utp_ap_parallel.thy](../angelic-processes/utp_ap_parallel.thy) | Generic parallel with `APOKM` merge healthiness. |
| [utp_ap_parallel_lifted.thy](../angelic-processes/utp_ap_parallel_lifted.thy) | Direct lifting checks and a comparison construction through RAD. |

## 1. Generic parallel

[ap_par](../angelic-processes/utp_ap_parallel.thy#L234) uses the completed merge: `ap_par P N Q = P ∥[APOKM N] Q`.
[APOKM](../angelic-processes/utp_ap_parallel.thy#L84) is [monotonic](../angelic-processes/utp_ap_parallel.thy#L94) and [idempotent](../angelic-processes/utp_ap_parallel.thy#L133).
Here `N` is a merge on angelic observations.

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `AP` | `P`, `Q` both `AP` | `ap_par P N Q is AP` | [ap_par_AP_closure](../angelic-processes/utp_ap_parallel.thy#L391) |
| `A` | `P`, `Q` both `H1` | `ap_par P N Q is A` | [ap_par_A_closure](../angelic-processes/utp_ap_parallel.thy#L306) |

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂`, `N₁ ⊑ N₂` | `ap_par P₁ N₁ Q₁ ⊑ ap_par P₂ N₂ Q₂` | [ap_par_mono](../angelic-processes/utp_ap_parallel.thy#L412) |
| Commutativity | `N is SymMerge` | `ap_par P N Q = ap_par Q N P` | [ap_par_comm](../angelic-processes/utp_ap_parallel.thy#L418) |
| Associativity | `APOKM N is SymMerge`, `AssocMerge (APOKM N)` | `ap_par (ap_par P N Q) N R = ap_par P N (ap_par Q N R)` | [ap_par_assoc](../angelic-processes/utp_ap_parallel.thy#L427) |

## 2. Lifting ordinary reactive merges

AP shares RAD's observation alphabet and reuses [rad_lift_merge](RAD_PARALLEL.md#2-lifting-ordinary-reactive-merges).
The direct construction is `ap_par P (rad_lift_merge M) Q`.

### Merge healthiness and closure

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `APOKM` | None | `APOKM (rad_lift_merge M) is APOKM` | [ap_lift_merge_APOKM](../angelic-processes/utp_ap_parallel_lifted.thy#L189) |
| `AP` | `P`, `Q` both `AP` | `ap_par P (rad_lift_merge M) Q is AP` | [ap_lift_merge_AP](../angelic-processes/utp_ap_parallel_lifted.thy#L193) |

Global mapping laws and A2 closure for this direct construction remain open.

### Basic merge example

These results use `M = rad_basic_merge` at a started, nonwaiting initial
observation with `tr(s0) = 0`.

| Property | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| Merge policy | None | APOKM leaves the lifted basic merge unchanged at this observation | [ap_lift_basic_active](../angelic-processes/utp_ap_parallel_lifted.thy#L198) |
| Empty final set | None | The direct parallel rejects `{}`, even on failure | [ap_par_lift_basic_empty](../angelic-processes/utp_ap_parallel_lifted.thy#L215) |
| Singleton witnesses | `P`, `Q` both `AP`, `A2` | Accepted singleton branches and some `sOut ∈ Z` satisfy `basic_merge_state` and `okL ∧ okR ⇒ okOut` | [ap_par_lift_basic_active_obs](../angelic-processes/utp_ap_parallel_lifted.thy#L236) |

These local results do not establish global correspondence or A2 closure.

## 3. Parallel through RAD

The comparison construction [ap_par_via_rad](../angelic-processes/utp_ap_parallel_lifted.thy#L122) maps to RAD and back:

```
ap_par_via_rad P M Q = H1 (rad_par_lifted (RA1 P) M (RA1 Q))
```

### Healthiness and closure

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `AP` | None | `ap_par_via_rad P M Q is AP` | [ap_par_via_rad_AP](../angelic-processes/utp_ap_parallel_lifted.thy#L128) |
| `A2` | `P`, `Q` both `AP`, `A2` | `ap_par_via_rad P M Q is A2` | [ap_par_via_rad_A2](../angelic-processes/utp_ap_parallel_lifted.thy#L145) |

### Mapping laws

Write `F(P) = rad_ac2p (RA1 P)` and `G(D) = H1 (rad_p2ac D)`.
All parallel mapping laws below hold for arbitrary `M`, with the same flat RD
scope as [the RAD guide](RAD_PARALLEL.md#rad_ac2prad_p2ac-mapping-laws).

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| None | `RA1 (ap_par_via_rad P M Q) = rad_par_lifted (RA1 P) M (RA1 Q)` | [ap_par_via_rad_RA1](../angelic-processes/utp_ap_parallel_lifted.thy#L133) |
| `P`, `Q` both `RAD` | `ap_par_via_rad (H1 P) M (H1 Q) = H1 (rad_par_lifted P M Q)` | [ap_par_via_rad_H1](../angelic-processes/utp_ap_parallel_lifted.thy#L138) |
| `P`, `Q` both `AP`, `A2` | `F(ap_par_via_rad P M Q) = RD (F(P) ∥[M] F(Q))` | [ap_par_via_rad_ac2p](../angelic-processes/utp_ap_parallel_lifted.thy#L152) |
| `D`, `E` both `RD` | `ap_par_via_rad G(D) M G(E) = G(RD (D ∥[M] E))` | [ap_par_via_rad_p2ac](../angelic-processes/utp_ap_parallel_lifted.thy#L160) |

The conversions are not unrestricted inverses:

| Premises | Conclusion | Lemma |
| --- | --- | --- |
| `D is RD` | `F(G(D)) = D` | [ap_RD_roundtrip](../angelic-processes/utp_ap_parallel_lifted.thy#L99) |
| `P` both `AP`, `A2` | `G(F(P)) = H1 (RA1 P)` | [ap_RD_reverse_roundtrip](../angelic-processes/utp_ap_parallel_lifted.thy#L105) |
| `P` all `AP`, `A2`, `NDAP` | `G(F(P)) = P` | [ap_RD_reverse_roundtrip_NDAP](../angelic-processes/utp_ap_parallel_lifted.thy#L111) |

[Chaos_AP_neq_ChaosCSP](../angelic-processes/utp_ap_parallel_lifted.thy#L65) and [Chaos_AP_same_RAD](../angelic-processes/utp_ap_parallel_lifted.thy#L75) show that
distinct AP processes can have the same RA1 image. Thus parallel through RAD
[ap_par_via_rad_Chaos](../angelic-processes/utp_ap_parallel_lifted.thy#L177) cannot distinguish those operands.
No equality with the direct construction has been proved; its failure,
empty-set, trace and waiting cases remain to be investigated.
