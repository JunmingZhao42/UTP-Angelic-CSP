# Angelic process parallel by merge

[Overview](../PARALLEL.md) · [AD](AD_PARALLEL.md) · [RAD](RAD_PARALLEL.md) · [AP](AP_PARALLEL.md)

[utp_ap_parallel.thy](../angelic-processes/utp_ap_parallel.thy)
defines the sole AP operator, `ap_par`, using [RAD parallel](RAD_PARALLEL.md).
It has mapping and A2 laws, at the cost of identifying some distinct divergent
AP processes. The former direct operator remains on the original branch.

The operator [ap_par](../angelic-processes/utp_ap_parallel.thy#L121) maps to RAD and back:

```
ap_par P M Q = H1 (rad_par (RA1 P) M (RA1 Q))
```

### Healthiness and closure

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `AP` | None | `ap_par P M Q is AP` | [ap_par_AP](../angelic-processes/utp_ap_parallel.thy#L127) |
| `A2` | `P`, `Q` both `AP`, `A2` | `ap_par P M Q is A2` | [ap_par_A2](../angelic-processes/utp_ap_parallel.thy#L144) |

### Mapping laws

Write `F(P) = rad_ac2p (RA1 P)` and `G(D) = H1 (rad_p2ac D)`.
All parallel mapping laws below hold for arbitrary `M`, with the same flat RD
scope as [the RAD guide](RAD_PARALLEL.md#rad_ac2prad_p2ac-mapping-laws).

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| None | `RA1 (ap_par P M Q) = rad_par (RA1 P) M (RA1 Q)` | [ap_par_RA1](../angelic-processes/utp_ap_parallel.thy#L132) |
| `P`, `Q` both `RAD` | `ap_par (H1 P) M (H1 Q) = H1 (rad_par P M Q)` | [ap_par_H1](../angelic-processes/utp_ap_parallel.thy#L137) |
| `P`, `Q` both `AP`, `A2` | `F(ap_par P M Q) = RD (F(P) ∥[M] F(Q))` | [ap_par_ac2p](../angelic-processes/utp_ap_parallel.thy#L151) |
| `D`, `E` both `RD` | `ap_par G(D) M G(E) = G(RD (D ∥[M] E))` | [ap_par_p2ac](../angelic-processes/utp_ap_parallel.thy#L159) |

The conversions are not unrestricted inverses:

| Premises | Conclusion | Lemma |
| --- | --- | --- |
| `D is RD` | `F(G(D)) = D` | [ap_RD_roundtrip](../angelic-processes/utp_ap_parallel.thy#L98) |
| `P` both `AP`, `A2` | `G(F(P)) = H1 (RA1 P)` | [ap_RD_reverse_roundtrip](../angelic-processes/utp_ap_parallel.thy#L104) |
| `P` all `AP`, `A2`, `NDAP` | `G(F(P)) = P` | [ap_RD_reverse_roundtrip_NDAP](../angelic-processes/utp_ap_parallel.thy#L110) |

[Chaos_AP_neq_ChaosCSP](../angelic-processes/utp_ap_parallel.thy#L64) and [Chaos_AP_same_RAD](../angelic-processes/utp_ap_parallel.thy#L74) show that
distinct AP processes can have the same RA1 image. Thus parallel through RAD
[ap_par_Chaos](../angelic-processes/utp_ap_parallel.thy#L176) cannot distinguish those operands.
This transport deliberately works through the RA1 image of its operands.

### Algebra

| Property | Premises | Law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂` | `ap_par P₁ M Q₁ ⊑ ap_par P₂ M Q₂` | `ap_par_mono` |
| Commutativity | `rad_lift_merge M is SymMerge` | `ap_par P M Q = ap_par Q M P` | `ap_par_comm` |

Associativity depends on the corresponding RAD law.
