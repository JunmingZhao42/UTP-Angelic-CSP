# Angelic process parallel

[Parallel by merge](README.md) · [RAD](RAD.md)

Source: [utp_ap_parallel.thy](../../angelic-processes/utp_ap_parallel.thy).
[ap_par](../../angelic-processes/utp_ap_parallel.thy#L121) uses the reactive alphabet and merge of [RAD](RAD.md).

```text
P ∥AP[M] Q = H1 (RA1 P ∥RAD[M] RA1 Q)
```

| Result of `P ∥AP[M] Q` | Operand premises | Merge premise | Lemma |
| --- | --- | --- | --- |
| [A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | Both AP+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | None | [ap_par_A2](../../angelic-processes/utp_ap_parallel.thy#L149) |
| [AP](../../angelic-processes/utp_ap_healthy.thy#L173) | Both AP+[A2](../../angelic-designs/utp_ades_healthy.thy#L1218) | `M is ORDm` | [ap_par_AP](../../angelic-processes/utp_ap_parallel.thy#L128) |

## ac2p/p2ac mapping laws

Write `F(P) = ac2p (RA1 P)` and `G(D) = H1 (p2ac D)`.

| Operand premises | Merge premise | Equality | Lemma |
| --- | --- | --- | --- |
| `P,Q` both AP and A2 | `M is ORDm` | `RA1 (P ∥AP[M] Q) = RA1 P ∥RAD[M] RA1 Q` | [ap_par_RA1](../../angelic-processes/utp_ap_parallel.thy#L135) |
| `P,Q` both AP and A2 | `M is ORDm` | `F(P ∥AP[M] Q) = F(P) ∥[M] F(Q)` | [ap_par_ac2p](../../angelic-processes/utp_ap_parallel.thy#L156) |
| `D,E` both RD | None | `G(D) ∥AP[M] G(E) = G(D ∥[M] E)` | [ap_par_p2ac](../../angelic-processes/utp_ap_parallel.thy#L164) |
| `P,Q` both RAD | None | `H1 P ∥AP[M] H1 Q = H1 (P ∥RAD[M] Q)` | [ap_par_H1](../../angelic-processes/utp_ap_parallel.thy#L142) |

| Operand premises | Round trip | Lemma |
| --- | --- | --- |
| `D is RD` | `F(G(D)) = D` | [ap_RD_roundtrip](../../angelic-processes/utp_ap_parallel.thy#L98) |
| `P` is AP and A2 | `G(F(P)) = H1 (RA1 P)` | [ap_RD_reverse_roundtrip](../../angelic-processes/utp_ap_parallel.thy#L104) |
| `P` is AP, A2 and NDAP | `G(F(P)) = P` | [ap_RD_reverse_roundtrip_NDAP](../../angelic-processes/utp_ap_parallel.thy#L110) |

## Algebraic properties

[ap_par_mono](../../angelic-processes/utp_ap_parallel.thy#L189) gives monotonicity. [ap_par_comm](../../angelic-processes/utp_ap_parallel.thy#L196) gives commutativity when
`rad_lift_merge M is SymMerge`. No AP associativity theorem is installed.

The [RA1](../../reactive-angelic-designs/utp_rad_healthy.thy#L16) transport can identify distinct divergent processes:
[Chaos_AP_neq_ChaosCSP](../../angelic-processes/utp_ap_parallel.thy#L64) and [Chaos_AP_same_RAD](../../angelic-processes/utp_ap_parallel.thy#L74) exhibit this, and
[ap_par_Chaos](../../angelic-processes/utp_ap_parallel.thy#L182) shows their parallel images agree.
