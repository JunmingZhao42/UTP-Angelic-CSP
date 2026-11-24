# Angelic process parallel

[Parallel by merge](README.md) · [RAD](RAD.md)

Source: [`utp_ap_parallel.thy`](../../angelic-processes/utp_ap_parallel.thy).
[`ap_par`](../../angelic-processes/utp_ap_parallel.thy#L16) uses the reactive alphabet and merge of [RAD](RAD.md).

```isabelle
P ∥AP[j] Q = H1 (RA1 P ∥RAD[j] RA1 Q)
```

| Result of `P ∥AP[j] Q` | Operand premises | Merge premise | Lemma |
| --- | --- | --- | --- |
| [`A2`](../../angelic-designs/utp_ades_a2.thy#L94) | Both AP+[`A2`](../../angelic-designs/utp_ades_a2.thy#L94) | None | [`ap_par_A2`](../../angelic-processes/utp_ap_parallel.thy#L44) |
| [`AP`](../../angelic-processes/utp_ap_healthy.thy#L178) | Both AP+[`A2`](../../angelic-designs/utp_ades_a2.thy#L94) | None | [`ap_par_AP`](../../angelic-processes/utp_ap_parallel.thy#L23) |

## ac2p/p2ac mapping laws

Write `F(P) = ac2p (RA1 P)` and `G(D) = H1 (p2ac D)`.

| Operand premises | Merge premise | Equality | Lemma |
| --- | --- | --- | --- |
| `P,Q` both AP and A2 | None | `RA1 (P ∥AP[j] Q) = RA1 P ∥RAD[j] RA1 Q` | [`ap_par_RA1`](../../angelic-processes/utp_ap_parallel.thy#L30) |
| `P,Q` both AP and A2 | None | `F(P ∥AP[j] Q) = F(P) ∥RD[j] F(Q)` | [`ap_par_ac2p`](../../angelic-processes/utp_ap_parallel.thy#L51) |
| `D,E` both RD | None | `G(D) ∥AP[j] G(E) = G(D ∥RD[j] E)` | [`ap_par_p2ac`](../../angelic-processes/utp_ap_parallel.thy#L59) |
| `P,Q` both RAD | None | `H1 P ∥AP[j] H1 Q = H1 (P ∥RAD[j] Q)` | [`ap_par_H1`](../../angelic-processes/utp_ap_parallel.thy#L37) |

| Operand premises | Round trip | Lemma |
| --- | --- | --- |
| `D is RD` | `F(G(D)) = D` | [`ap_RD_roundtrip`](../../angelic-processes/utp_ap_rad.thy#L292) |
| `P` is AP and A2 | `G(F(P)) = H1 (RA1 P)` | [`ap_RD_reverse_roundtrip`](../../angelic-processes/utp_ap_rad.thy#L301) |
| `P` is AP, A2 and NDAP | `G(F(P)) = P` | [`ap_RD_reverse_roundtrip_NDAP`](../../angelic-processes/utp_ap_nd.thy#L216) |

## Canonicity through RAD

[`ap_par_canonical`](../../angelic-processes/utp_ap_parallel.thy#L88) transports
[RAD canonicity](RAD.md#canonicity) through the monotone outer `H1`:

```isabelle
M is ABm ⟹ singleton_refines (merge_rdes j) M ⟹
  P ∥AP[j] Q ⊑ H1 (RA1 P ∥[M] RA1 Q)
```

There is no operand healthiness or A2 premise. This compares operators
transported through RAD; it does not characterise arbitrary AP parallel
operators or establish AP closure of the comparison operator.

## Algebraic properties

[`ap_par_mono`](../../angelic-processes/utp_ap_parallel.thy#L96) gives monotonicity. [`ap_par_comm`](../../angelic-processes/utp_ap_parallel.thy#L103) gives commutativity when
`j is SymMerge`. No AP associativity theorem is installed.

The [`RA1`](../../reactive-angelic-designs/utp_rad_trace.thy#L17) transport can identify distinct divergent processes:
[`Chaos_AP_neq_ChaosCSP`](../../angelic-processes/utp_ap_ops.thy#L323) and [`Chaos_AP_same_RAD`](../../angelic-processes/utp_ap_ops.thy#L333) exhibit this, and
[`ap_par_Chaos`](../../angelic-processes/utp_ap_parallel.thy#L77) shows their parallel images agree.
