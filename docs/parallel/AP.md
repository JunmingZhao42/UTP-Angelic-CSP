# Angelic process parallel by merge

[Overview](README.md) · [AD](AD.md) · [RAD](RAD.md) · [AP](AP.md)

[utp_ap_parallel.thy](../../angelic-processes/utp_ap_parallel.thy)
defines the sole AP operator, `ap_par`, written `P ∥AP[M] Q`,
using [RAD parallel](RAD.md).
The notation and reactive merge conventions are those of the RAD guide.

## AP parallel by merge

The operator [ap_par](../../angelic-processes/utp_ap_parallel.thy#L121) maps to RAD and back:

```isabelle
P ∥AP[M] Q = H1 ((RA1 P) ∥RAD[M] (RA1 Q))
```

| Healthiness | Operand premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| `AP` | None | `(P ∥AP[M] Q) is AP` | [ap_par_AP](../../angelic-processes/utp_ap_parallel.thy#L128) |
| `A2` | `P`, `Q` both `AP`, `A2` | `(P ∥AP[M] Q) is A2` | [ap_par_A2](../../angelic-processes/utp_ap_parallel.thy#L145) |

## `ac2p`/`p2ac` mapping laws

Write `F(P) = ac2p (RA1 P)` and `G(D) = H1 (p2ac D)`.
All parallel mapping laws below hold for arbitrary `M`, with the same flat RD
scope as [the RAD guide](RAD.md#ac2pp2ac-mapping-laws).

| Operand premises | Equality | Lemma |
| --- | --- | --- |
| None | `RA1 (P ∥AP[M] Q) = (RA1 P) ∥RAD[M] (RA1 Q)` | [ap_par_RA1](../../angelic-processes/utp_ap_parallel.thy#L133) |
| `P`, `Q` both `RAD` | `(H1 P) ∥AP[M] (H1 Q) = H1 (P ∥RAD[M] Q)` | [ap_par_H1](../../angelic-processes/utp_ap_parallel.thy#L138) |
| `P`, `Q` both `AP`, `A2` | `F(P ∥AP[M] Q) = RD (F(P) ∥[M] F(Q))` | [ap_par_ac2p](../../angelic-processes/utp_ap_parallel.thy#L152) |
| `D`, `E` both `RD` | `G(D) ∥AP[M] G(E) = G(RD (D ∥[M] E))` | [ap_par_p2ac](../../angelic-processes/utp_ap_parallel.thy#L160) |

The conversions are not unrestricted inverses:

| Premises | Conclusion | Lemma |
| --- | --- | --- |
| `D is RD` | `F(G(D)) = D` | [ap_RD_roundtrip](../../angelic-processes/utp_ap_parallel.thy#L98) |
| `P` both `AP`, `A2` | `G(F(P)) = H1 (RA1 P)` | [ap_RD_reverse_roundtrip](../../angelic-processes/utp_ap_parallel.thy#L104) |
| `P` all `AP`, `A2`, `NDAP` | `G(F(P)) = P` | [ap_RD_reverse_roundtrip_NDAP](../../angelic-processes/utp_ap_parallel.thy#L110) |

## Algebraic properties

| Property | Premises | Algebraic law | Lemma |
| --- | --- | --- | --- |
| Monotonicity | `P₁ ⊑ P₂`, `Q₁ ⊑ Q₂` | `P₁ ∥AP[M] Q₁ ⊑ P₂ ∥AP[M] Q₂` | [ap_par_mono](../../angelic-processes/utp_ap_parallel.thy#L184) |
| Commutativity | `rad_lift_merge M is SymMerge` | `P ∥AP[M] Q = Q ∥AP[M] P` | [ap_par_comm](../../angelic-processes/utp_ap_parallel.thy#L191) |

Associativity depends on the corresponding [RAD law](RAD.md#algebraic-properties).

## Divergent process example

[Chaos_AP_neq_ChaosCSP](../../angelic-processes/utp_ap_parallel.thy#L64) and [Chaos_AP_same_RAD](../../angelic-processes/utp_ap_parallel.thy#L74) show that
distinct AP processes can have the same RA1 image. Thus parallel through RAD
[ap_par_Chaos](../../angelic-processes/utp_ap_parallel.thy#L177) cannot distinguish those operands.
This transport deliberately works through the RA1 image of its operands.
The former direct operator remains on the original branch.
