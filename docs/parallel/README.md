# Parallel by merge

[Documentation](../README.md) · [Paper guides](../paper/README.md)

- [Generic](Generic.md): `P ∥[M] Q`, its symmetry and associativity laws, and guarded merges.
- [D](D.md): ordinary designs, `P ∥D[j] Q`.
- [AD](AD.md): angelic designs, `P ∥AD[j] Q`.
- [RD](RD.md): ordinary reactive designs, `P ∥RD[j] Q`.
- [Stateful RD](RD-stateful.md): `P ∥R[M] Q`, including state-merge lifting and normality.
- [RAD](RAD.md): reactive angelic designs, `P ∥RAD[j] Q`.
- [AP](AP.md): angelic processes, `P ∥AP[M] Q`.
- [Related work](related-work.md): divergence, infeasibility and comparisons with other models.

## Shared notation

| Notation | Meaning |
| --- | --- |
| `P, Q, R` | Operands |
| `j` | State merge; each model lifts it to its observations |
| `M` | Merge of complete observations |
| `P is H` | `H P = P` |
| `(ok, s)` | Prior observation |
| `okL, sR, …` | Branch observations, subscripted `L`, `R` |
| `ok', s'` | Merged output |
| `acL, acR, ac'` | AD choice sets, rather than individual states |
| `j(s,sL,sR,s')` | `merge_eval j s sL sR s'` |
| `mergeable j` | `∀s sL sR. ∃s'. j(s,sL,sR,s')` |
| `x`, `z` | Prior and output records with auxiliary variables |
| `p, q, r` | Branch records |
| `u` | Intermediate merge result |
| `M(x,p,q,z)` | `merge_eval M x p q z` |
| `ok0, s0` | Isabelle names for `ok, s` where those would resolve to lens constants |

The guides use readable observation tuples rather than literal record syntax.

The merges constructed from `j`:

| Model | Merge | Parallel |
| --- | --- | --- |
| D | [`merge_des`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L30) `j` | `P ∥D[j] Q` |
| AD | [`merge_ades`](../../angelic-designs/utp_ades_parallel_lift.thy#L17) `j` | `P ∥AD[j] Q` |
| RD | [`merge_rdes`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L34) `j` | `P ∥RD[j] Q` |
| RAD | [`merge_rad`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L348) `j` | `P ∥RAD[j] Q` |
