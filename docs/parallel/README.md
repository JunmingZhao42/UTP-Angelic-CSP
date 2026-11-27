# Parallel by merge

[Documentation](../README.md) · [Paper guides](../paper/README.md)

- [Generic](Generic.md): `P ∥[M] Q`, its symmetry and associativity laws, and guarded merges.
- [D](D.md): ordinary designs, `P ∥D[j] Q`.
- [AD](AD.md): angelic designs, `P ∥AD[j] Q`.
- [Canonicity](Canonicity.md): the choice-set lift as the least admissible merge on choice sets, for AD and RAD.
- [RD](RD.md): ordinary reactive designs, `P ∥RD[j] Q`.
- [Stateful RD](RD-stateful.md): `P ∥R[M] Q`, including state-merge lifting and normality.
- [RAD](RAD.md): reactive angelic designs, `P ∥RAD[j] Q`.
- [AP](AP.md): angelic processes, `P ∥AP[j] Q`.
- [Related work](related-work.md): divergence, infeasibility and comparisons with other models.

## Shared notation

| Notation | Meaning |
| --- | --- |
| `P, Q, R` | Operands |
| `j` | State merge; each model lifts it to its observations |
| `M` | Merge of complete observations |

Each merge reads a prior, two branches and an output:

| | Prior | Left | Right | Output |
| --- | --- | --- | --- | --- |
| Termination flag | `ok` | `okL` | `okR` | `ok'` |
| State | `s` | `sL` | `sR` | `s'` |
| Choice set (AD, RAD) | - | `acL` | `acR` | `ac'` |
| Whole record | `x` | `p` | `q` | `z` |

`j` reads states and `M` reads whole records; a record also carries any auxiliary
variables. With three branches, for operands `P`, `Q` and `R`, the states are
`sP, sQ, sR`, the flags `okP, okQ, okR`, the choice sets `acP, acQ, acR` and the
records `p, q, r`. An intermediate merge result is `u`, with flag `okU` and choice
set `acU`.

| Notation | Meaning |
| --- | --- |
| `j(s,sL,sR,s')` | `merge_eval j s sL sR s'` |
| `M(x,p,q,z)` | `merge_eval M x p q z` |
| `A2` | [No angelic choice](../paper/AD.md#d20): the ordinary fragment, which corresponds to D or RD through `ac2p` |
| `ok0, s0` | Isabelle names for `ok, s` where those would resolve to lens constants |

The guides use readable observation tuples rather than literal record syntax.

The merges constructed from `j`:

| Model | Merge | Parallel |
| --- | --- | --- |
| D | [`merge_des`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L30) `j` | `P ∥D[j] Q` |
| AD | [`merge_ades`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L14) `j` | `P ∥AD[j] Q` |
| RD | [`merge_rdes`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L34) `j` | `P ∥RD[j] Q` |
| RAD | [`merge_rad`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L35) `j` | `P ∥RAD[j] Q` |
