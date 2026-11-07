# Parallel by merge

[Documentation](../README.md) · [Paper guides](../paper/README.md)

- [D](D.md): ordinary designs, `P ∥D[j] Q`.
- [AD](AD.md): angelic designs, `P ∥AD[j] Q`.
- [RAD](RAD.md): reactive angelic designs, `P ∥RAD[M] Q`.
- [AP](AP.md): angelic processes, `P ∥AP[M] Q`.
- [Related work](related-work.md): divergence, infeasibility and comparisons with other models.

## Shared notation

`P,Q,R` are operands; `j` is a state merge and `M` an observation merge.
`P is H` means `H P = P`. In mathematical formulas, the prior is `(ok,s)`;
branch observations use subscripts `L,R`, and the merged output uses primes.
AD outputs contain choice sets `acL,acR,ac'`, rather than individual states.

`j(s,sL,sR,s')` abbreviates `merge_eval j s sL sR s'`.
`mergeable j` means `∀s sL sR. ∃s'. j(s,sL,sR,s')`.
Isabelle uses `ok0,s0` where the unadorned names would resolve to lens constants.
The guides use readable observation tuples rather than literal record syntax.

## Generic concurrency laws

[utp_concurrency.thy](../../deps/UTP/utp_concurrency.thy) defines [par_by_merge](../../deps/UTP/utp_concurrency.thy#L231), written `P ∥[M] Q`:

```text
(P ∥[M] Q)(x,out) ↔ ∃p q. P(x,p) ∧ Q(x,q) ∧ M(x,p,q,out)
```

[par_by_merge_eval](../../deps/UTP/utp_concurrency.thy#L282) gives this evaluation.
[par_by_merge_Sup_distl](../../deps/UTP/utp_concurrency.thy#L286) and [par_by_merge_Sup_distr](../../deps/UTP/utp_concurrency.thy#L290) distribute over demonic
choice; false is absorbing, and [par_by_merge_true](../../deps/UTP/utp_concurrency.thy#L298) characterises a true merge.

[par_by_merge_comm](../../deps/UTP/utp_concurrency.thy#L334) requires `M is SymMerge`.
[par_by_merge_cyclic](../../deps/UTP/utp_concurrency.thy#L383) requires `AssocMerge M` and gives

```text
(P ∥[M] Q) ∥[M] R = (Q ∥[M] R) ∥[M] P.
```

Thus [par_by_merge_assoc](../../deps/UTP/utp_concurrency.thy#L389) needs both symmetry and [AssocMerge](../../deps/UTP/utp_concurrency.thy#L215).
Alternatively, [par_by_merge_assoc_iff](../../deps/UTP/utp_concurrency.thy#L349) characterises associativity on all
relations by equality of the two merge folds. Branch and merged outputs must
share an alphabet for nesting; the prior alphabet may differ.

These laws have no operand-healthiness premises. Specialised operators must
establish them for their actual merge or transfer a law on their healthy operands.
D/AD correspondence is in [AD](AD.md#ac2pd2ac-mapping-laws);
RAD/AP use flat RD with [R3c](../../deps/UTP-Reactive-Designs/utp_rdes_healths.thy#L202), not an established D-to-RD correspondence.
