# Design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [AD](AD.md) · [RD](RD.md)

Source: [`utp_des_parallel_laws.thy`](../../deps/UTP-Designs/utp_des_parallel_laws.thy),
[`utp_des_parallel_lift.thy`](../../deps/UTP-Designs/utp_des_parallel_lift.thy) and
[`utp_des_nd.thy`](../../deps/UTP-Designs/utp_des_nd.thy).
[Shared notation](README.md#shared-notation).

We first give laws for any design merge `M`, then lift a state merge `j` to a
design merge and obtain `P ∥D[j] Q`.

## Generic merge healthiness and closure

Each design healthiness condition has a merge counterpart:

```isabelle
H1m M = M ∨ ¬ok
H2m M = M ;; J
H3m M = M ;; II_D
HDm   = H1m ∘ H2m
NDDm M = M ∧ (ok ∧ okL ∧ okR ⟶ ok')
```

[`H1m`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L19) permits any output
before start, [`H2m`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L21) cannot
require nontermination, [`H3m`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L23)
releases the output after divergence, and
[`NDDm`](../../deps/UTP-Designs/utp_des_nd.thy#L26) makes the merge result terminate if both branches terminate. All are idempotent and monotone.

The four core conditions `H1m`, `H2m`, `H3m` and `HDm` commute pairwise
without premises, so their application order does not matter
([`H1m_H2m_commute`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L29),
[remaining commutation laws](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L78)).
This does not extend to `NDDm`: from the definitions, it does not commute
with `H2m`, `H3m` or `HDm` in general; these negative results are not installed
as Isabelle lemmas.

| Law for `P ∥[M] Q` | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| `is H1` | Both `H1` | `H1m` | [`H1_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L208) |
| `is H2` | - | `H2m` | [`H2_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L213) |
| `is H3` | - | `H3m` | [`H3_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L219) |
| `is H` | Both `H1` | `HDm` | [`H_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L225) |
| `P ∥[M] Miracle =`<br>`Miracle ∥[M] P = Miracle` | `P is H1` | `H1m` | [`par_by_merge_miracle`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L234) |
| `P ∥[M] Chaos =`<br>`Chaos ∥[M] P = Chaos` | `P is H4` | a divergent branch lets `M` give any output | [`par_by_merge_chaos`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L245) |
| associative | All `NDD` | see [Generic](Generic.md#associativity-on-nondivergent-operands) | [`par_by_merge_assoc_NDD`](../../deps/UTP-Designs/utp_des_nd.thy#L72) |

## Lifted merge and laws

We lift `j` by conjoining the branch flags, then close the result under `HDm`
and `H3m`:

```isabelle
merge_des_raw j ((ok,s),(okL,sL),(okR,sR),(ok',s')) =
  (ok' = (okL ∧ okR)) ∧ j(s,sL,sR,s')

merge_des j ≡ H3m (HDm (merge_des_raw j))

P ∥D[j] Q ≡ P ∥[merge_des j] Q
```

[`merge_des_expand`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L47) unfolds it:
once a branch diverges the output is free, but a merged state must still exist.

```isabelle
merge_des j ((ok,s),(okL,sL),(okR,sR),(ok',s')) ↔
  ¬ok ∨ ((∃u. j(s,sL,sR,u)) ∧ (okL ∧ okR ⟶ ok' ∧ j(s,sL,sR,s')))
```

The lifted merge inherits these properties:

| Property of `merge_des j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `H1m` | - | [`merge_des_is_H1m`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L75) |
| `H2m` | - | [`merge_des_is_H2m`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L78) |
| `HDm` | - | [`merge_des_is_HDm`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L71) |
| `H3m` | - | [`merge_des_is_H3m`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L81) |
| `NDDm` | - | [`merge_des_NDDm`](../../deps/UTP-Designs/utp_des_nd.thy#L88) |
| `SymMerge` | `SymMerge` | [`merge_des_SymMerge`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L89) |
| `AssocMerge` | `AssocMerge`, `mergeable` | [`merge_des_AssocMerge`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L108) |

So `∥D[j]` preserves design healthiness:

| Result of `P ∥D[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `H` | Both `H1` | [`des_par_H_closure`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L161) |
| `N` | Both `H1` | [`des_par_N_closure`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L170) |
| `H3` | - | [`des_par_H3_closure`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L166) |

Its algebraic laws:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `P ∥D[j] Q = Q ∥D[j] P` | - | `SymMerge` | [`des_par_comm`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L208) |
| `(P ∥D[j] Q) ∥D[j] R =`<br>`P ∥D[j] (Q ∥D[j] R)` | - | `SymMerge`, `AssocMerge`, `mergeable` | [`des_par_assoc`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L215) |
| `(P ∥D[j] Q) ∥D[j] R =`<br>`P ∥D[j] (Q ∥D[j] R)` | All `NDD` | `SymMerge`, `AssocMerge` | [`des_par_assoc_nd`](../../deps/UTP-Designs/utp_des_nd.thy#L100) |
| `P ∥D[j] Miracle =`<br>`Miracle ∥D[j] P = Miracle` | `P is H1` | - | [`des_par_miracle`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L200) |
| `P ∥D[j] Chaos =`<br>`Chaos ∥D[j] P = Chaos` | `P is H4` | `mergeable` | [`des_par_chaos`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L185) |
| `Chaos ∥D[j] Chaos = Chaos` | - | `∀s. ∃sL sR u. j(s,sL,sR,u)` | [`des_par_chaos_chaos`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L178) |

Chaos is `true`, Miracle is `¬ok`, and `H4` means `P ;; true = true`.
The mapping laws to AD are in [AD](AD.md#ac2pd2ac-mapping-laws).
