# Design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [AD](AD.md) · [RD](RD.md)

Source files:

- [`utp_des_parallel_laws.thy`](../../deps/UTP-Designs/utp_des_parallel_laws.thy)
- [`utp_des_parallel_lift.thy`](../../deps/UTP-Designs/utp_des_parallel_lift.thy)
- [`utp_des_nd.thy`](../../deps/UTP-Designs/utp_des_nd.thy)

[Shared notation](README.md#shared-notation).

We lift a state merge `j` to a design merge to obtain `P ∥D[j] Q`, and give each
law for any design merge `M`, with its instance for `∥D[j]`. The mapping laws to AD
are in [AD](AD.md#correspondence-with-designs).

- [Merge conditions](#merge-conditions)
- [The lifted merge](#the-lifted-merge)
- [Closure](#closure)
- [Symmetry and associativity](#symmetry-and-associativity)
- [Zero laws](#zero-laws)

## Merge conditions

Each design healthiness condition has a merge counterpart:

```isabelle
H1m M = M ∨ ¬ok
H2m M = M ;; J
H3m M = M ;; II_D
HDm   = H1m ∘ H2m
NDDm M = M ∧ (ok ∧ okL ∧ okR ⟶ ok')
```

- [`H1m`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L19): any output is allowed
  before start.
- [`H2m`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L21): the merge cannot
  require nontermination.
- [`H3m`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L23): any output is allowed
  after a divergence.
- [`NDDm`](../../deps/UTP-Designs/utp_des_nd.thy#L26): the merge result terminates if
  both branches terminate.

All five conditions are idempotent and monotone.

The four core conditions `H1m`, `H2m`, `H3m` and `HDm` commute pairwise
without premises, so their application order does not matter
([`H1m_H2m_commute`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L29),
[remaining commutation laws](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L78)).
This does not extend to `NDDm`: from the definitions, `NDDm` does not commute
with `H2m`, `H3m` or `HDm` in general; these negative results are not installed
as Isabelle lemmas.

## The lifted merge

We lift `j` by conjoining the branch flags, then close the result under `HDm`
and `H3m`:

```isabelle
merge_des_raw j ((ok,s),(okL,sL),(okR,sR),(ok',s')) =
  (ok' = (okL ∧ okR)) ∧ j(s,sL,sR,s')

merge_des j ≡ H3m (HDm (merge_des_raw j))

P ∥D[j] Q ≡ P ∥[merge_des j] Q
```

[`merge_des_expand`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L47) unfolds
`merge_des j`: once a branch diverges, any output is allowed, but a merged state must
still exist.

```isabelle
merge_des j ((ok,s),(okL,sL),(okR,sR),(ok',s')) ↔
  ¬ok ∨ ((∃u. j(s,sL,sR,u)) ∧ (okL ∧ okR ⟶ ok' ∧ j(s,sL,sR,s')))
```

## Closure

Each closure rule holds for any `M` that satisfies its merge premises. For every
`j`, `merge_des j` satisfies each merge premise, which gives the closure law for
`∥D[j]`:

| `P ∥[M] Q` is | Operand premises | Merge premises | Lemma | `merge_des j` | `P ∥D[j] Q` |
| --- | --- | --- | --- | --- | --- |
| `H1` | Both `H1` | `H1m` | [`H1_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L208) | [`merge_des_is_H1m`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L75) | - |
| `H2` | - | `H2m` | [`H2_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L213) | [`merge_des_is_H2m`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L78) | - |
| `H3` | - | `H3m` | [`H3_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L219) | [`merge_des_is_H3m`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L81) | [`des_par_H3_closure`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L166) |
| `H` | Both `H1` | `HDm` | [`H_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L225) | [`merge_des_is_HDm`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L71) | [`des_par_H_closure`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L161) |

`∥D[j]` also preserves normality, by the `H1` and `H3` rows:

| Result of `P ∥D[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `N` | Both `H1` | [`des_par_N_closure`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L170) |

## Symmetry and associativity

With premises on `j`, the lifted merge has these properties:

| Property of `merge_des j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `NDDm` | - | [`merge_des_NDDm`](../../deps/UTP-Designs/utp_des_nd.thy#L88) |
| `SymMerge` | `SymMerge` | [`merge_des_SymMerge`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L89) |
| `AssocMerge` | `AssocMerge`, `mergeable` | [`merge_des_AssocMerge`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L108) |

Each law holds for any `M` with the merge premises, and for `∥D[j]` with the
premises on `j`:

| Law for $P \parallel_M Q$ | Operand premises | Merge premises | Lemma | Premises on `j` | `P ∥D[j] Q` |
| --- | --- | --- | --- | --- | --- |
| $P \parallel_M Q = Q \parallel_M P$ | - | `M is SymMerge` | [`par_by_merge_comm`](../../deps/UTP/utp_concurrency.thy#L414) | `SymMerge` | [`des_par_comm`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L208) |
| $(P \parallel_M Q) \parallel_M R =$<br>$P \parallel_M (Q \parallel_M R)$ | - | `M is SymMerge`, `AssocMerge M` | [`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30) | `SymMerge`, `AssocMerge`, `mergeable` | [`des_par_assoc`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L215) |
| $(P \parallel_M Q) \parallel_M R =$<br>$P \parallel_M (Q \parallel_M R)$ | All `NDD` | `M is SymMerge`, `M is NDDm`, `AssocMerge (merge_guard G_D M)` | [`par_by_merge_assoc_NDD`](../../deps/UTP-Designs/utp_des_nd.thy#L72) | `SymMerge`, `AssocMerge` | [`des_par_assoc_nd`](../../deps/UTP-Designs/utp_des_nd.thy#L100) |

The `NDD` associativity row instantiates
[`par_by_merge_assoc_guard`](Generic.md#associativity-on-nondivergent-operands) with the
nondivergence guard `λx z. ok x ⟶ ok z`, written inline in the lemma; this guide
calls the guard `G_D`. `NDD` operands satisfy `G_D`, and `NDDm` makes the merge
preserve `G_D`.

## Zero laws

| Law for $P \parallel_M Q$ | Operand premises | Merge premises | Lemma | Premises on `j` | `P ∥D[j] Q` |
| --- | --- | --- | --- | --- | --- |
| $P \parallel_M \mathit{Miracle} =$<br>$\mathit{Miracle} \parallel_M P = \mathit{Miracle}$ | `P is H1` | `H1m` | [`par_by_merge_miracle`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L234) | - | [`des_par_miracle`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L200) |
| $P \parallel_M \mathit{Chaos} =$<br>$\mathit{Chaos} \parallel_M P = \mathit{Chaos}$ | `P is H4` | `¬okL ∨ ¬okR ⟶ M(x,p,q,z)` | [`par_by_merge_chaos`](../../deps/UTP-Designs/utp_des_parallel_laws.thy#L245) | `mergeable` | [`des_par_chaos`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L185) |

For `∥D[j]`, Chaos is also idempotent:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| $\mathit{Chaos} \parallel_{D[j]} \mathit{Chaos} = \mathit{Chaos}$ | - | `∀s. ∃sL sR u. j(s,sL,sR,u)` | [`des_par_chaos_chaos`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L178) |

Chaos is `true`, Miracle is `¬ok`, and `H4` means `P ;; true = true`.
