# Generic parallel by merge

[Parallel by merge](README.md) · [D](D.md) · [RD](RD.md) · [AD](AD.md) · [RAD](RAD.md)

Source: [`utp_concurrency.thy`](../../deps/UTP/utp_concurrency.thy) and
[`utp_concurrency_assoc.thy`](../../deps/UTP/utp_concurrency_assoc.thy).
[Shared notation](README.md#shared-notation).

Parallel by merge (UTP book, Chapter 7) runs `P` and `Q` from the same prior,
keeps their outputs apart, and lets a merge predicate `M` combine them:

```isabelle
(P ∥[M] Q)(x,z) ↔ ∃p q. P(x,p) ∧ Q(x,q) ∧ M(x,p,q,z)
```

## Merges

A merge reads a record [`mrg`](../../deps/UTP/utp_concurrency.thy#L24) of the prior,
left and right observations; [`merge`](../../deps/UTP/utp_concurrency.thy#L47) is the
type of merges whose three parts and output share one alphabet.
[`merge_eval`](../../deps/UTP/utp_concurrency.thy#L53) writes `M(x,p,q,z)`, and
[`mergeable`](../../deps/UTP/utp_concurrency.thy#L64) says some output always exists.
UTP's [`Functional`](../../deps/UTP/utp_rel.thy#L264) says at most one output exists;
[`Functional_merge_eval`](../../deps/UTP/utp_concurrency.thy#L72) states it with `merge_eval`.
[`skip_m`](../../deps/UTP/utp_concurrency.thy#L105) returns the prior, and
[`swap_m`](../../deps/UTP/utp_concurrency.thy#L116) swaps the two branches.

## Separating simulations

`U0` and `U1` rename an operand's outputs into the left and right parts of
the record, written `⌈P⌉₀` and `⌈Q⌉₁`. Most of this section is renaming and
substitution laws for them.

## Parallel operator

[`par_sep`](../../deps/UTP/utp_concurrency.thy#L260) runs both operands into a merge
record, and [`par_by_merge`](../../deps/UTP/utp_concurrency.thy#L268) composes it with `M`:

```isabelle
P ∥[M] Q = (P ∥s Q) ;; M
```

The theory then gives unrestriction and substitution laws, and the basic
algebra: [`par_by_merge_eval`](../../deps/UTP/utp_concurrency.thy#L319) is the evaluation
above, false is absorbing, and a skip merge of feasible operands is `II`.

Parallel distributes over disjunction on either side
([`par_by_merge_disj_distl`](../../deps/UTP/utp_concurrency.thy#L332), [`par_by_merge_disj_distr`](../../deps/UTP/utp_concurrency.thy#L337)), and over `⊓` of
a set ([`par_by_merge_Sup_distl`](../../deps/UTP/utp_concurrency.thy#L323), [`par_by_merge_Sup_distr`](../../deps/UTP/utp_concurrency.thy#L327)). Conjunction only
subdistributes, since the two parallels on the left may use different observations of the
shared operand ([`par_by_merge_conj_subdistl`](../../deps/UTP/utp_concurrency.thy#L345),
[`par_by_merge_conj_subdistr`](../../deps/UTP/utp_concurrency.thy#L350)):

```isabelle
P ∥[M] (Q ∨ R) = (P ∥[M] Q) ∨ (P ∥[M] R)
(P ∥[M] Q) ∧ (P ∥[M] R) ⊑ P ∥[M] (Q ∧ R)
```

Parallel is monotone in each operand and in the merge
([`par_by_merge_mono_left`](../../deps/UTP/utp_concurrency.thy#L355),
[`par_by_merge_mono_right`](../../deps/UTP/utp_concurrency.thy#L360),
[`par_by_merge_mono_merge`](../../deps/UTP/utp_concurrency.thy#L365)), and so in all three
together ([`par_by_merge_mono`](../../deps/UTP/utp_concurrency.thy#L370)):

```isabelle
P ⊑ P' ∧ Q ⊑ Q' ∧ M ⊑ M' ⟹ P ∥[M] Q ⊑ P' ∥[M'] Q'
```

## Symmetry and associativity

[`SymMerge_eval`](../../deps/UTP/utp_concurrency.thy#L403) and
[`par_by_merge_comm`](../../deps/UTP/utp_concurrency.thy#L414):

```isabelle
(* we can swap the positions of p and q branches *)
M is SymMerge ↔ (∀x p q z. M(x,p,q,z) ↔ M(x,q,p,z))
M is SymMerge ⟹ P ∥[M] Q = Q ∥[M] P
```

[`AssocMerge_iff`](../../deps/UTP/utp_concurrency_assoc.thy#L15) and
[`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30):

```isabelle
(* merging p,q then r gives the same z as merging q,r then p;
   with u being the intermediate merge result *)
AssocMerge M ↔ ∀x p q r z.
    (∃u. M(x,p,q,u) ∧ M(x,u,r,z))
  ↔ (∃u. M(x,q,r,u) ∧ M(x,u,p,z))

M is SymMerge ∧ AssocMerge M ⟹ (P ∥[M] Q) ∥[M] R = P ∥[M] (Q ∥[M] R)
```

[`AssocMerge`](../../deps/UTP/utp_concurrency.thy#L252) itself is defined by rotating
the inputs of a three-way merge, hence the cyclic form.

## Associativity on nondivergent operands

The parallel merges of designs (D, RD, AD, RAD) are usually not associative
once an operand may diverge, so we prove associativity for nondivergent operands.
[`merge_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L41) `G M` keeps only branches
satisfying `G`, and [`par_by_merge_assoc_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L75)
gives associativity when the guarded merge is symmetric and associative, `M`
preserves `G`, and every operand satisfies `G`.

Each model instantiates `G` with its nondivergence guard:

```isabelle
G_D  x z = (ok x ⟶ ok z)
G_RD x z = (ok x ∧ ¬wait x ⟶ ok z)
```

| Model | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| D | NDD | `M is SymMerge`, `M is NDDm`, `AssocMerge (merge_guard G_D M)` | [`par_by_merge_assoc_NDD`](../../deps/UTP-Designs/utp_des_nd.thy#L72) |
| RD | RD, NDRD | `M is SymMerge`, `M is NDRDm`, `AssocMerge (merge_guard G_RD M)` | [`par_by_merge_assoc_NDRD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L533) |
| RAD over `rad_lift_merge M` | RAD, A2, NDRAD | The RD premises on `M` | [`par_by_rad_lift_merge_assoc_NDRAD`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L442) |

The merges built from `j` meet these premises when `j is SymMerge` and
`AssocMerge j`.
AD reuses the D law through `ac2p`; see [AD](AD.md#lifted-merge-and-laws).
