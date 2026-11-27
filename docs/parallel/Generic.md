# Generic parallel by merge

[Parallel by merge](README.md) · [D](D.md) · [RD](RD.md) · [AD](AD.md) · [RAD](RAD.md)

Source files:

- [`utp_concurrency.thy`](../../deps/UTP/utp_concurrency.thy)
- [`utp_concurrency_assoc.thy`](../../deps/UTP/utp_concurrency_assoc.thy)

[Shared notation](README.md#shared-notation).

Parallel by merge (UTP book, Chapter 7),
[`par_by_merge`](../../deps/UTP/utp_concurrency.thy#L268), runs `P` and `Q` from the same
prior, keeps their outputs apart in a merge record
([`par_sep`](../../deps/UTP/utp_concurrency.thy#L260)), and lets a merge predicate `M`
combine them ([`par_by_merge_eval`](../../deps/UTP/utp_concurrency.thy#L319)):

```isabelle
(P ∥[M] Q)(x,z) ↔ ∃p q. P(x,p) ∧ Q(x,q) ∧ M(x,p,q,z)
```

## Merges

A merge reads a record of the prior, left and right observations.

- [`mrg`](../../deps/UTP/utp_concurrency.thy#L24): the record type.
- [`merge`](../../deps/UTP/utp_concurrency.thy#L47): merges whose three parts and output
  share one alphabet.
- [`merge_eval`](../../deps/UTP/utp_concurrency.thy#L53): writes `M(x,p,q,z)`.
- [`mergeable`](../../deps/UTP/utp_concurrency.thy#L64): some output always exists.
- [`Functional`](../../deps/UTP/utp_rel.thy#L264): at most one output exists;
  [`Functional_merge_eval`](../../deps/UTP/utp_concurrency.thy#L72) states `Functional` with `merge_eval`.
- [`skip_m`](../../deps/UTP/utp_concurrency.thy#L105): returns the prior.
- [`swap_m`](../../deps/UTP/utp_concurrency.thy#L116): swaps the two branches.

## Parallel operator

| Property | Merge premise | Lemmas |
| --- | --- | --- |
| monotone | - | [`par_by_merge_mono`](../../deps/UTP/utp_concurrency.thy#L370); one argument at a time: [`par_by_merge_mono_left`](../../deps/UTP/utp_concurrency.thy#L355), [`par_by_merge_mono_right`](../../deps/UTP/utp_concurrency.thy#L360), [`par_by_merge_mono_merge`](../../deps/UTP/utp_concurrency.thy#L365) |
| distributes over `∨` | - | [`par_by_merge_disj_distl`](../../deps/UTP/utp_concurrency.thy#L332), [`par_by_merge_disj_distr`](../../deps/UTP/utp_concurrency.thy#L337) |
| distributes over `⊓` of a set | - | [`par_by_merge_Sup_distl`](../../deps/UTP/utp_concurrency.thy#L323), [`par_by_merge_Sup_distr`](../../deps/UTP/utp_concurrency.thy#L327) |
| subdistributes over `∧` | - | [`par_by_merge_conj_subdistl`](../../deps/UTP/utp_concurrency.thy#L345), [`par_by_merge_conj_subdistr`](../../deps/UTP/utp_concurrency.thy#L350) |
| commutative | `M is SymMerge` | [`par_by_merge_comm`](../../deps/UTP/utp_concurrency.thy#L414) |
| associative | `M is SymMerge`, `AssocMerge M` | [`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30) |

Each distribution law has a left and a right form. Conjunction only subdistributes,
since the two parallels on the left may use different observations of the shared
operand.

## Symmetry and associativity

[`SymMerge_eval`](../../deps/UTP/utp_concurrency.thy#L403) and [`AssocMerge_iff`](../../deps/UTP/utp_concurrency_assoc.thy#L15) state the merge premises:

```isabelle
(* we can swap the positions of p and q branches *)
M is SymMerge ↔ (∀x p q z. M(x,p,q,z) ↔ M(x,q,p,z))

(* merging p,q then r gives the same z as merging q,r then p;
   with u being the intermediate merge result *)
AssocMerge M ↔ ∀x p q r z.
    (∃u. M(x,p,q,u) ∧ M(x,u,r,z))
  ↔ (∃u. M(x,q,r,u) ∧ M(x,u,p,z))
```

[`AssocMerge`](../../deps/UTP/utp_concurrency.thy#L252) itself is defined by rotating
the inputs of a three-way merge, hence the cyclic form.

## Associativity on nondivergent operands

`par_by_merge_assoc` needs `AssocMerge M` at every observation. Some design merges
fail `AssocMerge` when a branch diverges. A branch diverges when the branch starts
(`ok`) but does not terminate (`okL` or `okR` false). `H3m` then allows any output, yet the two bracketings can differ. Take
`P` diverging in state `sP`, with `Q` and `R` terminating in `sQ` and `sR`:

- D: the [lifted merge](D.md#the-lifted-merge) gives any output after a
  divergence, but only if some merged state exists, `∃u. j(s,sL,sR,u)`. So
  `(P ∥ Q) ∥ R` checks that `sP` merges with `sQ`, while `P ∥ (Q ∥ R)` checks that
  `sP` merges with the merge of `sQ` and `sR`. With a partial `j`, one check can pass
  while the other fails. With a `mergeable` `j` both pass, so `par_by_merge_assoc`
  applies to all operands
  ([`des_par_assoc`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L215)).
- RD: completion lets a divergent result end with any extension of the merged trace.
  In `(P ∥ Q) ∥ R` the intermediate result diverges, so the intermediate trace may
  grow before meeting `R`. In `P ∥ (Q ∥ R)` the intermediate result terminates, so the
  intermediate trace cannot grow. The
  two agree only when `j` absorbs extensions ([RD](RD.md#symmetry-and-associativity)).

For such merges, we ask for `AssocMerge` only on nondivergent observations, and for
nondivergent operands in return.

[`merge_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L41) restricts a merge to branches that satisfy a guard `G`:

```isabelle
merge_guard G M (x,p,q,z) = G(x,p) ∧ G(x,q) ∧ M(x,p,q,z)
```

[`par_by_merge_assoc_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L75) gives
`(P ∥[M] Q) ∥[M] R = P ∥[M] (Q ∥[M] R)` when:

- `merge_guard G M` is symmetric and associative;
- `M` preserves `G`: guarded branches merge to a guarded output;
- every observation of `P`, `Q` and `R` satisfies `G`.

Each model guide states the instance for that model's nondivergence guard:

- [D](D.md#symmetry-and-associativity):
  [`par_by_merge_assoc_NDD`](../../deps/UTP-Designs/utp_des_nd.thy#L72);
- [RD](RD.md#symmetry-and-associativity):
  [`par_by_merge_assoc_NDRD`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy#L526),
  which [RAD](RAD.md#correspondence-with-rd) transfers through `p2ac`;
- [AD](AD.md#symmetry-and-associativity) and [RAD](RAD.md#symmetry-and-associativity): the
  laws for a `Functional` `j` off A2.

RD and RAD also have laws for normal operands, which may diverge (`NRD`, the
reactive analogue of H3); see [RD](RD.md#the-lifted-merge).
