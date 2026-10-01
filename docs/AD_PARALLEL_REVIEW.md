# Historical AD parallel review

> This review records the earlier pointwise implementation on `main`.
> It does not describe the current branch, which now uses only the
> [conjunction-based merge](AD_PARALLEL.md). The validation record below
> applies to its stated historical revision.

This records the AD review accepted on `main`. This branch additionally
contains RAD/AP WIP; see [branch contents](RESEARCH_BOUNDARY.md).

The AD parallel extension is separate from the paper coverage claim. It adds
choice-set merge lifting, healthiness results, a relational design form,
conditional algebraic laws and examples. RAD/AP parallel remain work in
progress on `research/parallel`.

## Meaning of the operator

`ades_merge_image` applies a state merge to each pair of branch results,
using the same prior state. `merge_ades` requires the output choice set to be
exactly this image; `merge_ades_up` allows any choice set containing it.
Both conjoin the branch termination flags.

The public `ades_par` uses the upward lifting. `PBMH_ades_par_raw` proves
that this is exactly PBMH closure of parallel with the exact lifting.
The relational design form retains both output-sensitive failure components;
a simple conjunction of the operand preconditions would not be valid in
general.

## Guarantees and assumptions

| Result | Premises |
| --- | --- |
| PBMH closure | None |
| H1, H2, H closure | Both operands have the corresponding healthiness |
| A1 closure | Both operands are H-healthy |
| A0 closure | Both operands are A0-healthy; `A0j j` |
| A closure | Both operands are A-healthy; `A0j j` |
| A2 closure | Both operands are A2-healthy; `A2j j` |
| A3 via the merge | Both operands are H-healthy; `A3j j` |
| A3, H3 and N via normal operands | Both operands are N-healthy; arbitrary merge |
| Commutativity | `swap_m ;; j = j` |
| Associativity | `swap_m ;; j = j` and `AssocMerge j` |

`A0j` means totality; `A2j` means at most one merged result. A2 closure needs
neither totality nor H-healthiness. The total nondeterministic merge
counterexample shows why totality alone is insufficient at the relation
level; it does not establish that `A2j` is necessary.

`A3j` excludes some exact singleton image at each prior state. Its element
may still occur in a larger image. Under totality,
`ades_par_A3_closure_iff_A3j` characterises A3 for **every pair of H-healthy
operands**. It makes no necessity claim for individual pairs, for the class
of A3-healthy operands alone, or for partial merges.

Normal operands provide a separate A3 guarantee for arbitrary merges because
the calculated precondition is independent of the output choices. This does
not remove totality from the A-closure theorem. Associativity likewise keeps
both symmetry and `AssocMerge`; no arbitrary-merge or sequential
associativity claim is made.

## Examples

For nonempty branch choice sets, `skip_m` returns the prior state and
`ades_right_merge` returns the right choice set. Both are total and
functional. `skip_m` satisfies `A3j` when there are at least two states;
the right merge fails `A3j`, but its normal assignment examples still satisfy
A3 through the normal-operand theorem.

The `{3,4,99}` example is accepted by the upward lift and rejected by the
exact `{3,4}` lift. `skip_m` is a merge policy, not a parallel identity law
for arbitrary operands.

## Names and source boundary

The established operator names and notation are retained. Fact names now
make the merge, property or additional premise explicit:

| Earlier name | Current name |
| --- | --- |
| `ades_merge_total` | `A0j` |
| `ades_par_by_merge` | `ades_par` |
| `ades_par_by_merge_*` facts | Corresponding `ades_par_*` facts |
| `PBMH_ades_par_by_merge_raw` | `PBMH_ades_par_raw` |
| `ades_par_PBMH_ades` | `ades_par_is_PBMH_ades` |
| `A0j_upclosed`, `A2j_downclosed` | `A0j_enlarge`, `A2j_restrict` |
| `A0j_skip_merge`, `A2j_skip_merge`, `A3j_skip_merge` | `skip_merge_A0j`, `skip_merge_A2j`, `skip_merge_A3j` |
| `ades_par_A3_iff_A3j` | `ades_par_A3_closure_iff_A3j` |
| `ades_par_H3_closure` | `ades_par_normal_H3_closure` |

`ades_par_PBMH_ades` remains an alias for the existing RAD WIP caller.
Other renamed facts have no compatibility aliases. External callers must
use the corresponding new names.

Only three theory files change: `utp_ades_parallel`, `utp_ades_core` and
`utp_ades_healthy`, all in `angelic-designs/`. Support comprises
`arel_not_applied`, `arel_indep_A3_rel`, `H_A3_intro`, `N_preD_indep` and
`A0_healthy_non_empty`; the last moves from the parallel theory into
`utp_ades_healthy` and changes its qualified namespace.

The existing exact-lift symmetry law `merge_ades_swap` is retained. The
naming pass changes no definitions, theorem statements or proof arguments.
Stable RAD/AP sources, session registrations, dependency pins and paper
coverage are unchanged from `4fcd5d9`.

## Validation

The committed theory revision `3300bf9` passed Isabelle2025-2 on 8 September
2026 using the separate `utp-cleanup-2026-09-08` profile. All three project
sessions and `Sequential_Composition_Audit` rebuilt successfully; the
subsequent no-build freshness check also returned exit 0.

Validation used an export of the committed sources and dependency files
checked against the unchanged pins. Reversing the eight fact renames and
removing the compatibility alias exactly reproduces the earlier reviewed
AD parallel source. Source hashes were unchanged by validation, and
`git diff --check` passed. No unfinished proofs or added axioms are present
in the changed theories.

To reproduce from a checkout with its pinned dependencies, set `ISABELLE`
to the Isabelle2025-2 executable and run from the repository root:

```bash
env ISABELLE_IDENTIFIER=utp-cleanup-2026-09-08 PROJECT_DIR="$PWD" \
  "$ISABELLE" build -b -d deps -d . -d audits/seq-associativity \
  -o system_heaps=false -o threads=4 \
  UTP-Angelic-CSP Sequential_Composition_Audit
```

Replace `-b` with `-n` for freshness. The paper-only snapshot was not rebuilt
for this integration; see [baseline checks](BASELINE.md) for its earlier
validation. Local logs, manifests and preservation records are retained in
the cleanup backup under `ad-parallel-integration/`.
