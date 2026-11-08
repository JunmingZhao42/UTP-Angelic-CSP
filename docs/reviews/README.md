# Stage log

One entry per finished stage: what changed and how it was checked. Open work is
in [PLAN.md](../../PLAN.md). Each stage's full write-up and raw evidence (PIDE
snapshots, batch logs, hashes and patches) are kept locally in
`audits/reviews/<date>-<stage>/`, which is gitignored.

The full build runs outside the sandbox, because Isabelle's startup `sysctl`
call is blocked inside it:

```sh
ISABELLE=/Applications/Isabelle2025-2.app/bin/isabelle UTP_PROFILE=utp-2025-2 \
  ./scripts/fullbuild.sh -v -o threads=2
```

## Open explorations

Scratch work behind optional PLAN Stage 1 research (necessity and commutation
of the merge conditions), outside the completed generic closure requirement.
Both interfaces were installed on 2 November 2026 under new names; the
scratch files keep the old names and no longer load against the current theory.

- [Generic AD closure rules](2026-10-30-ad-generic-closure-exploration/README.md)
  for an arbitrary merge `M`.
- [AD merge transformers](2026-10-30-ad-merge-healthiness/README.md), now `A2m`
  and, split, `A0m` and `A1m`.

## Stage 0a: baseline audit

30 October 2026, at `8aaa682` on `research/parallel2` with uncommitted work.

- The full build, the paper-only build and the freshness check passed. PIDE
  checked all 25 first-party and 15 RD dependency theories with zero errors.
  No theory or ML file changed.
- The paper audit compared 157 indexed items at statement level. The resulting
  guide corrections are tracked in
  [issue #1](https://github.com/JunmingZhao42/UTP-Angelic-CSP/issues/1); the
  remaining follow-ups are PLAN Stage 0b items.
- The two historical audits in `audits/` do not replay: the AD parallel audit
  times out, and the sequential audit fails at `eval_Stop_AP` on an obsolete
  record selector. Recheck them before relying on their claims.

## Stage 0b: dependency publication

30 October 2026.

- `deps/UTP` at `4493ca4` and `deps/UTP-Designs` at `b8967c4` are on the `main`
  branches of the user's forks; fresh fetches matched their commit and tree IDs.
  Tag `design-parallel-presquash` keeps `7e13304`, whose tree equals `b8967c4`.
- `.gitmodules` now points UTP-Designs at the fork. The fork's `bad-main` and
  `pred` branches were deleted; deleting them upstream was refused for lack of
  write access. A bundle of every pre-cleanup ref is at
  `deps/UTP-Designs/.git/audit-backups/2026-10-30-before-branch-cleanup.bundle`.

## Stage 0c: design parallel closure

31 October 2026.

- Installed `H3_par_by_merge` (premise `M is H3m`), the H1-weakened
  `H_par_by_merge`, `merge_des_is_H3m`, and `des_par_H3_closure`,
  `des_par_H_closure` and `des_par_N_closure`; see the
  [D guide](../parallel/D.md#healthiness-closure).
- Same-day follow-ups removed the redundant `par_by_merge_completion` and
  replaced `merge_des_completion` by `merge_des_is_H3m`. The literal
  `merge_des j is H3` is ill-typed: H3 expects a design relation, not a merge.
- The full build passed (8 min 13 s) before the follow-ups, and targeted
  UTP-Designs builds passed after each. PIDE was clean for the concurrency,
  design parallel and AD parallel theories.

## Stage 1: AD recipe and closure

30 October 2026. Each slice passed PIDE with zero errors and a batch build.

- **Recipe:** `merge_ades j ≡ ADH1m (ades_lift_merge j) ;; II_D`, with
  unconditional `merge_ades_ADH1m`, `merge_ades_ADH2m`, `merge_ades_ADHM` and
  `merge_ades_completion`. Equality with the old `ADHM (lift_merge j)` was
  proved for every `j` as `stage1_alt`, kept in
  [scratch.thy](2026-10-30-stage-1-recipe/scratch.thy). It uses the removed
  `lift_merge`, so it no longer loads against the current theory.
- **A2-only closure:** `ades_par_lifted_A2_closure` and `ades_par_A2_closure`
  need only A2 operands, with no premise on `j`.
- **Symmetry and associativity:** `merge_ades_SymMerge` and `ades_par_comm`
  assume `j is SymMerge` and nothing of the operands. Through
  `ades_par_normalise_A`, `ades_par_assoc` now needs A2 rather than A on all
  three operands, plus `j is SymMerge`, `AssocMerge j` and `mergeable j`.
- **Lifting cleanup:** `lift_merge_raw` was renamed `ades_lift_merge`, and the
  old `lift_merge`, `lift_merge_obs` and `merge_ades_alt_def` were removed.
  Theorem statements are unchanged.
- **ADH3m:** `ADH3m M ≡ M ;; II_D`, with unconditional `ADH3m_idem` and
  `merge_ades_ADH3m`. It is distinct from angelic A3.

## Stage 1: generic AD closure interface

2 November 2026, on top of `5e76186`. Names above this entry are the old ones.

- **Shared design conditions:** D's `H1m`, `H2m`, `H3m` and `HDM`, and the
  `H1/H2/H3/H_par_by_merge` rules, now allow merges whose prior, branch and
  output alphabets differ. AD dropped `ADH1m`, `ADH2m`, `ADH3m`, `ADHM` and their
  seven lemmas and uses D's; `merge_ades_ADHxm` became `merge_ades_is_Hxm`.
- **Angelic conditions and rules:** `merge_slice`, `merge_health`, `Am`, `A2m`, `A_par_by_merge`, `A2_par_by_merge`,
  `A3_par_by_merge`, `merge_ades_is_Am` and `merge_ades_is_A2m`, ported from the
  two 30 October explorations. The lifted closures are now corollaries. New
  helpers: `H3_obs` in the AD core and `H1_H3_impl_A3` in AD healthiness.
- **Explicit definitions:** `A2m` (and `A0m`, `A1m` below) are defined explicitly, like `H1m`;
  `A2m` is one expression, with no helper definitions. Its lemmas are only
  `A2m_obs`, `A2m_Idempotent` and `A2m_Monotonic`: `A2m_fixed`, `A2m_idem`,
  `A2m_mono` and
  `singleton_slice_A2_iff` were removed, and `A2_par_by_merge` and
  `merge_ades_is_A2m` use `A2m_obs` directly. `ades_merge_ext` (equality from
  merge observations) sits with the slice lemmas. The A2 rule's helpers
  `A2_nonempty_singleton`, `A2_singleton_witness` and
  `ades_par_by_merge_singletons` were folded into `A2_par_by_merge` and
  `ades_par_lifted_obs_A2` as local facts.
  `H1m_merge_health`, `H2m_merge_health`, `H3m_merge_health`,
  `HDM_merge_health`, `A0m_merge_health` and `A1m_merge_health` show that each
  condition applies H1, H2, H3, **H**, A0 or A1 to every slice of an AD merge.
- **A split:** `Am` was replaced by `A0m` and `A1m`, defined explicitly.
  `A0_par_by_merge` needs no operand premise and `A1_par_by_merge` needs H1
  operands; `A_par_by_merge` now assumes `M is A0m` and `M is A1m` and follows
  from the two. `merge_ades_is_Am` became `merge_ades_is_A0m` and
  `merge_ades_is_A1m`. The generic `merge_health_slices`, `merge_health_idem`
  and `merge_health_mono` replace `Am_slices`, `Am_idem` and `Am_mono`.
- **Layout:** `utp_ades_parallel.thy` follows D's order: merge observations,
  merge healthiness, generic closure, lifting, AD parallel, correspondence,
  algebraic laws, skip example. Downstream theories needed no change.
- **Checks:** PIDE reported zero errors for D's parallel theory and all five AD
  theories. The UTP-Designs and RD heaps were rebuilt with the change, and the
  full build then passed for AD, RAD and CSP (2 min 24 s, two threads).
  After the `A2m` cuts and the folding of the A2 helpers, PIDE again reported
  zero errors for the AD parallel theory, and the full build passed for AD, RAD
  and CSP (1 min 25 s, two threads). After the A split and the removal of `Am`,
  PIDE reported zero errors and warnings for the AD parallel theory, and the full
  build passed (1 min 39 s, two threads); again after folding `A2m_idem` and
  `A2m_mono` (1 min 23 s).

## Stage 1: generic AD closure cleanup

3 November 2026.

- Removed the unused D-to-slice bridges and the general `merge_health`
  framework. `A0m_slices` and `A1m_slices` now give the direct fixed-point
  characterisations used by the closure and constructed-merge proofs.
- Retained all five AD closure rules and the three angelic transformers'
  monotonicity and idempotence results. Merge conditions and the closure,
  correspondence and algebraic-law statements and premises are unchanged.
- Generic healthiness closure is complete. Necessity and transformer
  compatibility remain optional research in PLAN Stage 1.
- **Checks:** PIDE finished all 780 commands in the AD parallel theory with
  zero errors, warnings, bad, failed or unprocessed commands. Separately, the
  full-project batch build passed, rebuilding AD, RAD and CSP (1 min 59 s,
  two threads). All 57 retained lemma statements and all remaining definitions
  match the pre-cleanup source; the documentation link check passed.

## Stage 1: shared generic parallel laws

3 November 2026.

- Moved `par_by_merge_assoc_iff`, `AssocMerge_iff_eval` and
  `par_by_merge_assoc_iff_AssocMerge` from RD to UTP's `utp_concurrency.thy`.
  Prior and branch/output alphabets may now differ. Added the direct
  `par_by_merge_assoc` corollary with symmetry and `AssocMerge` premises.
- Generalised `merge_eval`; consolidated `par_by_merge_eval`,
  `SymMerge_eval`, `AssocMerge_eval` and `par_by_merge_SUP_left/right` in the
  same theory. Removed their RD/RAD copies and the AD evaluation and symmetry
  specialisations. RD's completed-merge criteria and RAD's associativity
  proofs reuse the shared laws; AD uses the generic laws directly at its type.
- Kept the specialised closure, correspondence and algebraic-law statements
  and premises. Generic associativity of an arbitrary AD merge does not
  assert `AssocMerge (merge_ades j)` for the constructed merge.
- **Checks:** PIDE finished all six modified theories and the existing RD
  associativity tests with zero errors, warnings, bad or unfinished commands.
  All 151 retained RD/AD/RAD lemma statements are unchanged. The full-project
  batch build passed on the final sources: UTP, D, reactive, RD and AD rebuilt
  before a source-digest restart; RAD and CSP rebuilt in the successful final
  invocation (1 min 4 s, two threads). Documentation links and whitespace
  checks passed.

## Stage 1: fold redundant associativity corollaries

3 November 2026.

- Removed `par_by_merge_assoc_iff_AssocMerge` and `AssocMerge_eval`.
  `par_by_merge_assoc` now combines `par_by_merge_assoc_iff` and
  `AssocMerge_iff_eval` directly. RD's completed-merge equivalence and RAD's
  associativity proof use those same criteria without the removed corollaries.
- Retained the statements and premises of `par_by_merge_assoc`,
  `rdes_parallel_assoc_iff` and `rad_par_assoc`; updated the guides and plan.
- **Checks:** PIDE finished all three modified theories and the existing RD
  associativity tests with zero errors, warnings, bad or unfinished commands.
  All 117 retained lemma statements are unchanged. The full-project batch
  rebuild passed through UTP, D, reactive, RD, AD, RAD and CSP (14 min 10 s,
  two threads). Documentation links and whitespace checks passed.

## UTP: cyclic parallel law

3 November 2026.

- Installed `par_by_merge_cyclic` in `utp_concurrency.thy` with the sole
  premise `AssocMerge M`. Its fold argument remains local to the proof.
  Updated the shared-law guide to distinguish cyclic invariance from ordinary
  reassociation and explain the role of symmetry.
- Validation is restricted to UTP at the user's request; downstream proof
  replay and batch builds are deferred until explicitly requested.
- **Checks:** PIDE finished all 384 commands in `utp_concurrency.thy` with
  zero errors, warnings, bad or unfinished commands. All 43 existing lemma
  statements are unchanged. Documentation links and whitespace checks passed.
  No batch build was run.

## Remove the unused generic fold equivalence

3 November 2026.

- Removed `AssocMerge_iff_eval` from UTP. RD retains its exact completed-merge
  equivalence using a proof-local argument over an abstract merge. RAD derives its fold premise
  from `par_by_merge_assoc` and `par_by_merge_assoc_iff`; the existing RD
  test uses the retained completed-merge equivalence. Caller statements and
  premises are unchanged.
- Updated the shared-law and RAD guides to use the cyclic/commutativity proof
  and the direct fold criterion.
- **Checks:** PIDE finished all four modified theories with zero errors,
  warnings, bad or unfinished commands, including the RD associativity tests.
  All 124 retained lemma statements are unchanged. Documentation links and
  whitespace checks passed. No batch rebuild was run.

## Use the symmetry premise directly for generic commutativity

3 November 2026.

- Changed `par_by_merge_comm` to assume `M is SymMerge`, equivalent to its
  previous premise `swapₘ ;; M = M`. Simplified its UTP, D, RD, AD and RAD
  callers to pass merge-symmetry facts directly.
- Retained `SymMerge_eval`, used by `rad_lift_merge_SymMerge` to establish
  symmetry of the lifted merge, and updated the shared-law guide.
- **Checks:** PIDE finished all six modified theories and the existing RD
  associativity tests with zero errors, warnings, bad or unfinished commands.
  The other 248 lemma statements in the modified theories are unchanged.
  Documentation links and whitespace checks passed. No batch build was run.

## Align parallel choice laws with sequential naming

3 November 2026.

Renamed the parallel distribution laws to `par_by_merge_SUP_distl` and
`par_by_merge_SUP_distr`, matching the bound variables and notation of
`seq_SUP_distl` and `seq_SUP_distr`. Updated the RD reference and shared-law
guide. UTP-only PIDE checks, documentation links and whitespace checks passed;
RD proof replay and batch builds were not run.

## Simplify parallel distribution to sets of alternatives

3 November 2026.

Replaced the indexed parallel distribution laws with `par_by_merge_Sup_distl`
and `par_by_merge_Sup_distr`, matching the set-based sequential laws. Updated
the RD caller and shared-law guide. UTP and a generic scratch check of the
caller's indexed-choice argument passed in PIDE. Documentation links and
whitespace checks passed; RD replay and batch builds were not run.

## Shorten the generic associativity equivalence proof

3 November 2026.

Shortened `par_by_merge_assoc_iff` from 30 to 17 proof lines by naming its two
sides with local term patterns and condensing the reverse direction. The
statement and proof methods are unchanged. UTP-only PIDE checks passed. In
three paired scratch checks, the revised lemma was faster in every pair;
median local PIDE timing was 474 ms versus 613 ms for the original. These are
local measurements, not batch-build timings. Documentation links and
whitespace checks passed; no downstream replay or batch build was run.

## Remove redundant merge type annotations

3 November 2026.

Removed the four redundant `fixes M` annotations from the generic symmetry
and associativity laws. PIDE confirmed identical inferred merge types before
and after, and UTP checked cleanly. Documentation links and whitespace checks
passed; no downstream replay or batch build was run.

## Group generic symmetry and associativity laws

3 November 2026.

Added a symmetry subsection after the general parallel laws and grouped its
pointwise characterisation, swap lemmas and commutativity rule. Kept the
existing associativity subsection and earlier theory structure. All 49 lemma
statements and proofs are unchanged. UTP-only PIDE, documentation-link and
whitespace checks passed; no downstream replay or build was run.

## Add the unconstrained-merge law

3 November 2026.

Added `par_by_merge_true`, proved by `pred_auto`: an unconstrained merge
requires feasibility of both operands and leaves the merged output unrestricted.
Updated the shared-law guide. UTP-only PIDE, documentation-link and whitespace
checks passed; no downstream replay or build was run.

## Reuse generic parallel algebra in D, AD and RD

3 November 2026.

D associativity now obtains its state-merge equation and lifted-merge criterion
from the generic UTP laws. AD uses shorter local representation and projection
equations before applying the D law. RD names direct instances of the generic
associativity and commutativity laws, and exposes `rdes_parallel_comm` for its
completed operator. Existing theorem premises are unchanged. Focused PIDE
checks of the D and AD parallel theories, the RD laws theory and the changed
RD associativity proof passed, as did documentation-link and whitespace checks.
The unchanged SRD-carrier criterion later in the RD associativity theory was
stopped during a slow replay after the changed proof passed. No full build,
RAD replay or RD counterexample-theory replay was run.

## Express design merge completion with H3m

3 November 2026.

Changed `merge_des` to apply `H3m` explicitly to the HDM-healthy raw lift.
The semantics are unchanged; the alternative-definition and symmetry proofs
unfold H3m, and H3m closure now follows from idempotence. Updated the D guide.
The D parallel theory passed focused PIDE checking (460 commands); documentation
links and whitespace checks passed. No downstream replay or full build was run.

## AD parallel without outer A3

3 November 2026. `merge_ades` now expresses completion as
`H3m (H1m (ades_lift_merge j))`, and `ades_par` uses that merge directly.
A3 closure, the simplified singleton evaluation and A normalisation now require
H1 operands. The associativity proof uses H1 and A2; symmetry, A2 closure and
the Chaos–Chaos law retain their premises. Focused PIDE validation checked
`utp_ades_parallel`; no full build or downstream theory replay was run.

## Generic design and AD Miracle zero laws

3 November 2026. Added `par_by_merge_miracle` in UTP Designs for H1 operands
and H1m merges, allowing different prior, branch and output alphabets. The lifted D proof now applies these
results directly; `ades_par_miracle` derives both AD zero laws for arbitrary `j`.
Focused PIDE checking covered the D and AD parallel theories. Documentation
links and whitespace checks passed; no full build or RD/RAD replay was run.

## Full rebuild after AD parallel changes

3 November 2026. The full registered build passed with
`./scripts/fullbuild.sh -v -o timeout=600`, including UTP Designs, RD, AD, RAD,
and Angelic CSP. The final run took 5 minutes 9 seconds; UTP2, Designs and
Reactive had passed earlier in the same rebuild sequence and were reused.

The first attempt stalled in RD. In `rdes_parallel_assoc_SRD_iff`, replaced
`pred_auto; blast` after choice distribution with `fast`; the remaining goal
only exchanges indexed choice binders. The theorem statement is unchanged.
The RD associativity theory passed focused PIDE checking and the final batch
build, including its test theory. No temporary proof probes remain.

## Consolidate generic Miracle zero laws

3 November 2026. Combined the two generic zero laws into
`par_by_merge_miracle`, with two conclusions and inferred types. Both branch
alphabets now agree; the prior and final output alphabets remain independent.
Updated the D and AD callers and guides. Focused PIDE checking covered both
parallel theories; no full build or RD/RAD replay was rerun for this cleanup.

## Organise D and AD parallel theories

3 November 2026. Grouped both theories into merge healthiness, generic parallel
laws, state-merge lifting and concrete parallel laws. AD keeps its observation
and slice helpers first. Shortened repetitive comments and retained the readable
observation formulas. Named declarations, theorem statements and proofs are
unchanged. Focused PIDE checking covered both parallel theories; no full build
or RD/RAD replay was run for this structural cleanup.

## Pairwise merge-healthiness commutation

3 November 2026. Settled all 21 unordered pairs among H1m, H2m, H3m, HDM,
A0m, A1m and A2m on arbitrary AD merges: 15 commute and 6 have proved
counterexamples. Added the H-only equations to UTP Designs and the AD equations
and existential counterexamples to AD parallel. The witnesses use unit or
Boolean state spaces; no finite search is used in the installed proofs.
The [AD guide](../parallel/AD.md#commutation-of-merge-healthiness) records the
matrix and explains the failures. Conditional commutation and one-way
preservation remain open. Focused PIDE checks passed for D (490 commands)
and AD (864 commands); documentation links and whitespace checks passed.
No full build or RD/RAD replay was run.

## Remove AD merge slices

3 November 2026. Removed `merge_slice` and its supporting lemmas from AD
parallel. Extensionality, generic closure and lifted-merge healthiness now use
merge observations directly; `ades_par_by_merge_obs` supplies the AD evaluation
form. Definitions and closure premises are unchanged. Updated the AD guide and
plan. Focused PIDE checking passed for the AD theory; documentation links and
whitespace checks passed. No full build or downstream replay was run.

## Concise parallel references

3 November 2026. Reduced the six parallel guides to shared notation, definitions,
laws with their premises, correspondence and semantic limits. Removed repeated
walkthroughs, proof narratives and tables; corrected the stale AD Miracle status.
Documentation links, incoming heading anchors, 70 parallel declaration references
and whitespace checks passed. No theories changed or Isabelle checks rerun.

## Combined AD merge healthiness and merge names

7 November 2026. Added `ADm ≡ A0m ∘ A1m`, proved its fixed-point law,
idempotence and monotonicity, and used it for generic and lifted AD closure.
Renamed the Design condition `HDM` to `HDm` and the ordinary RD condition
`RADm` to `ORDm` in the affected theories and guides.

Focused PIDE checks passed for Design parallel (588 commands), AD parallel
(746), ordinary RD parallel laws (518), the RD lift (284) and RAD parallel
(392), with no errors or unfinished commands in the checked contexts.
Documentation links and whitespace checks passed. The rename-only AP snapshot
and a batch build were not rerun.

## Reorganise RAD healthiness and use paper names

8 November 2026. Moved CSPA1 into RAD healthiness alongside CSPA2, moved
design forms, composition laws, choice laws and Example 11 into their owning
theories, and removed two unreferenced lemmas. RAD-facing statements now
use CSPA2; declaration links were updated.

PIDE passed the affected RAD theories and AP healthiness, RAD correspondence,
operators and nondivergence callers with no errors, bad or unfinished commands.
Documentation-link and whitespace checks passed. AP parallel and examples
were not replayed, and no batch build was run.

## Share choice-set merge healthiness in AD

8 November 2026. Moved PBMHm, RABm and their general laws into AD parallel;
PBMH closure is now `PBMH_ades_par_by_merge`. Updated the AD guide and
related declaration links.

Focused PIDE checking passed for AD parallel (862 commands), with no errors,
warnings, bad or unfinished commands. Documentation-link and whitespace
checks passed. No batch build was run.

## Move AP correspondence laws out of parallel

8 November 2026. Moved ordinary reactive-design correspondence into AP RAD,
Chaos laws into AP operators, and non-divergence results into AP ND.
Renamed `ap_rad_roundtrip_NDAP` to `H1_RA1_NDAP_AP_healthy` and used explicit
premises and conclusions for the two NDAP laws. Updated declaration links.

Focused PIDE checking passed for AP RAD, operators, ND and parallel, with
no errors, bad or unfinished commands. The existing warnings in operators
and ND remain. Documentation-link and whitespace checks passed. No AP
examples replay or batch build was run.
