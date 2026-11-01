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

Scratch work behind open PLAN Stage 1 items (necessity and commutation of the
merge conditions). Both were installed on 2 November 2026 under new names; the
scratch files keep the old names and no longer load against the current theory.

- [Generic AD closure rules](2026-10-30-ad-generic-closure-exploration/README.md)
  for an arbitrary merge `M`.
- [AD merge transformers](2026-10-30-ad-merge-healthiness/README.md), now `Am`
  and `A2m`.

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
- **Angelic conditions and rules:** `merge_slice`, `merge_health`, `Am`, `A2m`
  (`A2m_atoms`, `A2m_reduce`), `A_par_by_merge`, `A2_par_by_merge`,
  `A3_par_by_merge`, `merge_ades_is_Am` and `merge_ades_is_A2m`, ported from the
  two 30 October explorations. The lifted closures are now corollaries. New
  helpers: `H3_obs` in the AD core and `H1_H3_impl_A3` in AD healthiness.
- **Slice-wise forms:** `Am` is defined explicitly, like `H1m`.
  `H1m_merge_health`, `H2m_merge_health`, `H3m_merge_health`,
  `HDM_merge_health` and `Am_merge_health` show that each condition applies H1,
  H2, H3, **H** or A to every slice of an AD merge.
- **Layout:** `utp_ades_parallel.thy` follows D's order: merge observations,
  merge healthiness, generic closure, lifting, AD parallel, correspondence,
  algebraic laws, skip example. Downstream theories needed no change.
- **Checks:** PIDE reported zero errors for D's parallel theory and all five AD
  theories. The UTP-Designs and RD heaps were rebuilt with the change, and the
  full build then passed for AD, RAD and CSP (2 min 24 s, two threads).
