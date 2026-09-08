> Historical record from the previous research branch (`8f8b5d9`).
> The revisions and pending-work descriptions below describe that checkpoint.
> Use [baseline checks](BASELINE.md) and [branch contents](RESEARCH_BOUNDARY.md)
> for the rebuilt branch.

# Paper baseline and dependency handoff

The paper baseline covers the AD/RAD/AP development indexed in
[PAPER_COVERAGE.md](PAPER_COVERAGE.md), including the explicit qualifications
to the source. The working `ROOT` still includes the parallel research.

## Independent paper check

From the repository root, run:

```bash
python3 scripts/check-paper-baseline.py \
  --isabelle /Applications/Isabelle2025-2.app/bin/isabelle
```

Use the executable path for your installation. Python 3 and Git are the only
additional requirements. The default Isabelle profile is `utp-paper-baseline`;
it is separate from the interactive `utp-2025-2` profile. The script uses
`system_heaps=false` and four proof threads. One editor server (VS Code or
PIDE MCP) may remain active during one build. Run builds serially, as specified
in the local `AGENTS.md` runtime policy.

The script retains a temporary directory and prints its location. It contains:

- `project/`: the exact source snapshot checked by Isabelle;
- `manifest.json`: file SHA-256 hashes, submodule HEADs, parent gitlinks and
  the local submodule edits excluded from the snapshot;
- `build.log` and `result.json`: the build output, command and exit code.

`--output PATH` chooses a new output directory; an existing directory is never
overwritten. `--prepare-only` exports the snapshot without starting Isabelle.
`--profile NAME` selects another dedicated profile.

Every nonparallel project theory is copied from the current working tree.
Only four build-boundary files are transformed in the copy:

| File | Snapshot change |
| --- | --- |
| `ROOT` | Omit `utp_ades_parallel`, `utp_rad_parallel` and `utp_ap_parallel` from the theory lists. |
| `angelic-designs/utp_ades.thy` | Import `utp_ades_designs`. |
| `reactive-angelic-designs/utp_rad.thy` | Import `utp_rad_nd`, `utp_rad_examples` and `utp_rad_ops_csp`. |
| `Angelic_CSP.thy` | Import `angelic-processes/utp_ap_nd` and `angelic-processes/utp_ap_examples`. |

The aggregates contain no definitions or proofs. The script checks that they
remain import-only before replacing their imports. The other project theory
contents are identical to the working files, with both hashes recorded.
No associativity audit theory or project parallel theory is loaded. Imported
UTP libraries may still contain their own established parallel theories.

Each dependency is exported with `git archive` at its **checked-out HEAD**.
Uncommitted modifications and untracked dependency files are excluded.
`deps/ROOT` and `deps/ROOTS` are parent-repository files and are copied from the
working tree. The script does not fetch, reset, stage, commit or push anything.

This snapshot boundary preserves the current parallel files, including their
imports. A permanent split into paper and research sessions would also need
explicit imports in those parallel files: merely removing them from the
existing aggregates would remove dependencies they currently inherit.

## Validation record: 2026-09-07

Both builds passed with Isabelle2025-2 on arm64 macOS:

| Check | Result |
| --- | --- |
| Paper snapshot, fresh `utp-paper-baseline` profile | Exit 0; 6m12s. Rebuilt HOL-Eisbach, Optics, Shallow_Expressions, Shallow_Expressions_Z, UTP2, UTP-Designs, UTP-Reactive, UTP-Reactive-Designs and all three project sessions. Distribution HOL heaps were reused. |
| Final paper recheck after two declaration-keyword tidies | Exit 0; 40s. Rebuilt RAD and AP in the same snapshot/profile. |
| Full working tree, `utp-2025-2` profile | Exit 0; 44s. Rebuilt RAD and AP, including their parallel theories; reused current dependency and AD heaps. |
| Source and preservation checks | All 18 nonaggregate paper theories match the final snapshot byte-for-byte. All snapshot hashes match their manifest. 148 protected dependency/parallel files are unchanged; pending submodule patches/status and the parent staging index are unchanged. |
| Source hygiene | `git diff --check` passes in the parent and both dirty submodules. No `sorry`, `oops`, `metis` or exploratory proof commands were found in the nonparallel project theories. All 70 headline theorem rows (3–72) and their qualified fact references were checked against the source. |

The fresh-profile check confirms that the paper development does **not** need
the pending UTP or UTP-Designs edits. It uses the checked-out committed
revisions listed below, not the older gitlinks still recorded by the parent.
The full build confirms that the cleanup is compatible with the current
parallel research and pending dependency edits.

Local evidence from this run is retained under
`/tmp/angelic-paper-baseline-2026-09-07/` (`build.log`, `final-build.log`,
`manifest.json`, `result.json`) and `/tmp/angelic-baseline-check/`
(`full-build.log`, `preservation.json`). These temporary files are local
evidence; rerun the script to reproduce the check after later changes.

The final paper recheck used:

```bash
env ISABELLE_IDENTIFIER=utp-paper-baseline \
  PROJECT_DIR=/tmp/angelic-paper-baseline-2026-09-07/project \
  /Applications/Isabelle2025-2.app/bin/isabelle build -v -b \
  -d /tmp/angelic-paper-baseline-2026-09-07/project/deps \
  -d /tmp/angelic-paper-baseline-2026-09-07/project \
  -o system_heaps=false -o threads=4 UTP-Angelic-CSP
```

The full working-tree check used:

```bash
env ISABELLE_IDENTIFIER=utp-2025-2 \
  PROJECT_DIR=/Users/ming/AI-summer/repos/UTP-Angelic-CSP \
  /Applications/Isabelle2025-2.app/bin/isabelle build -v -b \
  -o system_heaps=false -o threads=4 UTP-Angelic-CSP
```

The cleanup moved the shared RA1 input-unrest law into `utp_rad_healthy`
and the shared prefix observations/continuations into `utp_rad_seq`, without
changing their statements or proofs. Declaration keywords now classify
`RA1_RA3_commute` as paper Theorem 68 and the demonic Chaos zero law as a
supporting lemma. The README and local roadmap point to the coverage record;
the roadmap's completed AP results and support locations are corrected.
No submodule or project parallel source was edited, and nothing was staged,
committed or pushed.

## Submodule review and commit order

The dependency revisions exported for the paper check are:

| Submodule | Checked-out commit |
| --- | --- |
| `Abstract_Prog_Syntax` | `44f64866919533975745da914b337572066733cb` |
| `Circus_Toolkit` | `8542d78a64088d18fc9402c111aafd433a8371ff` |
| `Optics` | `047501aa20507f372cbe96c58014813ffff3d390` |
| `Shallow-Expressions` | `c8ca17a0b85335435d2bc40b13b8a4a1c38dde57` |
| `UTP` | `ac77c5f6ffe3d6f291a413f146637ed6970dced0` |
| `UTP-Designs` | `6fb241add47f398fd35277b816457b07d3d3c85a` |
| `UTP-Reactive` | `2054af57da7a43fd374700d5ec97599631229f0d` |
| `UTP-Reactive-Designs` | `143d4a572c7de372240406dc0b3c28bafed19d50` |
| `Z_Toolkit` | `e02081d630ac81dd3355d148fb64803c90640f94` |

Two revisions differ from the parent repository's recorded gitlinks:
`Circus_Toolkit` (`a19e7c8` → `8542d78`) and `UTP-Designs`
(`700a4fe` → `6fb241a`). The existing change to `deps/ROOT` adds the
`Abstract_Prog_Syntax` session dependency needed by the newer Circus toolkit.
It belongs to the parent repository, not to a submodule commit.

The source changes awaiting **your review** are:

| Repository | Pending files | Purpose |
| --- | --- | --- |
| `deps/UTP` | `utp_concurrency.thy` | Adds `merge_eval`, a pointwise abbreviation for the existing merge-record encoding. |
| `deps/UTP-Designs` | `utp_des_healths.thy` | Adds `H_implies_H1`, `H_implies_H2` and `N_implies_H`. The last is an alias-style wrapper around an existing implication. |
| `deps/UTP-Designs` | `utp_des_parallel.thy` (untracked), `utp_designs.thy` | Adds the design parallel theory and imports it through the aggregate. Include the new file when reviewing the aggregate change. |

These changes are preserved, not revised by the paper cleanup. Build validation
does not substitute for reviewing the intended parallel semantics or deciding
the scope of an upstream PR. No remote state was refreshed during this check.

After reviewing the changes:

1. Commit the intended UTP change in `deps/UTP`.
2. Commit the intended UTP-Designs changes in `deps/UTP-Designs`, including the
   new theory if keeping its aggregate import. The new parallel theory uses
   the UTP merge interface, so review that dependency together.
3. Make the selected submodule commits available from the intended remote
   repositories, using your preferred branch/PR workflow. Check the destination
   remotes before publishing.
4. Rebuild the full project and rerun the paper snapshot check at those HEADs.
5. Record the resulting submodule gitlinks and `deps/ROOT` in the parent
   repository, together with the intended parent source/documentation changes.

Do not run `git submodule update` over these pending edits to obtain a baseline;
the snapshot script supplies the committed-content check without changing them.
A later clean clone is reproducible only once the chosen submodule commits are
available and the parent commit records their gitlinks. The current dirty
parent tree is not yet such a published checkpoint.

AP source files are copied from `angelic-processes/`. The snapshot keeps
the same directory layout and session names as its source checkout.

On 8 September 2026, after the AP directory move, the full research build
and standalone associativity audit passed with Isabelle2025-2. The no-build
freshness check returned exit 0. The check reused a verified export of the
current pinned dependency commits in profile `utp-cleanup-2026-09-08`.
This validates the relocated sources; the provisional parallel content still
requires semantic review. The earlier validation and dependency handoff above
describe the 7 September checkpoint.
