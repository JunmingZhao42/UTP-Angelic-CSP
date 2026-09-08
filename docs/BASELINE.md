# Baseline checks

The [coverage index](PAPER_COVERAGE.md) lists the paper results and their
assumptions. The normal project build also includes the earlier AD parallel
theory; the paper check below excludes parallel development. See the
[research boundary](RESEARCH_BOUNDARY.md) for the current split.

## Run the checks

From the repository root, set `ISABELLE` to the Isabelle2025-2 executable.
To check all project sessions with a separate profile:

```bash
env ISABELLE_IDENTIFIER=utp-cleanup-2026-09-08 PROJECT_DIR="$PWD" \
  "$ISABELLE" build -b -d deps -d . \
  -o system_heaps=false -o threads=4 UTP-Angelic-CSP
```

Replace `-b` with `-n` for a freshness check. The
[sequential audit](../audits/seq-associativity/README.md#run-the-audit)
has its own session and command.

To check only the paper development:

```bash
python3 scripts/check-paper-baseline.py --isabelle "$ISABELLE"
```

## What the paper checker uses

The checker leaves the source checkout and submodules untouched.

| Input | Snapshot behaviour |
| --- | --- |
| Project theories | Copies the **working tree**, which may differ from the current commit. |
| Parallel theories and audit | Excludes them; adjusts `ROOT` and the three import-only aggregates. All other copied theory bytes are unchanged. |
| Dependencies | Exports each checked-out **submodule HEAD**, excluding local edits. This can differ from the parent repository's pinned commit. |
| Layout | Preserves the layer directories, including `angelic-processes/`, and session names. |

`manifest.json` records source hashes, the parent commit, exported dependency
commits, parent gitlinks and excluded submodule changes. The output directory
contains `project/` and, after a build, `build.log` and `result.json`.

Useful options:

- `--output /absolute/path/to/new-directory`: choose where to retain the output.
- `--prepare-only`: export without building.
- `--profile NAME`: choose the Isabelle profile; default `utp-paper-baseline`.

## Recorded validation

The following checks passed on **8 September 2026**, after the AP directory
move, with Isabelle2025-2 and profile `utp-cleanup-2026-09-08`:

| Check | Result |
| --- | --- |
| Full project, including the retained AD parallel theory | Build and freshness check: exit 0. |
| Paper-only snapshot | Build and freshness check: exit 0. |
| Standalone sequential associativity audit | Build and freshness check: exit 0. |

The dependency export was checked against its committed sources before reuse.
Local cleanup backups retain the commands, logs and manifests under
`steps6-7-validation/`; the final history checks are under `history-repair/`.
These are historical validation records, not a new build triggered by a
documentation edit.

A passing build checks the stated propositions. Their additional premises
still apply, and general design sequential associativity remains false.
