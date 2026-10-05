# Baseline checks

The [coverage index](PAPER_COVERAGE.md) lists the paper results and their
assumptions. This branch's normal build includes AD parallel and RAD/AP
parallel WIP; the paper check below excludes all parallel development. See the
[research boundary](RESEARCH_BOUNDARY.md) for the current split.

## Run the checks

From the repository root, set `ISABELLE` to the Isabelle2025-2 executable.
To check all project sessions:

```bash
env ISABELLE_IDENTIFIER=utp-2025-2 PROJECT_DIR="$PWD" \
  "$ISABELLE" build -b -d deps -d . \
  -o system_heaps=false -o threads=4 UTP-Angelic-CSP
```

Replace `-b` with `-n` for a freshness check.

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

A passing build checks the stated propositions. Their additional premises
still apply, and general design sequential associativity remains false.
