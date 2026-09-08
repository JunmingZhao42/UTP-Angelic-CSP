# Research branch rebuild

Rebuilt on 8 September 2026 from reviewed `main` at `2c39a6e`.
The previous research tip, `8f8b5d9`, is preserved on
`backup/research-before-main-rebase-2026-09-08`.

## Source selection

| Content | Selection and check |
| --- | --- |
| AD theories and pinned dependencies | Unchanged from `main`. |
| AP parallel and AP healthiness support | Byte-for-byte copies of the previous research files. |
| RAD parallel | Previous research file, with only `ades_par_PBMH_ades` changed to `ades_par_is_PBMH_ades`. Reversing that rename reproduces the original bytes. |
| `ROOT` and RAD/AP aggregate imports | Exact copies of the research versions, retaining both WIP theories. |
| Standalone sequential audit | Keep `main`'s `lemma` keywords; statements and proofs match the previous research version. |
| Paper coverage | Keep `main`'s concise document; every coverage-table row matches the previous research version. |
| Paper checker | Keep `main`'s executable permission; script contents are identical. |

No RAD/AP definition, theorem premise or proof step was changed by this
rebuild. A successful build confirms the stated proofs, not that the WIP
semantics are final.

## Research documents

The mixed [parallel guide](../PARALLEL_BY_MERGE.md), `CLAUDE.md`, the
`slides/` ignore rule and all [PR drafts](pr-drafts/README.md) are retained.
The guide uses the current AD fact names and records the remaining duplicate
RAD helpers. The PR drafts retain their original dates and status reports.

The previous README's semantic discussion is retained in
[SEMANTIC_NOTES.md](SEMANTIC_NOTES.md). Its complete dependency handoff is
preserved, beneath a historical-record notice, in
[RESEARCH_HANDOFF.md](RESEARCH_HANDOFF.md). Current setup and build
instructions use `main`'s concise format, adjusted for this research branch.

## Validation

The committed source snapshot `ef24e81` passed Isabelle2025-2 in profile
`utp-cleanup-2026-09-08`:

- Full `UTP-Angelic-CSP` build, including all AD/RAD/AP parallel theories: exit 0.
- `Sequential_Composition_Audit`: exit 0.
- Subsequent no-build freshness check: exit 0.

All three project sessions and the audit rebuilt. Dependency heaps were
reused after their exported files were checked against the pinned commits.
Source and dependency hashes were unchanged after the build. The later
documentation commit has the same Isabelle inputs. The separate paper-only
snapshot was not rebuilt for this branch migration.

From a checkout with pinned dependencies, set `ISABELLE` to the Isabelle2025-2
executable and run from the repository root:

```bash
env ISABELLE_IDENTIFIER=utp-cleanup-2026-09-08 PROJECT_DIR="$PWD" \
  "$ISABELLE" build -b -d deps -d . -d audits/seq-associativity \
  -o system_heaps=false -o threads=4 \
  UTP-Angelic-CSP Sequential_Composition_Audit
```

Replace `-b` with `-n` for freshness. Local manifests, build logs and
before/after preservation records are retained in the cleanup backup under
`research-main-rebase/`.
