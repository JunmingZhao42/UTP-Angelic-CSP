# Paper baseline checks

The cleanup branch retains the paper mechanisation and supporting algebra,
plus the AD parallel implementation already present at `dead464`.
See [PAPER_COVERAGE.md](PAPER_COVERAGE.md) for the source index and exact
qualifications, and [RESEARCH_BOUNDARY.md](RESEARCH_BOUNDARY.md) for the
excluded provisional work. The [associativity audit](../audits/seq-associativity/README.md)
is a separate session; its conditional laws are not production imports.

## Reproduce the paper check

From the repository root, with `ISABELLE` set to the Isabelle2025-2 executable:

```bash
python3 scripts/check-paper-baseline.py --isabelle "$ISABELLE"
```

The checker copies the current working-tree theories into a new temporary
project, omitting all three parallel theories and the audit. It removes their
session registrations and rewrites the three import-only aggregates. All
other copied theory bytes are unchanged. Thus the input is the working tree,
not necessarily the current commit; the manifest records both source hashes
and the parent commit for traceability.

Each dependency is exported from its checked-out submodule commit. Local
submodule edits are excluded; the manifest records those edits, the exported
commit and the parent gitlink. The checker never changes the source checkout
or submodules. No dependency pointers were changed by this cleanup.

Use `--output /absolute/path/to/new-directory` to retain the snapshot at a
chosen location, `--prepare-only` to export without building, or `--profile`
to select an isolated Isabelle user profile. The default profile is
`utp-paper-baseline`. The output contains `manifest.json`, `project/`, and,
when building, `build.log` and `result.json` with the exit status.

## Validation

The full cleanup sources and standalone audit were checked on 8 September
2026 using Isabelle2025-2. The full build includes the retained AD parallel
theory; the paper snapshot separately checks that the indexed development
does not depend on parallel research. A successful build checks the stated
Isabelle propositions, with the qualifications in the coverage index.
It does not establish unrestricted sequential associativity or remove the
additional premises documented for the paper correspondences.

The paper-only snapshot completed successfully on 8 September 2026 (exit 0;
6m42s including dependency rebuilds), using profile `utp-cleanup-2026-09-08`.
Its manifest and build log were retained in `/private/tmp/utp-step6-paper/`.

AP source files are copied from `angelic-processes/`. The snapshot keeps
the same directory layout and session names as its source checkout.

After the AP directory move, both the full cleanup build (including the
retained AD parallel theory and separate audit) and the relocated paper
snapshot passed. Each no-build freshness check also returned exit 0.
These checks used profile `utp-cleanup-2026-09-08` and reused the same
committed dependency export after verifying its hashes against the new
snapshot. The paper snapshot build took 54s. The commands, results and
manifests are retained with the cleanup backup under
`steps6-7-validation/`.
