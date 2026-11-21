# Patched Isabelle2026 setup

Use the ARM64 macOS Isabelle2026 distribution, revision `096842708b28`, with the
published `thm.ML` fix. The local installation is
`$HOME/Applications/Isabelle2026-patched.app`, and its main profile is
`utp-2026-patched`. The 2025-2 installation and its profile remain separate.

The project builds from the dependency revisions recorded in `deps/`; the
toolkit forks carry the Isabelle2026 compatibility commits.

## Installation and kernel

The [official ARM archive](https://isabelle.in.tum.de/website-Isabelle2026/dist/Isabelle2026_macos_arm.tar.gz)
has SHA-256 `7244e596d44ee9fbb8b988ef2990474b3385fa4a7ec1343867b224a13b6ddc28`.
Verify the archive before extraction. In `src/Pure/thm.ML`, compare the
`bicompose_aux` / `newAs` context with the
[published patch](https://isabelle.systems/zulip-archive/stream/247541-Mirror.3A-Isabelle-Users-Mailing-List/topic/.E5.9B.9E.E5.A4.8D.3A.20.5Bisabelle.5D.20Soundness-critical.20issues.20in.20thm.2EML.html).
For this revision, its exact changes are:

```diff
-          (case rename_bvars dpairs tpairs B As0 of
+          (case rename_bvars dpairs (rtpairs @ tpairs) Bi As0 of
...
-              in (map (strip_apply (Same.commit term) B) As0, deriv_rule1 I proof rder) end
+              in (map (strip_apply (Same.commit term) Bi) As0, deriv_rule1 I proof rder) end
```

Source edits take effect only after rebuilding Pure and HOL. The runtime root
inside this macOS bundle is `Contents/Resources`; the top-level `heaps` entry
is a symlink. Set aside the actual `Contents/Resources/heaps` directory as
`Contents/Resources/heaps.unpatched-distribution` before rebuilding.

Before first opening this isolated app, add this guard at the start of its
`etc/settings`, before it computes `ISABELLE_HOME_USER`:

```bash
case "$ISABELLE_IDENTIFIER" in
  utp-2026-patched|utp-2026-patched-*) ;;
  *) ISABELLE_IDENTIFIER=utp-2026-patched ;;
esac
ISABELLE_NAME="$ISABELLE_IDENTIFIER"
```

This keeps inherited macOS GUI settings from directing the new prover into an
older profile, while allowing the separate paper profile. Use macOS's normal
Gatekeeper and App Management approvals when required.

## Profile and build

From the project root:

```bash
export PROJECT_DIR="$PWD"
export ISABELLE="$HOME/Applications/Isabelle2026-patched.app/bin/isabelle"
export UTP_PROFILE=utp-2026-patched
export ISABELLE_IDENTIFIER="$UTP_PROFILE"
mkdir -p "$HOME/.isabelle/$UTP_PROFILE/etc"
cp isabelle-profile/settings "$HOME/.isabelle/$UTP_PROFILE/etc/settings"
cp isabelle-profile/ROOTS "$HOME/.isabelle/$UTP_PROFILE/ROOTS"
"$ISABELLE" build -b -v -o system_heaps=false -o threads=4 HOL
./scripts/fullbuild.sh -v -o quick_and_dirty=false
```

Start with no Pure/HOL images in the new profile. The settings template also
excludes distribution heaps and caps ML memory at 4000 MiB; it retains the
4 GiB Java budget. Avoid `-c` in a populated profile: it also cleans registered
descendant caches.

## PIDE MCP

The separate component checkout is
`$HOME/Applications/isabelle-pide-mcp-2026-patched`, at commit
`51593d3d12000ef4ed450a07aaaba347530d3479`. Its `ISABELLE_VERSION` matches
`096842708b28`. Register it only in the new profile:

```bash
"$ISABELLE" components -u "$HOME/Applications/isabelle-pide-mcp-2026-patched"
```

The new profile's `etc/preferences` contains:

```text
pide_ai_unicode_symbols_disk = false
pide_ai_unicode_symbols = false
pide_ai_build_encode_symbols = false
```

These settings preserve the existing source encoding. This tool version uses
`node` and `session_id`, millisecond timeouts, and `ranged_origins` in place of
`find_entities`. The project MCP configuration runs
[`scripts/pide-mcp.sh`](../../scripts/pide-mcp.sh), which fixes the executable
and profile and locates the current worktree. The old global wrapper is unchanged.
Refresh only the affected client connection after changing its command; see
[Codex MCP configuration](https://learn.chatgpt.com/docs/extend/mcp?surface=cli).

## Verification and rollback

On 12 November 2026, patched Pure/HOL, the three regression helper checks,
ordinary valid proofs, and the complete `UTP-Angelic-CSP` build passed. Each
saved invalid proof was rejected independently at a proof command. The Pure
build database's kernel-source digest matches the patched `thm.ML`.
PIDE verification checks the AP parallel theory, the project entry, the actual
runtime installation/profile, and complete processing of the loaded theories.
Passing those regressions establishes only that those examples are blocked.
It does not establish that Isabelle has no other soundness defects.

Raw logs, source hashes, patches and recoverable snapshots are kept locally,
outside the repository. Compatibility edits adapt
ML APIs, replace one removed solver-helper reference, make AP symmetry rules
explicit, and prove `H1_A2_closure` at its unchanged general type. Statements,
premises and definitions are preserved. Existing upstream SMT proofs were
allowed for the rebuild; new and repaired proofs use no SMT.

The paper-only helper's mock check fails on both the initial snapshot and the
updated checkout because its existing filter omits the split parallel filenames.
A paper-only proof build was not part of this verification.

For rollback, review the upgrade-only diff and restore only its allowlisted files
from the snapshot's `initial/working-files.tar.gz`, preserving any later edits. Restore the saved
project MCP configuration, then select `/Applications/Isabelle2025-2.app/bin/isabelle`
and `utp-2025-2`. During initial GUI approval, the inherited old identifier caused
a cache collision; its Pure/HOL images were subsequently rebuilt with the
unchanged 2025-2 executable, with user approval. Their bytes and logs differ from
the original cache. The saved copies of the old heaps were deleted on
22 November 2026, so dependent sessions need a rebuild after rollback.
