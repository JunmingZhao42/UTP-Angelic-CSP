# UTP-Angelic-CSP

An Isabelle/UTP mechanisation of Ribeiro and Cavalcanti's
[Angelic processes for CSP via the UTP](https://doi.org/10.1016/j.tcs.2018.10.008)
(*Theoretical Computer Science* 756, 2019, pp. 19–63).

The three sessions build on each other:

| Layer | Directory | Session |
| --- | --- | --- |
| Angelic designs (AD) | `angelic-designs/` | `UTP-Angelic-Designs` |
| Reactive angelic designs (RAD) | `reactive-angelic-designs/` | `UTP-Reactive-Angelic-Designs` |
| Angelic processes (AP) | `angelic-processes/` | `UTP-Angelic-CSP` |

[angelic-processes/utp_ap.thy](angelic-processes/utp_ap.thy) is the entry point. On `research/parallel2`,
ordinary design parallel follows the raw state merge with design Skip, as the
reactive-design merge does with reactive Skip: the merge constrains the output
only when both branches terminate, and after divergence some merged state must
still exist. The AD lifting and its ordinary-design correspondence proofs use
this semantics; RAD/AP retain their separate reactive merge semantics.
The reviewed development is on `main`.

See the [documentation index](docs/README.md) for the paper guides, parallel
notes and build checks.

## Parallel by merge

AD lifts a state merge and applies A3. RAD lifts an ordinary reactive merge,
with no outer RAD wrapper. AP completes the RAD merge as AD does, and relates the
result to RAD through RA1 and H1, as for sequential composition. Each layer has
closure and mapping laws with explicit premises. See the
[parallel guide](docs/parallel/README.md).

## Build

Use **Isabelle2026 (revision `096842708b28`) with the published kernel fix**
and the dependency revisions in `deps/`. The fix changes `bicompose_aux`
in `src/Pure/thm.ML`; an unpatched Isabelle2026 installation is insufficient.
See [patched installation setup](docs/tools/isabelle2026-patched.md).
The submodules use GitHub SSH URLs. Abstract_Prog_Syntax comes from
`isabelle-utp`; the others use the forks recorded in [.gitmodules](.gitmodules),
which carry this development's changes and the Isabelle2026 compatibility edits.

### Setup

From the repository root, set the executable and profile:

```bash
export PROJECT_DIR="$PWD"
export ISABELLE="$HOME/Applications/Isabelle2026-patched.app/bin/isabelle"
export UTP_PROFILE="utp-2026-patched"

# On a fresh clone only: this resets submodules to the recorded commits.
git submodule sync --recursive
git submodule update --init --recursive
```

Install the profile templates:

```bash
mkdir -p "$HOME/.isabelle/$UTP_PROFILE/etc"
cp isabelle-profile/ROOTS "$HOME/.isabelle/$UTP_PROFILE/ROOTS"
cp isabelle-profile/settings "$HOME/.isabelle/$UTP_PROFILE/etc/settings"
```

Keep `PROJECT_DIR` exported when using this profile.

### Full build

To build only the ordinary-design layer:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build -b -d deps \
  -o system_heaps=false -o threads=4 UTP-Designs
```

Build all three sessions, including the parallel development:

```bash
./scripts/fullbuild.sh
```

Pass `-n` for a freshness check: `./scripts/fullbuild.sh -n`.

### Paper-only build

Build the development indexed by the [paper guides](docs/paper/README.md),
without the parallel theories:

```bash
./scripts/paperbuild.sh
```

This uses the current checkout and submodules. It temporarily adjusts the paper
imports outside the checkout, then removes that temporary directory.

## Edit

Open jEdit:

```bash
./scripts/edit.sh
```

Or start the VS Code language server:

```bash
./scripts/edit.sh vscode
```

Both keep RAD/AP editable. To edit AD too:

```bash
./scripts/edit.sh jedit -A UTP-Reactive-Designs
```

The scripts use `ISABELLE` and `UTP_PROFILE` from setup and accept additional
Isabelle options. They locate the repository automatically.

To check the helpers themselves, run [test-build-scripts.sh](scripts/test-build-scripts.sh):

```bash
./scripts/test-build-scripts.sh
```

It uses a mock Isabelle command to check paper exclusions, unchanged proof files,
cleanup, failure handling and editor routing. It does not build proofs or open
an editor.

## Background

For the underlying UTP concepts, see Cavalcanti and Woodcock's *A Tutorial
Introduction to CSP in Unifying Theories of Programming* and Hoare and He's
*Unifying Theories of Programming*.
