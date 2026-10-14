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

[Angelic_CSP.thy](Angelic_CSP.thy) is the entry point. The
`research/parallel` branch keeps one parallel operator by lifted merge per
AD, RAD and AP layer. This experimental work is included in the build.
The reviewed development is on `main`.

See the [documentation index](docs/README.md) for the paper guides, parallel
notes, build checks and source correspondence review.

## Parallel by merge

AD lifts a state merge and applies A3. RAD lifts an ordinary reactive merge
and applies RAD. AP transports RAD parallel through RA1 and H1. Each layer
has closure and mapping laws with explicit premises; AP transport can
identify distinct divergent processes. See the [parallel guide](docs/parallel/README.md).

## Build

Use **Isabelle2025-2** and the dependency commits pinned in `deps/`.
The submodules use GitHub SSH URLs. Most come from `isabelle-utp`;
Optics uses the compatibility fork recorded in [.gitmodules](.gitmodules).

### Setup

From the repository root, set the executable and profile:

```bash
export PROJECT_DIR="$PWD"
export ISABELLE="/path/to/Isabelle2025-2/bin/isabelle"
export UTP_PROFILE="utp-2025-2"

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

Build all three sessions, including the parallel development:

```bash
./scripts/fullbuild.sh
```

Pass `-n` for a freshness check: `./scripts/fullbuild.sh -n`.

### Paper-only build

Build the development indexed by the [paper guides](docs/paper/README.md),
without the parallel theories or RAD representation comparison:

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
