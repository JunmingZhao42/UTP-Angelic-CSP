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

| Documentation | Contents |
| --- | --- |
| [Paper coverage](docs/PAPER_COVERAGE.md) | Definitions, theorem names and exact assumptions |
| [Baseline checks](docs/BASELINE.md) | Full-project and paper-only build checks |
| [Parallel by merge](PARALLEL.md) | The AD/RAD/AP operators, merge healthiness, closure proofs and examples |
| [Semantic notes](docs/SEMANTIC_NOTES.md) | Observation alphabets, operators and differences from the sources |
| [Research boundary](docs/RESEARCH_BOUNDARY.md) | Paper baseline and parallel research scope |

## Parallel by merge

AD lifts a state merge and applies A3. RAD lifts an ordinary reactive merge
and applies RAD. AP transports RAD parallel through RA1 and H1. Each layer
has closure and mapping laws with explicit premises; AP transport can
identify distinct divergent processes. See the [parallel guide](PARALLEL.md).

## Build

Use **Isabelle2025-2** and the dependency commits pinned in `deps/`.
The submodules use GitHub SSH URLs. Most come from `isabelle-utp`;
`Optics` and `Z_Toolkit` use compatibility forks recorded in `.gitmodules`.

From this branch's checkout, set the path to your Isabelle executable:

```bash
export PROJECT_DIR="$PWD"
export ISABELLE="/path/to/Isabelle2025-2/bin/isabelle"
export UTP_PROFILE="utp-2025-2"
```

For an existing clone, run `git submodule sync --recursive`, then
`git submodule update --init --recursive`.
Install the profile templates and build all three sessions:

```bash
mkdir -p "$HOME/.isabelle/$UTP_PROFILE/etc"
cp isabelle-profile/ROOTS "$HOME/.isabelle/$UTP_PROFILE/ROOTS"
cp isabelle-profile/settings "$HOME/.isabelle/$UTP_PROFILE/etc/settings"

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP-Angelic-CSP
```

Keep `PROJECT_DIR` exported when using this profile. Replace `-b` with `-n`
for a freshness check without rebuilding.

## Edit

Open jEdit:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
  "$PROJECT_DIR/Angelic_CSP.thy"
```

Or start the VS Code language server:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" vscode_server \
  -n -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
  -d "$PROJECT_DIR/deps" -d "$PROJECT_DIR" \
  -o system_heaps=false
```

Both reuse the AD heap while keeping RAD/AP editable. To edit AD theories
too, use `-A UTP-Reactive-Designs` instead.

## Background

For the underlying UTP concepts, see Cavalcanti and Woodcock's *A Tutorial
Introduction to CSP in Unifying Theories of Programming* and Hoare and He's
*Unifying Theories of Programming*.
