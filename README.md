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

`Angelic_CSP.thy` is the entry point. This is `research/parallel`, based on
`main` with the reviewed AD parallel foundation. Its normal build also loads
**RAD/AP parallel WIP**; a passing build does not make that research final.
Use `main` for the reviewed development.

| Read this | For |
| --- | --- |
| [Paper coverage](docs/PAPER_COVERAGE.md) | Definitions, theorem names and exact assumptions |
| [AD parallel](docs/AD_PARALLEL_REVIEW.md) | Merge semantics, naming and qualified parallel laws |
| [Parallel research](PARALLEL_BY_MERGE.md) | The AD/RAD/AP research guide and open issues |
| [Semantic notes](docs/SEMANTIC_NOTES.md) | Observation alphabets, operators and source qualifications |
| [Baseline checks](docs/BASELINE.md) | Paper-only builds and validation records |
| [Research boundary](docs/RESEARCH_BOUNDARY.md) | What this research branch adds to `main` |
| [Sequential associativity audit](audits/seq-associativity/README.md) | Counterexamples and conditions for reassociation |

## Build

Use **Isabelle2025-2** and the dependency commits pinned in `deps/`.
The submodules use GitHub SSH URLs. Most come from `isabelle-utp`;
`Optics` and `Z_Toolkit` use compatibility forks recorded in `.gitmodules`.

Clone, then set the path to your Isabelle executable:

```bash
git clone --branch research/parallel --recurse-submodules git@github.com:JunmingZhao42/UTP-Angelic-CSP.git
cd UTP-Angelic-CSP

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
