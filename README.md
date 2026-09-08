# UTP-Angelic-CSP

This repository is an Isabelle/UTP workspace for mechanising ideas from
Ribeiro and Cavalcanti's paper on angelic processes for CSP.
It provides three stacked sessions for angelic designs, reactive angelic
designs, and angelic processes, based on the Isabelle/UTP reactive-design stack.

The layer directories are `angelic-designs/`, `reactive-angelic-designs/`,
and `angelic-processes/`. The top-level `Angelic_CSP.thy` remains the entry
point; all three session names are unchanged.

The cleanup retains the committed AD parallel implementation; provisional
AD extensions and RAD/AP parallel remain on `research/parallel`. See the
[research boundary](docs/RESEARCH_BOUNDARY.md) for the source selection and
validation results. The [paper coverage index](docs/PAPER_COVERAGE.md)
records the exact theorem qualifications; [baseline guide](docs/BASELINE.md)
describes the separate paper snapshot.

## Basis

The intended mathematical source is:

- Pedro Ribeiro and Ana Cavalcanti, [Angelic processes for CSP via the UTP](https://doi.org/10.1016/j.tcs.2018.10.008), *Theoretical Computer Science* 756, 2019, pp. 19-63.

Useful background reading:

- Ana Cavalcanti and Jim Woodcock, [A Tutorial Introduction to CSP in Unifying Theories of Programming](../../UTP-tutorial/CW06.pdf) for the UTP, designs, reactive processes, and CSP background.
- Hoare and He's UTP book, especially the chapters on alphabetised predicates, designs, recursion, and reactive processes.

## Requirements

This repository uses:

- the official `Isabelle2025-2` distribution;
- the profile `utp-2025-2`; and
- dependency commits pinned under `deps/`.

Most dependencies use upstream `isabelle-utp` repositories. `Optics` and
`Z_Toolkit` use the `main` branches of the `JunmingZhao42` forks for
Isabelle2025-2 compatibility. `.gitmodules` records the repositories;
the submodule entries pin the exact commits.

## Quick Start

Clone the repository with its pinned dependencies, then set `PROJECT_DIR` to
the repository root, `ISABELLE` to the Isabelle executable, and `UTP_PROFILE`
to the project's Isabelle user profile:

```bash
git clone --recurse-submodules <repository-url> UTP-Angelic-CSP
cd UTP-Angelic-CSP

export PROJECT_DIR="$PWD"
export ISABELLE="/path/to/Isabelle2025-2/bin/isabelle"
export UTP_PROFILE="utp-2025-2"
```

Adjust the Isabelle executable path for your installation. Then run:

```bash
cd "$PROJECT_DIR"
git submodule sync --recursive
git submodule update --init --recursive

mkdir -p "$HOME/.isabelle/$UTP_PROFILE/etc"
cp "$PROJECT_DIR/isabelle-profile/ROOTS" \
  "$HOME/.isabelle/$UTP_PROFILE/ROOTS"
cp "$PROJECT_DIR/isabelle-profile/settings" \
  "$HOME/.isabelle/$UTP_PROFILE/etc/settings"

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP-Angelic-CSP
```

Open the checked project for editing with:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
  "$PROJECT_DIR/Angelic_CSP.thy"
```

The same session setup can be used by the VS Code language server:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" vscode_server \
  -n -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
  -d "$PROJECT_DIR/deps" -d "$PROJECT_DIR" \
  -o system_heaps=false
```

These commands load the finished `UTP-Angelic-Designs` heap and keep the
reactive angelic design and angelic-process theories editable. To edit the
`utp_ades_*` theories as well, replace `-A UTP-Angelic-Designs` with
`-A UTP-Reactive-Designs`.
