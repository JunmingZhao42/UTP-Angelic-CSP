# UTP-Angelic-CSP

This repository is an Isabelle/UTP workspace for mechanising ideas from
Ribeiro and Cavalcanti's paper on angelic processes for CSP.
It is currently a child session based on the Isabelle/UTP reactive-design stack.

## Basis

The intended mathematical source is:

- Pedro Ribeiro and Ana Cavalcanti, [Angelic processes for CSP via the UTP](https://doi.org/10.1016/j.tcs.2018.10.008), *Theoretical Computer Science* 756, 2019, pp. 19-63.

Useful background reading:

- Ana Cavalcanti and Jim Woodcock, [A Tutorial Introduction to CSP in Unifying Theories of Programming](../../UTP-tutorial/CW06.pdf) for the UTP, designs, reactive processes, and CSP background.
- Hoare and He's UTP book, especially the chapters on alphabetised predicates, designs, recursion, and reactive processes.

## Requirements

This repository uses:

- the official `Isabelle2025-2` distribution;
- the profile `utp-isabelle-2025-2`; and
- dependency commits pinned under `deps/`.

Most dependencies are pinned from `github.com/isabelle-utp`. `Optics` and
`Z_Toolkit` use the `optics-2025-2` and `z-2025-2` compatibility forks.

## Quick Start

Clone the repository with its pinned dependencies, then set `PROJECT_DIR` to
the repository root, `ISABELLE` to the Isabelle executable, and `UTP_PROFILE`
to the project's Isabelle user profile:

```bash
git clone --recurse-submodules <repository-url> UTP-Angelic-CSP
cd UTP-Angelic-CSP

export PROJECT_DIR="$PWD"
export ISABELLE="/path/to/Isabelle2025-2/bin/isabelle"
export UTP_PROFILE="utp-isabelle-2025-2"
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
  -n -u -R UTP-Angelic-CSP \
  "$PROJECT_DIR/Angelic_CSP.thy"
```
