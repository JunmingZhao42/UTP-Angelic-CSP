# Isabelle Setup

This project is intended to use a plain Isabelle2025 installation with a separate
Isabelle user profile for the local UTP source stack.
**Note:** I have only tested the setup on macOS.

## What You Need

This setup uses two pieces:

1. A plain `Isabelle2025.app`, used as the Isabelle executable. Download it
   from [the Isabelle2025 distribution page](https://isabelle.in.tum.de/website-Isabelle2025/dist/).
2. This project checkout, including its pinned submodules under `deps/`.

## Project Setup

Set up these environment variables to match your machine:

```bash
export PROJECT_DIR="$HOME/path/to/UTP-Angelic-CSP"
export ISABELLE_HOME="$HOME/path/to/Isabelle2025.app"
export ISABELLE="$ISABELLE_HOME/bin/isabelle"
export UTP_PROFILE="Isabelle2025-utp"
```

Here `PROJECT_DIR` is the root of this repository checkout. `ISABELLE_HOME`
points to the plain Isabelle app bundle. `UTP_PROFILE` is the name of the
isolated Isabelle user profile for this project.

Clone this project from your own repository or fork, including its pinned
submodules:

```bash
git clone --recurse-submodules <your-UTP-Angelic-CSP-repo-url> "$PROJECT_DIR"
cd "$PROJECT_DIR"
```

For an existing checkout, initialise or refresh the submodules with:

```bash
cd "$PROJECT_DIR"
git submodule update --init --recursive
```

The UTP stack is recorded as git submodules under `deps/`. The submodule commit
pointers in this repository are the known-good versions for this project.

The expected directory layout is:

```text
$WORKSPACE/
  Isabelle2025.app
  UTP-Angelic-CSP/
    deps/
      Abstract_Prog_Syntax/
      Circus_Toolkit/
      Optics/
      Shallow-Expressions/
      UTP/
      UTP-Designs/
      UTP-Reactive/
      UTP-Reactive-Designs/
      Z_Toolkit/
```

The current working setup uses pinned submodule commits from the upstream
`isabelle-utp` repositories. The `deps/ROOT` and `deps/ROOTS` files describe
the dependency sessions, and the project profile points Isabelle at `deps/`.

## Isabelle Profile

Create one isolated Isabelle profile for this source stack:

```bash
mkdir -p "$HOME/.isabelle/$UTP_PROFILE/etc"
```

This profile keeps ROOTS, settings, and build products separate from the default
`Isabelle2025` profile.

Install the repo copy of `ROOTS` into the Isabelle profile:

```bash
cp "$PROJECT_DIR/isabelle-profile/ROOTS" "$HOME/.isabelle/$UTP_PROFILE/ROOTS"
```

Install the recommended Isabelle settings:

```bash
cp "$PROJECT_DIR/isabelle-profile/settings" \
  "$HOME/.isabelle/$UTP_PROFILE/etc/settings"
```

The settings file gives jEdit/PIDE and Poly/ML more memory for the large UTP
sessions. You can adjust it if your machine needs a different memory budget.

Use this command prefix for all Isabelle commands in this project:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE"
```

## One-Off Build

The first real build can take a while:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false \
  UTP-Angelic-CSP
```

This stores the compiled sessions under the isolated Isabelle profile.

## Open This Project

First editable open, or after changing session dependencies:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -u -R UTP-Angelic-CSP \
  "$PROJECT_DIR/Angelic_CSP.thy"
```

Normal fast reopen after the first build succeeds:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -R UTP-Angelic-CSP \
  "$PROJECT_DIR/Angelic_CSP.thy"
```

Use `-u`, not `-s`. The `-u` flag uses user heaps. The `-s` flag asks Isabelle to
use system heaps in the app bundle and is not appropriate for this local source
stack.

## (Optional) Open with VS Code

If you use the [unofficial Isabelle2025 VS Code extension](https://github.com/ponder-j/Isabelle-Vscode), 
configure the extension environment to use the same Isabelle profile and project
session:

```bash
export ISABELLE_IDENTIFIER="$UTP_PROFILE"
ISABELLE_VSCODIUM_ARGS='{"logic":"UTP-Angelic-CSP","logic_requirements":true,"options":["system_heaps=false"]}'
export ISABELLE_VSCODIUM_ARGS
```

The exact way to provide these variables depends on how you launch VS Code on
your machine. If VS Code was already open with a different Isabelle environment,
fully quit it and reopen the project after changing the environment.

## (Optional) Inspect Parent Sessions

For faster editable work in a parent repository with jEdit, open that
repository's main theory on top of its prebuilt parent session:

```bash
# UTP: edit UTP on top of fixed support sessions
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false Shallow_Expressions_Z Abstract_Prog_Syntax Z_Toolkit HOL-Algebra

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -l Shallow_Expressions_Z \
  -i Abstract_Prog_Syntax -i Z_Toolkit -i HOL-Algebra \
  -d "$PROJECT_DIR/deps/UTP" \
  "$PROJECT_DIR/deps/UTP/utp.thy"
```

```bash
# UTP-Designs: edit UTP-Designs on top of fixed UTP2
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP2

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -l UTP2 \
  -d "$PROJECT_DIR/deps/UTP-Designs" \
  "$PROJECT_DIR/deps/UTP-Designs/utp_designs.thy"
```

```bash
# UTP-Reactive: edit UTP-Reactive on top of fixed UTP-Designs
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP-Designs Circus_Toolkit

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -l UTP-Designs \
  -i Circus_Toolkit \
  -d "$PROJECT_DIR/deps/UTP-Reactive" \
  "$PROJECT_DIR/deps/UTP-Reactive/utp_reactive.thy"
```

```bash
# UTP-Reactive-Designs: edit UTP-Reactive-Designs on top of fixed UTP-Reactive
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP-Reactive

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -l UTP-Reactive \
  -d "$PROJECT_DIR/deps/UTP-Reactive-Designs" \
  "$PROJECT_DIR/deps/UTP-Reactive-Designs/utp_rea_designs.thy"
```
