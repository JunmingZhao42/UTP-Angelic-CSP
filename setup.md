# Isabelle Setup

This project is intended to use a plain Isabelle2025 installation with a separate
Isabelle user profile for the local UTP source stack.
I have only tested the setup on macOS.

## What You Need

This setup uses three pieces:

1. A plain `Isabelle2025.app`, used as the Isabelle executable. Download it
   from [the Isabelle2025 distribution page](https://isabelle.in.tum.de/website-Isabelle2025/dist/).
2. A `Isabelle2025-CyPhyAssure.app` bundle, used for support session
   sources such as `Optics`, `Shallow-Expressions`, `Z_Toolkit`, and
   `Circus_Toolkit`. Download it from
   [the Isabelle/UTP download page](https://isabelle-utp.york.ac.uk/download).
3. Editable source clones in `$PROJECT_DIR/repos`, including the UTP stack and
   this project.

## Project Setup

Set up these environment variables to match your machine:

```bash
export PROJECT_DIR="$HOME/path/to/project"
export ISABELLE="$PROJECT_DIR/Isabelle2025.app/bin/isabelle"
export UTP_PROFILE="Isabelle2025-utp"
```

Here `PROJECT_DIR` is the directory that contains the Isabelle apps and the
`repos` directory. `UTP_PROFILE` is the name of the isolated Isabelle user
profile for this project. 

Create the project root and the `repos` directory:

```bash
mkdir -p "$PROJECT_DIR/repos"
cd "$PROJECT_DIR/repos"
```

All source repositories below should be cloned directly inside
`$PROJECT_DIR/repos`.

Clone the editable UTP stack:

```bash
git clone https://github.com/isabelle-utp/Abstract_Prog_Syntax.git
git clone https://github.com/isabelle-utp/UTP.git
git clone https://github.com/isabelle-utp/UTP-Designs.git
git clone https://github.com/isabelle-utp/UTP-Reactive.git
git clone https://github.com/isabelle-utp/UTP-Reactive-Designs.git
```

Clone this project from your own repository or fork:

```bash
git clone <your-UTP-Angelic-CSP-repo-url> UTP-Angelic-CSP
```

The expected directory layout is:

```text
$PROJECT_DIR/
  Isabelle2025.app
  Isabelle2025-CyPhyAssure.app
  repos/
    Abstract_Prog_Syntax/
    UTP/
    UTP-Designs/
    UTP-Reactive/
    UTP-Reactive-Designs/
    UTP-Angelic-CSP/
```

The current working setup uses the `main` branch of the cloned repositories.

## Isabelle Profile

Create one isolated Isabelle profile for this source stack:

```bash
mkdir -p "$HOME/.isabelle/$UTP_PROFILE/etc"
```

This profile keeps ROOTS, settings, and build products separate from the default
`Isabelle2025` profile and from the CyPhyAssure app profile.

Install the repo copy of `ROOTS` into the Isabelle profile:

```bash
cp "$PROJECT_DIR/repos/UTP-Angelic-CSP/isabelle-profile/ROOTS" \
  "$HOME/.isabelle/$UTP_PROFILE/ROOTS"
```

Install the recommended Isabelle settings:

```bash
cp "$PROJECT_DIR/repos/UTP-Angelic-CSP/isabelle-profile/settings" \
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
  "$PROJECT_DIR/repos/UTP-Angelic-CSP/Angelic_CSP.thy"
```

Normal fast reopen after the first build succeeds:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -R UTP-Angelic-CSP \
  "$PROJECT_DIR/repos/UTP-Angelic-CSP/Angelic_CSP.thy"
```

Use `-u`, not `-s`. The `-u` flag uses user heaps. The `-s` flag asks Isabelle to
use system heaps in the app bundle and is not appropriate for this local source
stack.

## (Optional) Open with VS Code

If you use the [unofficial Isabelle2025 VS Code extension](https://github.com/ponder-j/Isabelle-Vscode), 
set up the below environment and launch vscode:

```bash
ISABELLE_HOME="$PROJECT_DIR/Isabelle2025.app"
ISABELLE_IDENTIFIER="$UTP_PROFILE"
ISABELLE_VSCODIUM_ARGS='{"logic":"UTP-Angelic-CSP","logic_requirements":true,"options":["system_heaps=false"]}'

```

If VS Code was already open with a different Isabelle environment, fully quit VS
Code and run `utp-vscode` from a fresh shell. The function opens a new VS Code
window for this project.

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
  -d "$PROJECT_DIR/repos/UTP" \
  "$PROJECT_DIR/repos/UTP/utp.thy"
```

```bash
# UTP-Designs: edit UTP-Designs on top of fixed UTP2
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP2

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -l UTP2 \
  -d "$PROJECT_DIR/repos/UTP-Designs" \
  "$PROJECT_DIR/repos/UTP-Designs/utp_designs.thy"
```

```bash
# UTP-Reactive: edit UTP-Reactive on top of fixed UTP-Designs
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP-Designs Circus_Toolkit

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -l UTP-Designs \
  -i Circus_Toolkit \
  -d "$PROJECT_DIR/repos/UTP-Reactive" \
  "$PROJECT_DIR/repos/UTP-Reactive/utp_reactive.thy"
```

```bash
# UTP-Reactive-Designs: edit UTP-Reactive-Designs on top of fixed UTP-Reactive
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP-Reactive

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -l UTP-Reactive \
  -d "$PROJECT_DIR/repos/UTP-Reactive-Designs" \
  "$PROJECT_DIR/repos/UTP-Reactive-Designs/utp_rea_designs.thy"
```
