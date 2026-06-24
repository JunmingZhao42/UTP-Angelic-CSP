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

## Isabelle/UTP Stack

This repository depends on the Isabelle/UTP stack through pinned git
submodules under `deps/`:

- [isabelle-utp/Abstract_Prog_Syntax](https://github.com/isabelle-utp/Abstract_Prog_Syntax)
- [isabelle-utp/UTP](https://github.com/isabelle-utp/UTP)
- [isabelle-utp/UTP-Designs](https://github.com/isabelle-utp/UTP-Designs)
- [isabelle-utp/UTP-Reactive](https://github.com/isabelle-utp/UTP-Reactive)
- [isabelle-utp/UTP-Reactive-Designs](https://github.com/isabelle-utp/UTP-Reactive-Designs)

Use `git clone --recurse-submodules` or `git submodule update --init
--recursive` so that the checked-out dependency versions match the known-good
commit pointers recorded by this repository.

## Setup

See [setup.md](setup.md) for the machine setup, expected repository layout,
Isabelle profile files, and commands for opening this project or inspecting the
parent sessions.

The normal editable open command, after the first build succeeds, is:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -R UTP-Angelic-CSP \
  "$PROJECT_DIR/Angelic_CSP.thy"
```

For VS Code, configure the Isabelle extension environment as described in
`setup.md`.

## Todo

### This Week (Week 2)

- [ ] Finish reading the angelic-process paper with implementation notes.
  Focus on section 5 of angelic designs.
- [ ] Mechanise section 5.1.
  - [ ] Define the first angelic state space/alphabet.
  - [ ] Mechanise the first healthiness conditions.
  For each condition, prove monotonicity and idempotence.
- [ ] Finish draft plan for the fellowship.

## Plan

### 1. Angelic Designs
Mechanise Section 5.
- Healthiness:
  - A0, PBMH, A1, and A.
  - Complete-lattice result.
- Operators:
  - Sequential composition.
  - Skip, assignment, demonic choice, and angelic choice.
  - A2 and other lemmas.
- Correspondence with extended binary multirelations and ordinary designs.

### 2. Reactive Angelic Designs
Mechanise Section 6.
- Healthiness:
  - RAD healthiness conditions.
  - Lattice and closure results.
- Operators:
  - Chaos, Stop, Skip, sequence, choice, prefixing, and external choice.
- Correspondence:
  - Relationship with existing reactive-design or CSP models.
  - Preservation of the Section 6 operators.

### 3. Angelic Processes
Mechanise Section 7.
- Healthiness:
  - AP and NDAP healthiness conditions.
  - Lattice and closure results.
- Operators:
  - Process-level choice, Stop, Skip, sequence, prefixing, and
    divergence-related operators.
  - Closure and algebraic laws.
- Correspondence:
  - Relationship with RAD and CSP process models.

### 4. Investigate other properties
- Parallel operator:
  - Algebraic laws such as commutativty, associativity and monoticity etc.
