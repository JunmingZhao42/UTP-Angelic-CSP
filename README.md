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

This repository depends on the existing Isabelle/UTP stack rather than copying
its theories. The expected sibling repositories are:

- [isabelle-utp/UTP](https://github.com/isabelle-utp/UTP)
- [isabelle-utp/UTP-Designs](https://github.com/isabelle-utp/UTP-Designs)
- [isabelle-utp/UTP-Reactive](https://github.com/isabelle-utp/UTP-Reactive)
- [isabelle-utp/UTP-Reactive-Designs](https://github.com/isabelle-utp/UTP-Reactive-Designs)

## Setup

See [setup.md](setup.md) for the machine setup, expected repository layout,
Isabelle profile files, and commands for opening this project or inspecting the
parent sessions.

The normal editable open command, after the first build succeeds, is:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -R UTP-Angelic-CSP \
  "$PROJECT_DIR/repos/UTP-Angelic-CSP/Angelic_CSP.thy"
```

For VS Code, use the helper shell functions documented in `setup.md` if they
are installed in the local shell profile.

## Todo

### This Week (Week 2)

- [ ] Finish reading the angelic-process paper with implementation notes.
  Focus on section 5 of angelic designs.
- [ ] Mechanise section 5.1.
  - [ ] Define the first angelic state space/alphabet.
  - [ ] Mechanise the first healthiness conditions.
  For each condition, prove monotonicity and idempotence.
- [ ] Finish draft plan for the fellowship.
