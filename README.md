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

### This Week

- [ ] Finish reading the angelic-process paper with implementation notes.
  Focus on the definitions that will become Isabelle constants first: `PBMH`,
  `A0`, `A1`, `A`, `RA1`, `RA2`, `II_Rac`, `RA3`, `CSPA1`, `CSPA2`, `RAD`,
  `II_AP`, `RA3AP`, and `AP`.
- [ ] Define the first angelic state space/alphabet.
  Start by reusing the existing Isabelle/UTP alphabet and lens machinery rather
  than introducing a separate raw state model. The first design decision is how
  to represent the angelic choice variable `ac`, probably as a set of final
  reactive states.
- [ ] Mechanise the first healthiness conditions.
  Start with angelic designs (`A0`, `A1`, and `A`) before moving to reactive
  angelic designs. For each condition, aim for the standard Isabelle/UTP facts:
  monotonicity and idempotence.

### Reading Focus

For the state-space task, read:

- Paper definitions 16, 26, and 47: these specify the alphabets for angelic
  designs, reactive angelic designs, and angelic processes.
- [`utp_rea_core.thy`](../UTP-Reactive/utp_rea_core.thy): existing reactive
  alphabet with `ok`, `wait`, and `tr`.
- [`utp_rea_prog.thy`](../UTP-Reactive/utp_rea_prog.thy): stateful reactive
  alphabet with program state `st`.
- [`utp_sfrd_core.thy`](../UTP-Reactive-Designs/stateful-failure/utp_sfrd_core.thy):
  stateful failure alphabet with `tr`, `ref`, `wait`, and `st`.

For the healthiness-condition task, read:

- Paper definitions 17, 27-35, and 46-48, plus Appendix A.1-A.2 for the
  monotonicity, idempotence, and commutation facts used by the lattice results.
- [`utp_healthy.thy`](../UTP/utp_healthy.thy): Isabelle/UTP definitions of
  `Idempotent`, `Monotonic`, `Healthy`, and related closure attributes.
- [`utp_theory.thy`](../UTP/utp_theory.thy): how idempotent and monotonic
  healthiness functions induce complete lattices.
- [`Simple_Time_Theory.thy`](../UTP/examples/Simple_Time_Theory.thy): a small
  worked example of defining and proving healthiness properties.
- [`utp_des_healths.thy`](../UTP-Designs/utp_des_healths.thy): design
  healthiness conditions `H1` and `H2`.
- [`utp_rea_healths.thy`](../UTP-Reactive/utp_rea_healths.thy): reactive
  healthiness conditions and the local proof style for monotonicity,
  idempotence, and composition.

### Implementation Tasks

- [ ] Add a theory section for the angelic alphabet and type synonyms.
- [ ] Add `term` probes for the existing reactive-design variables and for the
  proposed `ac` representation.
- [ ] Define a small helper for non-empty angelic choices, corresponding to
  `ac != {}` in the paper.
- [ ] Define `A0` and prove `A0_mono` and `A0_idem`.
- [ ] Define `A1`; if `PBMH` is not already available in the parent theories,
  first introduce only the weakest useful placeholder or local definition.
- [ ] Define `A = A0 o A1` and prove the composed monotonicity/idempotence facts
  only after the component facts are stable.
- [ ] Then move to `RA1`, `RA2`, `II_Rac`, and `RA3`.
