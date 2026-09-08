# Semantic notes

These notes are retained from the research README. See
[paper coverage](PAPER_COVERAGE.md) for the theorem index.

## Semantic layers

The types describe observation alphabets; healthiness conditions identify the
predicates that belong to each semantic theory. In particular, a value of type
`angelic_design` need not satisfy design healthiness `H` merely because of its
type. RAD and AP use the same reactive angelic alphabet with different
healthiness conditions.

The representation adapters have distinct meanings:

- `PBMH` acts on state-to-choice relations. `PBMH_ades` applies the same choice
  closure inside the full design alphabet while preserving the outer control
  observations. `A2` also preserves those observations when it normalises
  behaviour through empty and singleton choices.
- Plain design-alphabet lifting adds observation fields to a predicate.
  `arel_to_ades P`, in contrast, constructs the design `true ⊢r P`, adding a
  contract with a true precondition.
- `aseq` composes state-to-choice relations. `aseq_ades` works on the full
  observation alphabet, whereas `angelic_design_seq` additionally hides the
  intermediate termination observation.
- `rad2csp_obs` and `csp2rad_obs` repackage reactive observations between the
  nested angelic alphabet and the flat CSP alphabet. Their inverse laws justify
  the adapters used by `rad_ac2p` and `rad_p2ac`.

## Qualifications to the mathematical source

The mechanisation records qualifications where the printed claims need extra
premises under the explicit observation semantics:

- Paper Theorem 6's reverse-mapping refinement needs `A3` in addition to
  `A`-healthiness. `A3` is the singleton-witness condition introduced in this
  development; `d2ac_ac2p_iff_A3` characterises exactly when that refinement
  holds on A-healthy designs. `P_dummy` is a counterexample to the unrestricted
  claim. The equality corresponding to Theorem 8 requires `A`, `A2`, and `A3`.
- Theorem 35's non-divergence characterisation is restricted to observations
  where initial `ok` is true. The theory `utp_rad_nd` contains both the guarded
  theorem and a counterexample to its unguarded version.
- `Skip_AD` is a left identity for H-healthy designs. For A-healthy designs,
  it is a right identity exactly when the precondition is independent of the
  final choice set, equivalently when the design is normal. This is the
  qualification in thesis Theorem T.4.5.8; `P_dummy` also demonstrates why an
  unrestricted right-identity law would fail.
- `ac2p P` evaluates `PBMH_ades P` at a singleton choice, with the observation
  adapters applied. Replacing this by direct singleton evaluation of `P`
  requires PBMH healthiness. Empty-choice behaviour therefore matters even
  though the target observation is a singleton.

The source definitions, qualified theorem statements, and counterexamples are
kept together in the corresponding theories. A successful Isabelle build
checks these stated claims; it does not remove their healthiness premises.

The correspondence APIs state their healthy carriers explicitly:
`ac2p_d2ac_galois` relates A- and A3-healthy angelic designs to H-healthy
designs, and `AP_RAD_galois` relates AP-healthy and RAD-healthy processes.
The associated closure laws establish that the mappings reach those carriers.
The general prefix normal forms are `Prefix_RAD_design` (thesis T.5.4.29)
and `Prefix_AP_design` (T.6.4.23). Their `prefix_handover` and
`prefix_continuation` predicates name the source's intermediate-state
calculations and preserve the outer control observations.
