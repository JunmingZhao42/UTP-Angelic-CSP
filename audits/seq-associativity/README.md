# Sequential composition: associativity audit

Audit date: 7 September 2026.

**The design-level sequential operator is not associative on the full A,
RAD, or AP carriers.** The accompanying Isabelle theory proves concrete
counterexamples and several sufficient conditions for associativity.
The implementation matches the literal sequential definitions in the source;
this finding does not call for another change to A2.

All existing implementation files, including every parallel file, were
preserved. This directory is a separate audit session, outside the production
session roots.

## Results

Write `P ;D Q` for `angelic_design_seq`, printed in Isabelle as
`P ;;\<^sub>D\<^sub>A Q`. The RAD abbreviation denotes this same operator,
and AP also uses it.

| Operator or assumptions | Associative? | Isabelle evidence |
|---|---|---|
| Raw relation composition `;;A` | Yes, unconditionally | Existing `aseq_assoc` |
| Full-alphabet auxiliary composition `;;AD` | Yes, unconditionally | `full_alphabet_aseq_assoc` |
| Design composition `;D`, all three operands A-healthy | No | `A_seq_not_associative` |
| Design composition `;D`, all three operands RAD-healthy | No | `RAD_carrier_not_associative` |
| Design composition `;D`, all three operands AP-healthy | No | `AP_carrier_not_associative` |
| First operand A2-healthy | Yes; no assumptions on the other two | `seq_assoc_first_A2` |
| First operand PBMH-healthy; middle operand a normal design | Yes; no assumption on the third | `seq_assoc_middle_normal` |
| First and middle operands AP-healthy; middle also NDAP-healthy | Yes; no assumption on the third | `AP_seq_assoc_middle_NDAP` |
| All three operands RAD- and NDRAD-healthy | Yes | `NDRAD_seq_assoc` |

These are sufficient conditions, not a claim that the weakest possible
conditions have been characterised. In particular, A2 is not necessary:
the non-divergent results retain angelic nondeterminism.

There is also a general one-way law, `seq_assoc_refine`:

\[
P ;_D (Q ;_D R) \;\sqsubseteq\; (P ;_D Q) ;_D R
\]

provided **P is PBMH_ades-healthy**. In the repository's refinement order,
this means that acceptance by the left-grouped expression implies acceptance
by the right-grouped expression. A-, RAD-, and AP-healthiness each imply
this PBMH condition, so this refinement applies on all three carriers.

## Why the brackets matter

The audit's `ades_eval` merely displays the existing observation records as
`P(i, x, o, C)`: initial `ok`, initial state, final `ok`, and final choice set.
It introduces no new process semantics. The checked equation `ades_eval_seq`
is:

\[
(P ;_D Q)(i,x,o,C)
= \exists b.\;P(i,x,b,\{y\mid Q(b,y,o,C)\}).
\]

For fixed external observations, define

\[
S_{b,c}=\{y\mid Q(b,y,c,\{z\mid R(c,z,o,C)\})\}.
\]

Then the two groupings reduce to:

\[
\begin{aligned}
((P ;_D Q);_D R)(i,x,o,C)
  &= \exists b,c.\;P(i,x,b,S_{b,c}),\\
(P ;_D (Q ;_D R))(i,x,o,C)
  &= \exists b.\;P(i,x,b,S_{b,\mathrm{False}}\cup S_{b,\mathrm{True}}).
\end{aligned}
\]

With left grouping, one value of the second intermediate `ok` must work
for the choice set as a whole. With right grouping, different intermediate
states may use different values. A predicate requiring two available states
can accept the union while rejecting each set separately.

PBMH gives upward closure, which proves the one-way law. A2 gives the stronger
binary-union equation:

\[
P(i,x,o,X\cup Y)=P(i,x,o,X)\lor P(i,x,o,Y).
\]

That proves associativity when the **first** operand is A2-healthy.
Normality of the middle operand provides another route: its failure
condition is independent of the final choice set, so the `False` branch
is contained in the `True` branch.

## A small counterexample

Use a Boolean program state and these ordinary angelic designs:

\[
\begin{aligned}
P &= \mathrm{true}\;\vdash\;
       (\mathrm{False}\in ac'\land\mathrm{True}\in ac'),\\
Q &= (s\lor\mathrm{False}\notin ac')\;\vdash\;
       (s\land\mathrm{True}\in ac'),\\
R &= \mathrm{Skip}_{AD}
   = \mathrm{true}\;\vdash\;(s\in ac').
\end{aligned}
\]

All three are A-healthy, as proved in the audit. Q is also A2-healthy:
putting A2 on the middle operand does not suffice.

At `ok = True`, `s = True`, `ok' = True`, and `ac' = {True}`:

| Expression | Predicate value |
|---|---|
| `(P ;D Q) ;D R` | `False` |
| `P ;D (Q ;D R)` | `True` |

P requires both Boolean intermediate states. Q can account for `False`
through failure and `True` through successful continuation. Right grouping
allows those two explanations to coexist inside P's choice set.

## Counterexamples using the existing reactive operators

The failure persists after imposing the reactive healthiness conditions.
No new primitive process is needed:

| Carrier | P | Q | R |
|---|---|---|---|
| RAD | Angelic choice of `Stop_RAD` and `PrefixSkip_RAD a` | `Chaos_RAD` | `Stop_RAD` |
| AP | Angelic choice of `Stop_AP` and `PrefixSkip_AP a` | `ChaosCSP_AP` | `Stop_AP` |

Here `PrefixSkip` means performing the event and then terminating.
The AP example specifically uses `ChaosCSP_AP`, the H1 image of
`Chaos_RAD`.

The checked example uses the unit event `a = ()`. Both external `ok` flags
are true. Its initial state is:

- trace `[]`, refusal `{}`, waiting `False`.

Its final choice set contains these two observations:

- trace `[]`, refusal `{a}`, waiting `True`;
- trace `[a]`, refusal `{}`, waiting `False`.

The waiting observation refuses `a`, so it cannot serve as the prefix's
offer of `a`. The prefix branch needs the observation after the event.
For both carriers, the left-grouped expression is false at this observation
and the right-grouped expression is true. The carrier theorems also prove
that every operand has the required healthiness.

The non-divergent fragment behaves better. For AP, the middle operand's
NDAP-healthiness gives a normal design, allowing the generic positive law.
For RAD, `NDRAD_seq_assoc` uses the existing H1/RA1 isomorphism and the
non-divergent sequential correspondence to transfer associativity from AP.

## Comparison with the mathematical source

The source definitions were checked directly, including rendered PDF pages:

- [Paper, p. 31, Definitions 18–19](/Users/ming/AI-summer/angelic-paper.pdf):
  design composition existentially hides `ok0` outside the auxiliary
  angelic composition; the auxiliary operation substitutes a set of
  possible initial states of Q for `ac'`.
- [Thesis, p. 116, Definitions 95–96](/Users/ming/AI-summer/angelic-thesis.pdf):
  the same construction and quantifier placement.
- [Current implementation](/Users/ming/AI-summer/repos/UTP-Angelic-CSP/angelic-designs/utp_ades_ops.thy:261):
  `angelic_design_seq` threads precisely these observations.

I found no unrestricted design-composition associativity theorem in paper
Section 5.2 or thesis Section 4.5.2. The occurrences of associativity in
the sources' PBMH calculations concern ordinary relational composition.
The repository's existing `aseq_assoc` concerns the raw auxiliary operator.
Neither establishes associativity of `;D`.

Thus this is a limitation of the literal definition on the broad healthy
carriers, rather than evidence that the Isabelle wrapping code mistranslates
that definition. It does not refute a numbered associativity theorem in
those source sections.

## Recommendation and validation

Keep the source-faithful operator. Promote the qualified associativity
theorems and the one-way refinement law into the appropriate AD/RAD/AP
layers, and retain the counterexamples as regression evidence. Do not
introduce an unconditional associativity rewrite or silently rebracket
general process expressions.

Requiring A2 everywhere would exclude the angelic behaviour that this
development is intended to model. A fully associative operator on the
entire carrier would require a separate semantic design decision and a
fresh audit of closure, normal forms, examples, and correspondence laws.

The evidence is in
[Sequential_Composition_Audit.thy](Sequential_Composition_Audit.thy).
The standalone session imports the current `Angelic_CSP` development.
Its proofs contain no `sorry`, `oops`, `metis`, or exploratory proof commands.

The saved session passed with Isabelle2025-2 on 7 September 2026, in about
11 seconds including startup. SHA-256 comparisons confirmed that all 29
baseline files, including all eight parallel files, were unchanged.

From the repository root, with `ISABELLE` set to the Isabelle2025-2 executable:

```sh
env ISABELLE_IDENTIFIER=utp-cleanup-2026-09-08 PROJECT_DIR="$PWD" \
  "$ISABELLE" build -b -d deps -d . -d audits/seq-associativity \
  -o system_heaps=false -o threads=4 Sequential_Composition_Audit
```

The cleanup copy uses `lemma` for the audit results, following the repository
convention for results that are not numbered theorems in the paper. Statements
and proofs are unchanged from the preserved audit.

Checked against the cleanup sources on 8 September 2026 with Isabelle2025-2.
The standalone session completed successfully (exit 0).
