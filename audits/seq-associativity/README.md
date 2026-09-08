# Sequential associativity audit

**Design sequential composition is not associative on the full A, RAD or AP
carriers.** This audit proves counterexamples and sufficient conditions for
associativity. Its [Isabelle theory](Sequential_Composition_Audit.thy) is a
separate session, outside the production imports.

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

These conditions are sufficient, not claimed to be weakest. A2 is not
necessary: the non-divergent cases retain angelic nondeterminism.

There is also a general one-way law, `seq_assoc_refine`:

$$
P ;_D (Q ;_D R) \;\sqsubseteq\; (P ;_D Q) ;_D R
$$

when **P is PBMH_ades-healthy**, including every A-, RAD- or AP-healthy P.
In this refinement order, acceptance by the left grouping implies acceptance
by the right grouping.

## Why the brackets matter

Write `P(i, x, o, C)` for initial `ok`, initial state, final `ok` and final
choice set. The audit's `ades_eval_seq` proves:

$$
(P ;_D Q)(i,x,o,C)
= \exists b.\;P(i,x,b,\{y\mid Q(b,y,o,C)\}).
$$

For fixed external observations, define

$$
S_{b,c}=\{y\mid Q(b,y,c,\{z\mid R(c,z,o,C)\})\}.
$$

Then the two groupings reduce to:

$$
\begin{aligned}
((P ;_D Q);_D R)(i,x,o,C)
  &= \exists b,c.\;P(i,x,b,S_{b,c}),\\
(P ;_D (Q ;_D R))(i,x,o,C)
  &= \exists b.\;P(i,x,b,S_{b,\mathrm{False}}\cup S_{b,\mathrm{True}}).
\end{aligned}
$$

With left grouping, one value of the second intermediate `ok` must work
for the choice set as a whole. With right grouping, different intermediate
states may use different values. A predicate requiring two available states
can accept the union while rejecting each set separately.

PBMH gives upward closure, which proves the one-way law. A2 gives the stronger
binary-union equation:

$$
P(i,x,o,X\cup Y)=P(i,x,o,X)\lor P(i,x,o,Y).
$$

That proves associativity when the **first** operand is A2-healthy.
Normality of the middle operand provides another route: its failure
condition is independent of the final choice set, so the `False` branch
is contained in the `True` branch.

## A small counterexample

Use a Boolean program state and these ordinary angelic designs:

$$
\begin{aligned}
P &= \mathrm{true}\;\vdash\;
       (\mathrm{False}\in ac'\land\mathrm{True}\in ac'),\\
Q &= (s\lor\mathrm{False}\notin ac')\;\vdash\;
       (s\land\mathrm{True}\in ac'),\\
R &= \mathrm{Skip}_{AD}
   = \mathrm{true}\;\vdash\;(s\in ac').
\end{aligned}
$$

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

## RAD and AP counterexamples

| Carrier | P | Q | R |
|---|---|---|---|
| RAD | Angelic choice of `Stop_RAD` and `PrefixSkip_RAD a` | `Chaos_RAD` | `Stop_RAD` |
| AP | Angelic choice of `Stop_AP` and `PrefixSkip_AP a` | `ChaosCSP_AP` | `Stop_AP` |

Here `PrefixSkip` means performing the event and then terminating.
The AP example specifically uses `ChaosCSP_AP`, the H1 image of
`Chaos_RAD`.

The checked example uses `a = ()` and both external `ok` flags true:

| Observation | Trace | Refusal | Waiting |
| --- | --- | --- | --- |
| Initial state | `[]` | `{}` | `False` |
| First final choice | `[]` | `{a}` | `True` |
| Second final choice | `[a]` | `{}` | `False` |

The waiting observation refuses `a`, so it cannot serve as the prefix's
offer of `a`. The prefix branch needs the observation after the event.
For both carriers, the left-grouped expression is false at this observation
and the right-grouped expression is true. The carrier theorems also prove
that every operand has the required healthiness.

The non-divergent fragment behaves better. For AP, the middle operand's
NDAP-healthiness gives a normal design, allowing the generic positive law.
For RAD, `NDRAD_seq_assoc` uses the existing H1/RA1 isomorphism and the
non-divergent sequential correspondence to transfer associativity from AP.

## Relation to the source definitions

The original audit (7 September 2026) compared paper Definitions 18–19
(p. 31) and thesis Definitions 95–96 (p. 116) with
[`angelic_design_seq`](../../angelic-designs/utp_ades_ops.thy). All hide the
intermediate `ok` outside auxiliary angelic composition, which substitutes
Q's possible initial states for the final choice set.

The audit found no unrestricted design-composition associativity theorem in
paper Section 5.2 or thesis Section 4.5.2. Their PBMH calculations concern
ordinary relational composition; `aseq_assoc` concerns the raw auxiliary
operator. Neither establishes associativity of design composition.

Keep the existing operator and its qualified laws. General expressions
cannot be silently rebracketed. Requiring A2 everywhere would exclude angelic
behaviour; changing the operator to obtain unrestricted associativity would
require a separate semantic review. The audit's positive laws are candidates
for later promotion into the production layers.

## Run the audit

From the repository root, set `ISABELLE` to the Isabelle2025-2 executable:

```sh
env ISABELLE_IDENTIFIER=utp-cleanup-2026-09-08 PROJECT_DIR="$PWD" \
  "$ISABELLE" build -b -d deps -d . -d audits/seq-associativity \
  -o system_heaps=false -o threads=4 Sequential_Composition_Audit
```

The session imports `Angelic_CSP`. It passed against the cleaned sources on
8 September 2026 (exit 0); see [baseline checks](../../docs/BASELINE.md) for
validation records. The audit proofs contain no `sorry`, `oops`, `metis` or
exploratory commands. All theory statements and proofs are unchanged by this
documentation edit.
