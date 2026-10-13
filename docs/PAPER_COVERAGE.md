# Paper coverage

This is the repository-wide coverage index for Ribeiro and Cavalcanti's
[*Angelic processes for CSP via the UTP*](https://doi.org/10.1016/j.tcs.2018.10.008)
(TCS 756, 2019, pp. 19–63). Ribeiro's
[*Angelic Processes* thesis](https://arxiv.org/abs/1505.04726v2) supplies supporting
proofs and additional laws.

The layer guides own the formulas, exact premises, thesis cross-references and
links to Isabelle declarations. This index records where to find them.

## Layer coverage

| Layer guide | Paper definitions | Main theorems | Additional numbered results |
| --- | --- | --- | --- |
| [AD: angelic designs](AD.md) | D15–25 | T3–8 | T64–65, T72; L3–4, L15–18, L24–26 |
| [RAD: reactive angelic designs](RAD.md) | D26–45 | T9–35 | T66–71; L5–9, L19–23; Ex11–21 |
| [AP: angelic processes](AP.md) | D46–57 | T36–63 | L10–14; Ex22–28 |

All theorem and lemma entries above have corresponding Isabelle facts, with the
qualifications below. Types specify alphabets; healthiness premises specify the
carriers on which the laws hold. An alphabet type alone does not imply design
healthiness.

## Find a result

| Topic | AD | RAD | AP |
| --- | --- | --- | --- |
| Alphabet and notation | [AD alphabet](AD.md#alphabet-and-notation) | [Reactive alphabet](RAD.md#alphabet-and-notation) | [Shared RAD alphabet](AP.md#alphabet-and-notation) |
| Healthiness and normal forms | [A0–A3](AD.md#healthiness-definitions) | [RA1–RA3 and RAD](RAD.md#healthiness-definitions) | [RA3AP and AP](AP.md#healthiness-definitions) |
| Mapping laws | [Ordinary designs](AD.md#mapping-ordinary-designs-and-predicates) | [Ordinary reactive predicates](RAD.md#direct-correspondence-with-ordinary-reactive-predicates) | [AP–RAD correspondence](AP.md#correspondence-with-rad) |
| Operators and closure | [AD operators](AD.md#operators-and-sequential-laws) | [RAD operators](RAD.md#process-operators) | [AP operators](AP.md#process-operators) |
| Non-divergence | — | [NDRAD](RAD.md#non-divergence) | [NDAP](AP.md#non-divergence) |
| Examples | [Mapping counterexample](AD.md#paper-mapping-theorems) | [RAD examples](RAD.md#worked-examples-and-numbered-lemmas) | [AP examples](AP.md#worked-examples) |

## Qualifications and scope

| Source claim | Qualification | Details and evidence |
| --- | --- | --- |
| AD T6 and T8 | The reverse mapping needs A3 in addition to the stated A / A2 premises. | [AD mapping theorems and counterexample](AD.md#paper-mapping-theorems) |
| RAD T35 | The universal failure test is guarded by initial `ok = True`. | [NDRAD characterisation and counterexample](RAD.md#non-divergence) |
| Appendix T67 | Requires an H-healthy design, not merely a predicate on the design alphabet. | [RAD healthiness algebra](RAD.md#idempotence-monotonicity-and-closure) |
| Appendix T68 | The printed statement repeats one side; the mechanisation states the commutation law established by its proof. | [RAD healthiness algebra](RAD.md#idempotence-monotonicity-and-closure) |
| Thesis T.4.5.8 | Right identity with Skip requires normality on the A carrier. | [AD identity laws](AD.md#operators-and-sequential-laws) |

Paper T1–2 and L1–2 are background results, not separately numbered claims in
this development. D22 uses typed records, lenses and ordinary substitution;
Appendix L27–28's general alphabet calculus has no separate named mechanisation.
The [AD guide](AD.md#remaining-appendix-lemmas) records that boundary.

The guides include supporting closure, Galois and prefix laws, but do not claim
complete mechanisation of every theorem in the thesis. General reassociation
must not be inferred from sequential closure or correspondence. In particular,
AP T63 does not require an associativity assumption or the standalone audit.

Parallel-by-merge and the standalone associativity audit are outside the paper
baseline. See [parallel research](../PARALLEL.md), the
[research boundary](RESEARCH_BOUNDARY.md), and [baseline checks](BASELINE.md).
