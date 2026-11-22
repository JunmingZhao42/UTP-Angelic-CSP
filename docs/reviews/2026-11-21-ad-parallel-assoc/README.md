# Associativity of AD parallel beyond A2

Date: 2026-11-21. We want to know when `P ∥AD[j] Q` is associative for operands
with angelic choice. The settled cases are described in the
[AD guide](../../parallel/AD.md):
[`ades_par_assoc_det`](../../../angelic-designs/utp_ades_parallel_lift.thy#L459)
for a deterministic, mergeable `j`, and a counterexample for a nondeterministic `j`.
This folder keeps the evidence for the open case of a partial deterministic `j`.

## Brute-force checks

[`brute_force.py`](brute_force.py) checks every triple of AD operands at one started
prior, with any precondition and divergence:

| Merge | Result |
| --- | --- |
| deterministic, mergeable | no counterexample (2 states; 3 states sampled) |
| deterministic, partial | counterexample once an operand diverges |
| nondeterministic | counterexample, the one in the AD guide |

The partial case is associative for operands that never diverge. This was proved
only in a discarded scratch theory and is not kept here.

## Rebuilding

```sh
python3 -I docs/reviews/2026-11-21-ad-parallel-assoc/brute_force.py 2 partial
```
