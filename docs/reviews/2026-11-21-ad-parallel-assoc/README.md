# Associativity of AD parallel beyond A2

Date: 2026-11-21. We want to know when `P ∥AD[j] Q` is associative for operands
with angelic choice. The installed laws
[`ades_par_assoc`](../../../angelic-designs/utp_ades_parallel_lift.thy#L351) and
[`ades_par_assoc_nd`](../../../angelic-designs/utp_ades_parallel_lift.thy#L368)
need all operands `A2`, so they only cover operands without angelic choice.

## Installed result

[`ades_par_assoc_det`](../../../angelic-designs/utp_ades_parallel_lift.thy#L651)
needs no operand premise when `j` is
deterministic ([`Functional`](../../../deps/UTP/utp_rel.thy#L264)) and
[`mergeable`](../../../deps/UTP/utp_concurrency.thy#L64), symmetric and associative:

```isabelle
(P ∥AD[j] Q) ∥AD[j] R = P ∥AD[j] (Q ∥AD[j] R)
```

## Counterexample for a nondeterministic merge

[`AD_Assoc_Counterexample.thy`](AD_Assoc_Counterexample.thy) shows that the `A2`
premise cannot simply be dropped. States are booleans, and the merge
[`jnd`](AD_Assoc_Counterexample.thy#L11) has `j(0,x) = {x}` and `j(1,1) = {0,1}`.
It is symmetric, associative and mergeable, but not deterministic.

```isabelle
⟨1⟩ ∥ ⟨1⟩ = ⟨0⟩ ⊓ ⟨1⟩
⟨1⟩ ∥ (⟨0⟩ ⊔ ⟨1⟩) = ⟨1⟩
(⟨0⟩ ⊓ ⟨1⟩) ∥ (⟨0⟩ ⊔ ⟨1⟩) = ⟨1⟩
```

So the left bracketing of `⟨1⟩ ∥ ⟨1⟩ ∥ (⟨0⟩ ⊔ ⟨1⟩)` is `⟨1⟩` and the right one is
`⟨0⟩ ⊓ ⟨1⟩` ([`ades_par_not_assoc_nondet`](AD_Assoc_Counterexample.thy#L147)).
Only the third operand is not `A2`. Here `⟨v⟩` is the assignment `assigns_ades 1⇩L v`.

## Brute-force checks

[`brute_force.py`](brute_force.py) checks every triple of AD operands at one started
prior, with any precondition and divergence:

| Merge | Result |
| --- | --- |
| deterministic, mergeable | no counterexample (2 states; 3 states sampled) |
| deterministic, partial | counterexample once an operand diverges |
| nondeterministic | counterexample, the merge above |

The partial case is associative for operands that never diverge. This was proved
only in a discarded scratch theory and is not kept here.

## Rebuilding

From the repository root, with the patched Isabelle2026 profile:

```sh
PROJECT_DIR="$PWD" ISABELLE_IDENTIFIER=utp-2026-patched timeout 600s \
  "$HOME/Applications/Isabelle2026-patched.app/bin/isabelle" build -o timeout=120 \
  -d deps -d . -d docs/reviews/2026-11-21-ad-parallel-assoc AD_Assoc_Counterexample
```

```sh
python3 -I docs/reviews/2026-11-21-ad-parallel-assoc/brute_force.py 2 nondet
```
