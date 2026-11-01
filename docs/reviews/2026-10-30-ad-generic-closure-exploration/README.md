# Generic AD parallel closure exploration

Date: 2026-10-30. Scope: sufficient merge premises for healthiness of
`P ∥[M] Q`, where `M :: 's ades_merge_rel` is arbitrary. All results below
are proved in the isolated [scratch theory](scratch.thy).
No production theory, operator, plan, or existing guide was changed.

## Results

The scratch helper `merge_slice M l r` fixes the two complete branch output
observations and leaves the initial and final observations free:

```isabelle
merge_slice M l r ≡ (λ(x,z). ades_merge_eval M x l r z)
```

It has type `'s angelic_design`. A slice condition therefore applies the
existing AD healthiness condition to this relation; it is not healthiness of
the state merge `j`.

| Result for `P ∥[M] Q` | Operand premises | Merge premises | Scratch lemma |
| --- | --- | --- | --- |
| H1 | `P is H1`, `Q is H1` | `M is ADH1m` | `generic_H1` |
| H2 | None | `M is ADH2m` | `generic_H2` |
| H3 | None | `M is ADH3m` | `generic_H3` |
| A | `P is H1`, `Q is H1` | Every `merge_slice M l r` is A | `generic_A_slices` |
| A2 | None | Every `merge_slice M l r` is A2 | `generic_A2_slices` |
| A2 | `P is A2`, `Q is A2` | Branch reduction below, and every singleton-branch slice is A2 | `generic_A2_atoms` |
| A3 | `P is H1`, `Q is H1` | `M is ADH1m`, `M is ADH3m` | `generic_A3` |

These are sufficient rules. Necessity and minimality of their premises have
not been established. This is a generic theorem interface under exploration,
not a new public parallel operator or an installed bundle of merge
healthiness transformers.

## A and A3

For A, fixing the branch observations makes the accepted output relation
A-healthy. Existentially combining accepted branch pairs preserves the
started part of A; H1 on both operands supplies the unstarted case.
`constructed_A_slices` proves that every slice of `merge_ades j` is A for
arbitrary `j`.

For A3, `normal_AD_A3` proves the stronger general observation that an AD
relation satisfying H1 and H3 satisfies A3. Right-skip completion makes a
failure at one output choice set admit every final output. If every singleton
permits failure, any one of them therefore supplies failure at the empty set.
This avoids the need to combine different branch witnesses uniformly.

## A2: conditions that include our construction

Requiring every slice to be A2 gives a short generic closure theorem, but is
too restrictive for the constructed merge. `constructed_not_all_A2_slices`
proves this for a Boolean state merge that returns the left branch state:
with left choice set `UNIV` and terminating branches, the merge needs both
Boolean values in its output. No singleton output suffices. Thus the merge
slice is not A2, despite the existing A2 closure theorem for A2 operands.

The compatible generic rule uses these two merge premises instead.

**Branch reduction.** For all flags, states, and choice sets:

```isabelle
⟦ ades_merge_obs M b s0 a L d R c Z;
  L = {} ∨ x ∈ L;
  R = {} ∨ y ∈ R ⟧
⟹ ades_merge_obs M b s0 a {x} d {y} c Z
```

**Singleton-branch A2.** For all `a`, `x`, `d`, `y`:

```isabelle
merge_slice M (ades_output a {x}) (ades_output d {y}) is A2
```

A2 on an operand ensures that an accepted nonempty branch set contains an
accepted singleton. If the empty branch set is accepted, A2 implies that
every singleton is accepted; this explains the `L = {}` and `R = {}` cases.
Branch reduction preserves the merge when selecting those singleton branch
observations. The second premise then supplies the required empty-or-singleton
decomposition of the final choice set.

`constructed_reduce` and `constructed_A2_atoms` prove both premises for
`merge_ades j`, for every `j`. `recovered_constructed_A`,
`recovered_constructed_A2`, and `recovered_constructed_A3` recover the three
existing lifted closure results from the generic rules with their original
operand premises. No extra state-merge condition is needed.

## Why ADHM and ADH3m alone do not suffice

The scratch family `terminating_merge F` accepts every unstarted observation,
and otherwise requires a terminating output whose choice set satisfies an
arbitrary predicate `F`. It is ADHM- and ADH3m-healthy for every `F`.

With `true` in both branches (proved A- and A2-healthy):

- Choosing `F Z ≡ Z = {}` gives a parallel result that is not A.
- Choosing `F Z ≡ {False, True} ⊆ Z` gives a result that is not A2.

These are Isabelle proofs (`ADHM_ADH3m_not_A` and `ADHM_ADH3m_not_A2`), not
finite test results. Flag healthiness and completion cannot replace the
additional choice-set conditions.

## Validation and next step

The [PIDE snapshot](../../../audits/reviews/2026-10-30-ad-generic-closure-exploration/evidence/pide-scratch.json) records zero errors, warnings,
bad, failed, canceled, running, or unprocessed commands. No `sorry`, `oops`,
or proof-search commands remain in the final scratch source.

The isolated batch build passed (exit 0; 15 seconds elapsed). Batch evidence
is separate: [log](../../../audits/reviews/2026-10-30-ad-generic-closure-exploration/evidence/batch.log), [result](../../../audits/reviews/2026-10-30-ad-generic-closure-exploration/evidence/batch-result.json), and the isolated
[session ROOT](../../../audits/reviews/2026-10-30-ad-generic-closure-exploration/evidence/ROOT.txt). It checks the scratch theory on the existing
UTP-Angelic-Designs heap, without adding a session to the project ROOT.

During exploration, a broad automation call stalled and prevented updates in
the old task PIDE session. That session was restarted on the built AD heap;
the successful session is `ad-generic-explore-20261030`. The proof was
restructured and all results rechecked. This is not a fresh PIDE replay of all
downstream project theories.

The smallest useful next step is to agree the names and presentation of the
slice-A and two A2 merge conditions, then install these generic rules and
derive the existing lifted closure lemmas from them. Defining monotone,
idempotent merge transformers for every proposed Boolean condition is a
separate question; it is not claimed by this exploration.

Existing files and staged changes are preserved, as recorded by the
[baseline](../../../audits/reviews/2026-10-30-ad-generic-closure-exploration/evidence/before.json) and [preservation check](../../../audits/reviews/2026-10-30-ad-generic-closure-exploration/evidence/preservation.json).
Nothing was committed.
