# AD merge premises as healthiness transformers

> Installed on 2 November 2026 under new names: `AM` is `Am`, `ATM` is
> `A2m_atoms`, `BRM` is `A2m_reduce` and `A2M` is `A2m`; `atom_branch` and
> `selects` became `singleton_output` and `selects_singleton`. The scratch below
> keeps the old names and no longer loads. See the [AD guide](../../parallel/AD.md).

The generic A and A2 closure premises can be expressed exactly as fixed points of monotone, idempotent transformers on `'s ades_merge_rel`. The names below are provisional scratch names. No production theory or existing healthiness definition was changed.

## A: apply A to each merge slice

`merge_slice M l r` fixes the two branch observations and leaves the initial and final AD observations free. Define `AM` by:

```isabelle
merge_slice (AM M) l r = A (merge_slice M l r)
```

The scratch proves `Monotonic AM`, `Idempotent AM`, and:

```isabelle
M is AM ⟷ (∀l r. merge_slice M l r is A)
```

Consequently, `P is H1`, `Q is H1`, and `M is AM` imply that parallel by merge with M is A-healthy. This repackages the previous sufficient merge premise exactly; it does not assert necessity for all possible parallel closure rules.

## A2: normalise singleton slices, then enforce branch reduction

`ATM` applies A2 to slices with two singleton branch choice sets and leaves all other slices unchanged. The branch termination flags are unrestricted.

`BRM` retains an accepted merge observation only if it is also accepted with every selected singleton branch pair, keeping the initial observation, branch flags and final observation unchanged. A state x is selectable from L when `L = {} ∨ x ∈ L`; the empty-set case therefore quantifies over every x.

Define `A2M M ≡ BRM (ATM M)`. The scratch proves monotonicity and idempotence of both component transformers and of A2M. It also proves:

```isabelle
M is A2M ⟷ (M is ATM) ∧ (M is BRM)
```

`ATM_fixed_obs` and `BRM_fixed_obs` identify these two fixed-point conditions with exactly the singleton-slice and branch-reduction premises of `generic_A2_atoms` in the previous exploration.

The key idempotence argument is that BRM leaves singleton branch slices unchanged. Thus BRM preserves the A2 healthiness installed by ATM; the composite is fixed by both components after one application. No commutation claim is needed.

Consequently, `P is A2`, `Q is A2`, and `M is A2M` imply that parallel by merge with M is A2-healthy. Requiring A2 on every branch slice would be stronger and is not the condition used here.

## Compatibility and scope

`constructed_AM` and `constructed_A2M` prove that `merge_ades j` satisfies both conditions for every j. Together with its existing ADH1m/ADH2m/ADH3m theorems, this supplies a common family satisfying all those merge conditions. The generic closure theorems themselves quantify over M and require no state-level j.

This investigation does not prove that AM and A2M commute, or that either preserves every existing merge-healthiness condition on arbitrary input M. Such preservation results would be needed before claiming an arbitrary composition of all transformers is a single idempotent normalisation recipe.

## Evidence

- [Scratch source](scratch.thy), importing the previous generic-closure scratch. The file is an evidence copy, not a production theory.
- [PIDE state](../../../audits/reviews/2026-10-30-ad-merge-healthiness/pide.json): zero errors, warnings, unfinished or failed commands; 325 commands finished.
- [Isolated batch log](../../../audits/reviews/2026-10-30-ad-merge-healthiness/batch.log) and [session ROOT](../../../audits/reviews/2026-10-30-ad-merge-healthiness/ROOT.txt): passed with exit code 0, 15 seconds total; the new theory took 1.000 seconds cumulative processing time. This is separate from PIDE evidence.
- [Validation record](../../../audits/reviews/2026-10-30-ad-merge-healthiness/validation.json): batch exit code, source preservation and absence of proof placeholders or search commands.
- [Source hashes](../../../audits/reviews/2026-10-30-ad-merge-healthiness/source-hashes.json): project theory hashes recorded for the batch check; no project `.thy` file was edited by this investigation.

The isolated session uses the current `UTP-Angelic-Designs` heap. It is not a fresh build of the full project. The proof source contains no `sorry`, `oops`, or retained proof-search commands.

## Resuming this work

The scratch imports the [generic closure scratch](../2026-10-30-ad-generic-closure-exploration/scratch.thy),
which imports `UTP-Angelic-Designs.utp_ades_parallel`. Restore both `scratch.thy`
files into fresh scratch theories, keeping their theory names, and recheck. The
isolated batch check used:

```sh
ISABELLE_IDENTIFIER=utp-2025-2 /Applications/Isabelle2025-2.app/bin/isabelle build \
  -v -b -o system_heaps=false -o threads=2 -d deps -d . \
  -D <directory holding the session ROOT>
```

Do not use bare `s` as a state variable: it is an existing lens constant. Keep
proof edits incremental; a broad automation call stalled an earlier session.
