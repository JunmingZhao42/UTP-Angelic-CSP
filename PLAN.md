# Parallel-by-merge plan

Goal: parallel operators built from a shared state-merge policy `j`, with D/AD
and RD/RAD round-trip correspondence on their stated healthy domains.
For general angelic operands these require A/A2 for AD and RAD/A2 for RAD;
correspondence outside A2 remains open.

**Current focus: ordinary RD/RAD parallel.** The D/AD developments are retained.
The ordinary RD lifting is ORDm-healthy, and RAD lifts that same completed
ordinary merge to choice sets. The flat RD/RAD mapping, healthy closure and
scoped associativity are installed. The stateful development retains a
unit-state comparison with upstream `M_R`; the isabelle-utp core theory is
unchanged.
The [ordinary RD guide](docs/parallel/RD.md) records the current interface; the
[stateful RD guide](docs/parallel/RD-stateful.md) retains the earlier results.
Stage 0b publication and the remaining Stage 1 and Stage 2 tasks are separate
from the flat RD/RAD correspondence.

## Route and proof obligations

Use the same `j` within each ordinary/angelic pair; the two pairs have different
state alphabets. The selected recipes are:

| Pair | Route | Status |
| --- | --- | --- |
| D/AD | D: `M_D j = H1m (merge_des_raw j) ;; II_D`. AD: `merge_ades j ≡ H1m (ades_lift_merge j) ;; II_D`. | Both installed; equivalence with the previous AD construction is recorded in the Stage 1 recipe audit. |
| RD/RAD | `j → merge_rdes j → ∥RD[j]`; `merge_rad j = rad_lift_merge (merge_rdes j)` gives the RAD merge. | Exact `p2ac` correspondence, RD/RAD closure and associativity for nondivergent operands are proved. |
| Upstream RD at unit state | `j → unit_state_rd_merge j → M_R(unit_state_rd_merge j)`. | `rdes_lift_parallel_unit_state_eq` compares ordinary `∥RD[j]` with this upstream instance; no further stateful bridge is needed for flat RAD. |

Keep the proof obligations separate:

1. **Construction:** define the observation-level merge from `j`.
2. **Merge healthiness:** prove its required properties, with any premises on `j`.
3. **Parallel closure:** healthy operands + specified merge properties imply a healthy result.
4. **Correspondence:** prove parallel commutes with the representation mappings.

Sharing `j` does not prove the last two obligations. Where useful, state closure
for a general merge `M`, then discharge its premises for the construction from
`j`. Keep any premise on `j` explicit, as a Boolean predicate `C j` or a fixed
point `j is Hj`; a property holds by construction only when it holds for every
`j`. One bundle of merge conditions need not suit every healthiness; if no
generic criterion is available, keep the specialised theorem and record the gap.

## Stage map

| Stage | Status | Purpose / dependency |
| --- | --- | --- |
| 0a | Complete | Validated project baseline; evidence recorded. |
| 0b | Partly complete, deferred | Publication and organisation; not a local proof prerequisite. |
| 0c | Complete | D closure validated and its guide updated. Independent of Stage 1. |
| 1 | Partly complete | AD recipe, merge healthiness and closure presentation. |
| 2 | Pending | D/RD law parity; ordinary RD associativity for nondivergent operands is proved. |
| 3 | Dropped | D → RD embedding; not pursued. |
| 4 | Optional research | Broader RD associativity for divergent operands; the nondivergent law is proved. |
| 5a | Complete | Flat RD/RAD correspondence through `p2ac` and `ac2p`. |
| 5b | Complete | Lifted merge healthiness and RD/RAD closure. |
| 5c | Partial | Commutativity and scoped associativity proved; qualified Chaos and Miracle laws remain to assess. |
| 5d | Optional research | Transfer a broader Stage 4 associativity result if one is pursued. |
| 6 | Pending | AP specialisation can use 5a–b; broader associativity depends on 5d. |

The flat RAD correspondence and closure in 5a–b are available to Stage 6.
The remaining laws in 5c and broader associativity in 5d are separate tasks.

For each mechanisation stage, record fresh PIDE and batch evidence separately,
complete a clean build, and update `docs/parallel`. Keep one D | RD | AD | RAD
law table with exact premises and proof status. Checkboxes below track work,
not conjectured truth. The [documentation conventions](docs/agents/documentation.md)
say where stage summaries, raw evidence and handoffs go.

## Stage 0a — baseline audit · complete

- [x] Preserve and inventory current working-tree changes and submodule revisions.
- [x] Replay the full `UTP-Angelic-CSP` build, including RAD/AP; record PIDE and
  batch evidence separately. Both pass for the current project baseline.
- [x] Archive the obsolete `AD-Parallel-Semantics` audit with a README notice;
  preserve its source. Its separate replay times out. The separate sequential
  audit fails on an obsolete record selector and is also marked unvalidated.

Evidence: [Stage 0a audit and validation](docs/reviews/README.md#stage-0a-baseline-audit).
Historical probe failures remain separate from the passing project baseline.

## Stage 0b — publication and organisation · deferred

These tasks are publication requirements, not prerequisites for local mechanisation.

- [x] Verify fork publication of UTP (`4493ca4`) and UTP-Designs (`b8967c4`),
  including fresh fetches and matching tree IDs.
- [x] Point UTP-Designs at its fork, sync configuration, set `main` tracking,
  and clean redundant local/fork branches while retaining the recovery tag.
- [ ] Commit the RD WIP in the `UTP-Reactive-Designs` fork.
  As of 30 October, the lifting, generic laws, associativity and counterexample
  theories were recorded clean in PIDE and the `UTP-Reactive-Designs` batch build passed.
- [x] Remove the unneeded associativity counterexample theory and its validation
  session (4 November 2026). The general stateful lifted associativity proofs
  were subsequently removed with the unused lift; see the
  [current scope](docs/parallel/RD-stateful.md#conditional-algebra-and-deferred-work).
- [ ] Commit the AD WIP and docs; record the three submodule pointers. The
  Stage 1 AD theories are committed (`5e76186`).
- [x] Commit the generalised merge conditions in the `UTP-Designs` fork
  (`6ffe0f8`, 2 November 2026) and record its pointer. Not pushed yet: a fresh
  clone cannot fetch that pointer until it is.
- [x] Place generic par-by-merge evaluation, choice-distribution, symmetry and
  associativity laws in UTP's `utp_concurrency.thy` (3 November 2026), with
  different prior and output alphabets where applicable. The design merge
  conditions and H1–H3 closure rules remain in `UTP-Designs`.
- [ ] Before publishing, add a proportionate reproducibility check (CI) for proof
  replay, doc links and submodule availability. None is tracked yet.
- [ ] Maintenance, unscheduled: clear build warnings, and switch definitions from
  object equality to `≡` where they are touched. Do not mass-edit proofs.

Evidence: [submodule verification and cleanup](docs/reviews/README.md#stage-0b-dependency-publication).
No new UTP/UTP-Designs fork or push is needed. Tag `design-parallel-presquash`
retains `7e13304`, whose tree matches `b8967c4`. The parent gitlink still needs
recording. Upstream `bad-main` and `pred` remain: GitHub denied write access.

## Stage 0c — D parallel closure and doc fixes · complete

Gaps from the 30 October 2026 review of `utp_des_parallel.thy` and its guides.
None blocks Stage 1 or the flat RD/RAD correspondence.

Work from generic concurrency to design merges, then specialise to the
constructed merge. The closure results below are installed, PIDE-checked, and validated by a
full-project batch build (31 October 2026).

**Generic concurrency — `deps/UTP/utp_concurrency.thy`:**

- [x] Reuse the existing `par_by_merge_seq_add` law,
  `(P ∥[M] Q) ;; K = P ∥[M ;; K] Q`, to derive the completion corollary
  `M ;; K = M ⟹ (P ∥[M] Q) ;; K = P ∥[M] Q`.
  Use this consequence directly in the design proof; no separate completion
  lemma is retained, since it only substitutes the premise into the existing law.

**Design closure — `deps/UTP-Designs/utp_des_parallel.thy`:**

- [x] Instantiate the generic completion rule with `K = II_D` and use
  `H3 X ≡ X ;; II_D` to prove
  `M ;; II_D = M ⟹ (P ∥[M] Q) is H3` for arbitrary design operands and
  design merge `M`. `H3_par_by_merge` now states the equivalent premise
  `M is H3m`, where `H3m M ≡ M ;; II_D` is monotone and idempotent.
- [x] Prove `merge_des j ;; II_D = merge_des j` from its construction,
  `seqr_assoc`, and design-skip idempotence. Derive H3 closure of
  `P ∥D[j] Q` for arbitrary operands and `j`, without a mergeability premise.
  Installed in healthiness form as `merge_des_is_H3m` and
  `des_par_H3_closure`. H3 itself expects a design input, so the merge
  property uses the corresponding transformer on the merge alphabet.
- [x] Weaken the generic design rule `H_par_by_merge` to premises
  `P is H1`, `Q is H1`, and `M is HDm`. H1 follows from
  `H1_par_by_merge`; `H2_par_by_merge` needs no operand premise.
  Derive the corresponding weakening of `des_par_H_closure` to H1 operands.
- [x] Combine H1 and H3 closure to prove normal-design (`N`) closure of
  `P ∥D[j] Q` for H1 operands and arbitrary `j`, using
  `N X ≡ H1 (H3 X)`. This is the D counterpart of upstream
  `par_rdes_NSRD`, with different premises; normality alone does not
  establish associativity. Installed as `des_par_N_closure`.

**Documentation — after theory changes and validation:**

- [x] Fix the stale `des_par_miracle` anchor in
  `docs/parallel/rd-parallel-divergence.md` (L432; fixed 1 November 2026).
  That note is now folded into [related work](docs/parallel/related-work.md),
  which cites lemmas by name rather than by line.
- [x] Update `docs/parallel/D.md` with the generic and constructed closure
  rules, keeping their exact premises and the two levels separate.
- [x] Reword the Chaos-zero paragraph of `docs/parallel/D.md` (1 November 2026):
  `des_par_chaos` assumes and uses `mergeable j`; self-mergeability is now
  described as an unproved weaker premise. Proving that variant is optional
  Stage 2 work.

Evidence: [Stage 0c closure and validation](docs/reviews/README.md#stage-0c-design-parallel-closure).

## Stage 1 — AD recipe and closure · partly complete

Outcome: an equivalent AD construction from `j`, with merge-healthiness and
parallel-closure results presented separately. The generic closure requirement
is complete; necessity and transformer compatibility are optional research.

Names changed on 2 November 2026: `ADH1m`, `ADH2m`, `ADH3m` and `ADHM` are now
D's `H1m`, `H2m`, `H3m` and `HDM`, generalised to merges whose alphabets
differ, and `merge_ades_ADHxm` became `merge_ades_is_Hxm`. `HDM` was renamed
`HDm` on 7 November 2026. Finished items below
keep the names they were done under. The [AD guide](docs/parallel/AD.md#merge-healthiness)
states the naming rule.

- [x] Recheck the recipe in scratch and define
  `merge_ades j ≡ ADH1m (ades_lift_merge j) ;; II_D`.
  Equality with the old `ADHM (lift_merge j)` construction was proved for every
  `j`; the recipe audit preserves that proof, `stage1_alt` in its
  [scratch](docs/reviews/2026-10-30-stage-1-recipe/scratch.thy), after removal of the old interface.
  The outer `A3` wrapper was subsequently removed: `ades_par` now uses
  `merge_ades` directly, with H1 premises for A3 closure.
- [x] Retain `ADH2m M = M ;; J`. Install unconditional `merge_ades_ADH1m`,
  `merge_ades_ADH2m`, `merge_ades_ADHM`, and `merge_ades_completion`.
  ADH2m follows from `II_D ;; J = II_D`; skip additionally releases the final
  choice set after divergence, whereas `J` preserves it.
- [x] Separate the construction's merge-healthiness lemmas from the existing
  A/A2/A3 parallel-closure theorems. ADH1m/ADH2m describe H1/H2-style behaviour
  on the AD merge alphabet, not A1/A2/A3. Record which merge properties hold
  for every `j` and which require a state-merge premise; preserve the exact
  operand premises of each closure and D/AD correspondence theorem.
- [x] Strengthen `ades_par_A2_closure` to only
  `P is A2` and `Q is A2`, without a premise on `j`. The general observation
  lemma retains unstarted operand feasibility; correspondence still requires
  A/A2. [Proof and validation](docs/reviews/README.md#stage-1-ad-recipe-and-closure).
- [x] Add `merge_ades_SymMerge`; let `ades_par_comm` assume `j is SymMerge`,
  with no operand premises.
- [x] Explore associativity: prove `ades_par_assoc` for H1- and A2-healthy
  operands, retaining `j is SymMerge`, `AssocMerge j`, and `mergeable j`.
  `ades_par_normalise_A` uses H1 and A2 to justify transfer through A-normalised operands;
  the D/AD correspondence premises remain unchanged. Associativity outside A2
  and necessity of the merge premises remain open.
  [Proof and validation](docs/reviews/README.md#stage-1-ad-recipe-and-closure).
- [x] Choose the generic AD closure interface for an arbitrary merge `M`, install
  it, and derive the existing lifted closures from it (2 November 2026). D's
  `H1m`, `H2m`, `H3m`, `HDm` and their `H1/H2/H3_par_by_merge` rules now allow
  merges whose alphabets differ, and AD uses them directly. AD adds `A0m`,
  `A1m`, their combined condition `ADm`, and the separate `A2m`, with the rules `A0_par_by_merge`,
  `A1_par_by_merge`, `A_par_by_merge`, `A2_par_by_merge` and `A3_par_by_merge`,
  and `merge_ades_is_A0m`, `merge_ades_is_A1m`, `merge_ades_is_ADm` and `merge_ades_is_A2m`; the lifted closures are now
  corollaries. The theory follows D's section order. Scratch origin:
  [generic closure rules](docs/reviews/2026-10-30-ad-generic-closure-exploration/README.md)
  and [merge transformers](docs/reviews/2026-10-30-ad-merge-healthiness/README.md).
  [Validation](docs/reviews/README.md#stage-1-generic-ad-closure-interface).
- [x] Simplify the generic closure support (3 November 2026): retain
  all five AD closure rules; remove `merge_health`, `merge_slice` and their
  supporting lemmas, and use merge observations directly. Retain the three angelic
  transformers' monotonicity and idempotence results with direct proofs.
  Closure statements, merge definitions and operand premises are unchanged.
  See the [cleanup log](docs/reviews/README.md#stage-1-generic-ad-closure-cleanup).
- [ ] Optional research, outside the closure requirement: necessity of the
  `A0m`/`A1m`/`A2m` closure rules. Only left-to-right is
  proved; these candidate equivalences are **unproved**:

  ```isabelle
  (M is A0m) ⟷ (∀P Q. (P ∥[M] Q) is A0)
  (M is A1m) ⟷ (∀P Q. (P is H1) ∧ (Q is H1) ⟶ ((P ∥[M] Q) is A1))
  (M is A2m) ⟷ (∀P Q. (P is A2) ∧ (Q is A2) ⟶ ((P ∥[M] Q) is A2))
  ```

  Prove the converses or give a checked counterexample. Do not add premises
  (H1m, H1, …) and present the restricted converse as the original claim.
  Decided on 1–2 November 2026: `H1m`, `H2m` and `H3m` stay as the premises of
  their rules; weaker premises were not adopted.
- [x] Settle unconditional pairwise commutation of `H1m`, `H2m`, `H3m`,
  `HDm`, `A0m`, `A1m` and `A2m`: 15 commuting pairs and 6 pairs with proved
  counterexamples. See the [results](docs/parallel/AD.md#commutation-of-merge-healthiness).
- [ ] Optional research: conditional commutation and one-way preservation
  between the merge transformers. Unconditional pairwise results do not settle
  these questions or idempotence of arbitrary noncommuting compositions.
- [x] Install `ades_par_miracle` for H1 operands and arbitrary state merge `j`.
  Both directions reuse the generic design law `par_by_merge_miracle`, with `merge_ades_is_H1m`.
  The lifted D law `des_par_miracle` reuses the same generic results.
- [x] Move and generalise the generic associativity criteria into
  `utp_concurrency.thy`, together with `par_by_merge_eval`, `SymMerge_eval`,
  and `par_by_merge_SUP_*`; add `par_by_merge_assoc`.
  RD and RAD reuse the shared results; AD uses them directly at its merge
  type and no longer duplicates evaluation or symmetry lemmas.
  See the [stage log](docs/reviews/README.md#stage-1-shared-generic-parallel-laws).
- [ ] Record the two completion orders, their empty-set rationale, and their correspondence scope as an ADR.
  AD completes after lifting, keeping the empty-set behaviour H1 and A3 need. RAD
  lifts the completed ordinary RD merge: RA1 excludes `{}` (`RAD_empty`), and
  CSPA1 supplies unstarted behaviour with a trace-feasible choice. Both are chosen
  constructions; empty-set behaviour alone does not force them.
- [x] Remove the old `lift_merge` compatibility definition and its observation
  and equivalence lemmas from the main theory. Rename the raw lift to
  `ades_lift_merge` and its observation lemma to `ades_lift_merge_obs`.
  Retain `ADHM`; prove `merge_ades_unfold` and merge healthiness directly from
  the new recipe. Preserve the old equivalence proof in the recipe audit.
  [Cleanup and validation](docs/reviews/README.md#stage-1-ad-recipe-and-closure).
- [x] Name right-skip completion on the AD merge type as
  `ADH3m M ≡ M ;; II_D`; prove `ADH3m_idem` and unconditional
  `merge_ades_ADH3m`. Keep `merge_ades_completion` as the rewrite equation
  and retain ADHM's ADH1m/ADH2m definition.
  [Validation](docs/reviews/README.md#stage-1-ad-recipe-and-closure).

Evidence: [Stage 1 recipe recheck and validation](docs/reviews/README.md#stage-1-ad-recipe-and-closure).
This completes the requested definition/merge-healthiness slice, not all of Stage 1.

## Stage 2 — D/RD law parity · pending

- [x] Restructure the local lifting for ordinary RD: ORDm healthiness, direct
  RD closure, symmetry and associativity under conditions on j. Preserve the
  earlier stateful results in a separate theory. See the [ordinary RD guide](docs/parallel/RD.md#lifted-merge-and-laws).

Outcome: a D | RD law table with exact premises and proved/refuted/open status.
This stage does not block the flat RD/RAD correspondence.

- [x] Organise the local RD laws and lifting theories around generic merge
  healthiness and closure, then the lifted merge and its laws. Reuse upstream
  definitions and closure rules; retain the isabelle-utp core, imports and session
  structure. Definitions, theorem statements and proofs are unchanged.
  See the [stateful RD guide](docs/parallel/RD-stateful.md) and
  [validation](docs/reviews/README.md#organise-rd-parallel-extensions).
- [x] Complete the generic actual-merge healthiness interface in
  `utp_srdes_parallel_laws`: SRDM packages the upstream sufficient conditions,
  with fixed-point equivalence, idempotence, monotonicity, conjunction/disjunction
  closure and symmetry preservation. Direct parallel has SRD closure under
  SRDM and NSRD closure with RD3; upstream RDM and the merge construction retain
  their meanings. See the [generic interface](docs/parallel/RD-stateful.md#generic-merge-healthiness-and-closure).
- [x] Prove `M is RDM ⟹ M_R(M) is SRDM` and derive lifted SRD/NSRD
  closure through the generic actual-merge rules. No additional premise on `j`
  is required; upstream completion semantics are unchanged. See the
  [completion bridge](docs/parallel/RD-stateful.md#upstream-rd-merge-construction).

Retain the existing `des_par_assoc` and conditional `rdes_parallel_assoc`
with their exact premises. A common completion theorem belongs in Stage 4;
it is not required to use either existing result.

- [ ] D: `des_completion` (iff; implied by `mergeable`) and `des_par_Chaos_iff` with explicit unstarted feasibility.
  `des_completion_iff` and `des_completion_mergeable` are scratch-checked, not installed.
- [ ] Optional: prove the D Chaos zero law under self-mergeability,
  `∀s0 s. ∃y. j(s0,s,s,y)`, instead of `mergeable j`.
- [ ] RD: derive a sufficient Chaos zero law from `rdes_parallel_Chaos_iff`, with
  explicit operand-feasibility and merge-compatibility premises. For SRD operands
  and an RDM seed, the exact criterion requires, at every active initial observation,
  actual branch observations forming a divergent pair and a merge witness at the
  initial trace. Accepting empty increments alone is insufficient; the witness is
  distinct from the actual final output. Preserve the existing
  `Chaos ∥R[M] Miracle = Miracle` law under `M is RDM`.
- [ ] Record each agreed D | RD row with exact premises and its status: proved,
  refuted at that scope, or open. Unresolved associativity research belongs in Stage 4
  and does not block other rows or Stage 5.

- [x] Prove `rdes_lift_parallel_assoc_nondiv` for RD and NDRD operands when
  `j is SymMerge` and `AssocMerge j`. A general stateful lifted law was removed
  with the unused stateful lift; broader ordinary laws belong in Stage 4.
- [ ] A unit-state lifted RD Chaos zero law with premises on `j`, specialising
  the RD Chaos item above via `rdes_parallel_Chaos_iff` and
  `unit_state_rd_merge_eval`, remains open.
- [x] Fix the `merge_rd_eval` anchor (L23) and the AD anchors in
  `docs/parallel/rd-parallel-divergence.md` (fixed 1 November 2026; the note is
  now folded into [related work](docs/parallel/related-work.md)).

## Stage 3 — D → RD embedding · dropped

Dropped on 5 November 2026: the project does not pursue a D–RD
correspondence. Upstream's reactive-design and instantaneous-design material
is unaffected.

## Stage 4 — broader RD associativity · optional research

`ORDm_parallel_assoc` proves associativity for arbitrary operands when the
input merge is RD2-healthy, symmetric and associative. For the constructed
`merge_rdes j`, `rdes_lift_parallel_assoc_nondiv` proves associativity
when `j is SymMerge` and `AssocMerge j` and all three operands are RD and
NDRD. Completion can extend a divergent intermediate trace, so this does not
establish the law for arbitrary RD operands.

The stateful `rdes_parallel_assoc` requires associativity of the completed
merge. `BasicMerge_completed_not_AssocMerge` refutes that sufficient premise
for BasicMerge; it does not refute associativity of parallel on healthy operands.

- [ ] Decide whether a broader ordinary RD law is needed. If so, specify an
  operand class `S`, prove the required closure and completion compatibility,
  and establish a scoped theorem or counterexample. Prefix-closed operands are
  one candidate, not an established result.
- [ ] If a generic theorem for completed `N ;; K` merges is useful, check
  existing Circus results and require compatibility for the actual intermediate
  results. The proved D and nondivergent RD laws do not depend on this theorem.

`SRD_Continuous`, `RD3_Continuous` and `NSRD_Continuous` are available for
stateful research. An NSRD decomposition argument remains to be developed if
that route is pursued.

## Stage 5 — RAD from ordinary RD parallel

Take `M = merge_rdes j` with `j :: ('t × 'e set) merge`. Ordinary
`P ∥RD[j] Q` uses `M` directly; `merge_rad j = rad_lift_merge M` names its
RAD choice-set lift. The ordinary RD and RAD laws below establish their correspondence and
closure. The [unit-state RD comparison](docs/parallel/RD.md#correspondence-with-upstream-rd-parallel)
is a separate check against upstream stateful parallel.

### 5a — flat RD/RAD correspondence · complete

- [x] `rad_par_p2ac` holds for any ordinary merge `M`.
  `merge_rad_p2ac` states the selected instance:
  `p2ac P ∥[merge_rad j] p2ac Q = p2ac (P ∥RD[j] Q)`.
- [x] `rad_par_form` and `rad_par_ac2p` give the reverse representation for
  RAD and A2 operands; `rad_ac2p_RD` maps these operands to ordinary RD.
  The reverse round trip outside A2 remains open.

### 5b — lifted merge and healthy closure · complete

- [x] `merge_rdes_ORDm` holds without a premise on `j`, and
  `rdes_lift_parallel_RD` gives ordinary RD closure.
- [x] `rad_par_A2` gives A2 closure for RAD/A2 operands. The generic
  `rad_par_by_merge_RAD` rule uses `M is RADm`. The seven component merge
  transformers are monotonic, idempotent and pairwise commuting. The ORDm
  lift is RADm-healthy, so `rad_par_RAD` gives RAD closure for all RAD operands.
  See the [component rules](docs/parallel/RAD.md#component-parallel-closure).

### 5c — algebraic laws · partly complete

- [x] `rad_par_comm_merge` gives commutativity when `M is SymMerge`;
  `merge_rdes_SymMerge` supplies this from `j is SymMerge`.
- [x] `rad_par_assoc` gives associativity for RAD/A2 operands and a symmetric,
  associative `M`. For the constructed merge, `rad_par_lift_assoc` gives
  associativity when `j is SymMerge`, `AssocMerge j`, all three operands are
  RAD and A2, and their ordinary RD images have `pre_R = true_r`.
- [ ] Assess whether the selected operator needs qualified Chaos and Miracle
  laws; retain the exact operand, merge and feasibility premises in any result.

### 5d — broader associativity · optional research

- [ ] If Stage 4 establishes a broader ordinary RD law, transfer it through
  `rad_par_form` at the corresponding RAD/A2 operand scope.

Stage 5d is not a prerequisite for AP specialisation.

## Stage 6 — AP and documentation

- [ ] Specialise the existing parameterised `ap_par` to
  `M = merge_rdes j`, retaining its generic definition and explicit
  AP/A2 premises. Use `merge_rdes_ORDm` for the merge premise.
- [ ] Transfer associativity at the scope available from 5c; pursue a broader
  law only if 5d supplies one.
- [ ] Update the guides and retire superseded historical notes.

## Remaining decisions

- Stage 0b: where generic par-by-merge lemmas should live.
- Stage 4: whether associativity beyond NDRD operands is needed.
- Stage 5c: whether qualified Chaos and Miracle laws are needed for the selected merge.

The shared `j` interface and completion orders are selected. The upstream
unit-state comparison is proved for ordinary RD and is not a prerequisite for
the flat RAD construction.

## RD/RAD reference

The [ordinary RD guide](docs/parallel/RD.md) records the constructed merge and
its laws. The [RAD guide](docs/parallel/RAD.md) records the choice-set lifting,
closure and mapping laws. The [stateful RD guide](docs/parallel/RD-stateful.md)
records the separate upstream comparison.

- `rad_par_p2ac` does not complete `M`; `merge_rad_p2ac` instantiates it
  with the completed `merge_rdes j` in 5a.
- The healthy round trip between flat RD and RAD ∩ A2 uses
  `rad_ac2p_p2ac_inverse`, `rad_p2ac_ac2p_RAD_A2`,
  `rad_p2ac_RD_closure`, `A2_p2ac` and `rad_ac2p_RD`.
  `rad_p2ac_RD1` and `rad_p2ac_RD2` carry RD1/RD2 (the paper's
  CSP1/CSP2) to CSPA1/CSPA2.
