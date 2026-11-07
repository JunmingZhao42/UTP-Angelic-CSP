# Parallel-by-merge plan

Goal: parallel operators built from a shared state-merge policy `j`, with D/AD
and RD/RAD round-trip correspondence on their stated healthy domains.
For general angelic operands these require A/A2 for AD and RAD/A2 for RAD;
correspondence outside A2 remains open.

**Current stage: Stage 1.** The AD recipe, its merge healthiness and the
generic AD closure interface are installed. The remaining Stage 1 tasks are
listed below; Stage 0b work remains deferred.

## Route and proof obligations

Use the same `j` within each ordinary/angelic pair; the two pairs have different
state alphabets. The selected recipes are:

| Pair | Route | Status |
| --- | --- | --- |
| D/AD | D: `M_D j = H1m (merge_des_raw j) ;; II_D`. AD: `merge_ades j ≡ H1m (ades_lift_merge j) ;; II_D`. | Both installed; equivalence with the previous AD construction is recorded in the Stage 1 recipe audit. |
| RD/RAD | `j → rdes_lift_merge j → M_R(rdes_lift_merge j) →` transport completed merge to flat alphabet `→` RAD lifting. | RD construction installed; transport and specialised RAD correspondence/closure pending. |

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
| 1 | **Current** | AD recipe, merge healthiness and closure presentation. |
| 2 | Pending | D/RD law parity; independent of the RAD bridge. |
| 3 | Optional | D → RD embedding; not needed for RAD. |
| 4 | Research | Restricted associativity; only 5d depends on a positive result. |
| 5a | Pending | Unit-state alphabet and healthiness bridge. |
| 5b | After 5a | Transport the completed RD merge and prove specialised correspondence. |
| 5c | After 5b | Healthy closure and transfer of available laws. |
| 5d | Conditional | Associativity transfer; needs 5c and a matching Stage 4 result. |
| 6 | After 5c | AP specialisation and documentation; associativity waits for 5d. |

RAD order: **0a → 5a → 5b → 5c → 6**. Stages 1–4 are separate work;
Stage 1 does not start the RAD bridge. Stage 5c can transfer existing laws
without waiting for Stage 2; additional laws can follow later.

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
- [ ] Commit the RD WIP in the `UTP-Reactive-Designs` fork; move the tests to a separate session.
  As of 30 October, the WIP theories (`utp_rdes_parallel_lift`, `_laws`, `_assoc`,
  `_assoc_tests`) were recorded clean in PIDE and the `UTP-Reactive-Designs` batch build passed.
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
None blocks Stage 1 or the RAD bridge.

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

## Stage 1 — AD recipe and closure · current

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
  `A1m`, their combined `ADm`, and `A2m`, with the rules `A0_par_by_merge`,
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
  lifts the transported completed RD merge: RA1 excludes `{}` (`RAD_empty`), and
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

Outcome: a D | RD law table with exact premises and proved/refuted/open status.
This stage does not block the RAD alphabet bridge.

Retain the existing `des_par_assoc_state` and conditional `rdes_parallel_assoc`
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
- [ ] Rename/split `rdes_parallel_initial_eval`; add `BasicMerge_not_completion`
  (scratch-checked, not installed) to the tests.
- [ ] Record each agreed D | RD row with exact premises and its status: proved,
  refuted at that scope, or open. Unresolved associativity research belongs in Stage 4
  and does not block other rows or Stage 5.

- [ ] Lifted RD associativity in terms of `j`, the counterpart of
  `des_par_assoc_state`. Prove that `j is SymMerge` and `AssocMerge j` transfer
  to `rdes_lift_merge j`. Determine whether a mergeability-style condition on
  `j` implies `RDM_completion (rdes_lift_merge j)`; D's `mergeable j` plays the
  same role for its inner `II_D`. Open question, not a claim.
- [ ] Lifted RD Chaos zero law with premises on `j`, specialising the RD Chaos
  item above via `rdes_parallel_Chaos_iff` and `rdes_lift_merge_eval`.
  `utp_rdes_parallel_lift.thy` currently proves neither law.
- [x] Fix the `merge_rd_eval` anchor (L23) and the AD anchors in
  `docs/parallel/rd-parallel-divergence.md` (fixed 1 November 2026; the note is
  now folded into [related work](docs/parallel/related-work.md)).

Treat `BasicMerge_not_completion` as a failure of the sufficient completion premise,
not as nonassociativity: `RDM_completion_not_necessary` already separates these claims.

## Stage 3 — D → RD embedding · optional

Target: `⌈D⌉ ∥R[rd_lift_state j] ⌈E⌉ = ⌈D ∥D[j] E⌉`.

- [ ] Install the scratch-checked `rd_lift_state j` and `rd_lift_state_RDM`;
  define an embedding `⌈·⌉` of designs as instantaneous reactive designs.
- [ ] Extend the scratch-checked `merge_rd_lift_state_eval` to waiting branch inputs.

The scratch results here and in Stage 2 are not installed, and their proof
artefacts may need recreating. Recheck them before installation.

## Stage 4 — RD associativity · research

Outcome: a scoped theorem, counterexample, or documented obstruction within an
agreed timebox. Only Stage 5d needs a positive result from this stage.

- [ ] Check whether utp-main proved Circus parallel associativity; reuse it if so.
- [ ] Search for a `BasicMerge` counterexample on SRD via `rdes_parallel_assoc_SRD_iff`.
- [ ] Investigate a generic associativity theorem for `N ;; K` merges, with explicit
  raw associativity, symmetry and completion-compatibility premises over an operand
  set `S`. Require closure of `S` under raw parallel, or compatibility for the exact
  intermediate results. Original operand membership or completed-output normality
  alone is insufficient.
- [ ] Test this route on a defined, suitably closed `S` (conjecture: prefix-closed operands).
  An SRD counterexample leaves restricted classes open; name the class each result covers.
- [ ] Only after the generic theorem is useful, consider recovering existing D/RD
  proofs through it. The D route still needs the unproved intermediate result
  `AssocMerge (H1m (merge_des_raw j))` under the intended premises; D associativity
  itself is already proved and need not wait for this refactoring.
- [ ] End the timebox with a scoped theorem, counterexample, or explicit unresolved obstruction.

`SRD_Continuous`, `RD3_Continuous` and `NSRD_Continuous` already exist and are imported.
An NSRD generator/decomposition argument remains to be developed if needed.

## Stage 5 — RAD from the completed RD merge

Outcome: specialise the existing generic RAD parallel to the completed RD merge
constructed from `j`, with correspondence and healthy closure proved separately.
See the [RD/RAD reference](#rdrad-reference) for existing results and limits.

### 5a — alphabet and healthiness bridge

- [ ] Define the unit-state alphabet map and its inverse, preserving `ok`, `wait`,
  `tr` and `ref`; remove only `st = ()`.
- [ ] Prove preservation of sequential composition and generic parallel-by-merge,
  including all merge observations.
- [ ] Prove transport of reactive skip (`II_R` to `II_C`).
- [ ] Prove equivalence of SRD healthiness at unit state with flat RD healthiness.

Stop at this bridge before introducing new parallel definitions. Stage 3's
instantaneous-design embedding is a separate task.

### 5b — completed merge and correspondence

- [ ] Transport `M_R(rdes_lift_merge j)` through 5a, with
  `j :: ('t × unit × 'e set) merge`. Keep trace/refusal policy in `j`; its type
  excludes `ok` and `wait`.
- [ ] Instantiate `rad_par` and `rad_par_p2ac` with the transported completed merge;
  prove correspondence with the specialised stateful RD operator.
- [ ] Use `rad_par_form` for the converse representation on RAD/A2 operands.

A flat `N_C`, `M_C` formula is optional: introduce it only after proving equality
with the transport. A second completion construction is not a prerequisite.

### 5c — healthy closure and available laws

- [ ] First try `ORDm` healthiness of the transported merge and reuse `rad_par_RAD`.
  If unavailable, investigate direct RD closure through 5a and
  `rdes_lift_parallel_NSRD`, then `rad_par_form` and `rad_p2ac_RD_closure`.
- [ ] Establish A2 closure with `rad_par_A2`; preserve RAD/A2 operand premises
  and CSPA1 behaviour.
- [ ] After closure, transfer qualified Chaos and Miracle laws and commutativity,
  including constants and every feasibility, operand and merge premise.

Failure of the sufficient `ORDm` condition alone does not refute the construction.
Neither closure route is established yet. Neither gives a round trip outside A2.

### 5d — conditional associativity transfer

- [ ] Transfer associativity only at the operand/merge scope proved in Stage 4
  and transported through 5a. For a restricted `S`, identify the corresponding
  RAD operands and establish the needed closure.

Requires 5c and a matching positive Stage 4 result. An open associativity question
does not block other RAD/AP laws or Stage 6.

## Stage 6 — AP and documentation

- [ ] Specialise the existing parameterised `ap_par` to the transported completed
  merge after 5a–c, retaining the generic definition and explicit AP/A2 premises.
  Reuse theorems when `ORDm` is established, or transfer closure using 5c.
- [ ] Transfer associativity only when 5d is available; otherwise mark it open.
- [ ] Update the guides and retire superseded historical notes.
- [ ] Optional: establish the D/RD/AD/RAD square at unit state.

## Remaining decisions

- Stage 0b: where generic par-by-merge lemmas should live.
- Stage 4: operand class, closure requirements and research timebox.
- Stage 5b: whether a flat `N_C`, `M_C` formula is useful after transport.

The shared `j` interface and completion orders are selected. Fork publication of
UTP and UTP-Designs is verified. A stateful RAD remains a separate extension;
the selected route uses the unit-state bridge to current flat RAD.

## RD/RAD reference

Installed results that Stage 5 builds on. The RAD parallel laws are in the
[RAD guide](docs/parallel/RAD.md), and the main RAD/RD mappings are in the
[RAD paper guide](docs/paper/RAD.md).

The specialised stateful RD operator is generic parallel with a completed merge:

```isabelle
P ∥R[rdes_lift_merge j] Q = P ∥[M_R(rdes_lift_merge j)] Q
```

Here `j :: ('t × 's × 'a) merge` relates trace contributions, program state and
remaining observations, without `ok` or `wait`. `N_R` and `M_R` act on the same
RD alphabet; they are not alphabet liftings.

| Merge expression | Guaranteed property | Premise |
| --- | --- | --- |
| `rdes_lift_merge j` | RDM (`rdes_lift_merge_RDM`) | None on `j` |
| `N_R(M)` | R1m, R3hm, RD1m | None on `M` |
| `N_R(M)` | R2m | `M is R2m`, implied by `M is RDM` |
| `M_R(M)` | RD3, hence RD2 | None on `M` |

- `SRD_par_by_merge`: SRD operands and a merge that is R1m, R2m, R3hm, RD1m and
  RD2 give an SRD result, for the merge used directly.
- `par_rdes_NSRD`: SRD operands and `M is RDM` give `(P ∥R[M] Q) is NSRD`.
  `rdes_lift_parallel_NSRD` instantiates it with `rdes_lift_merge j`, with no
  condition on `j`. Associativity and Chaos zero keep their own premises.
- RDM constrains the seed, not the completed merge, and `N_R` builds control
  behaviour, so the obligation is not `M is N_R`. RDM of the seed does not by
  itself give `ORDm` of the transported completion.
- `rad_par_p2ac`, `(p2ac P) ∥RAD[M] (p2ac Q) = p2ac (P ∥[M] Q)`, has no premises.
  It neither completes `M` nor identifies it with `rdes_lift_merge j`.
- The healthy round trip between flat RD and RAD ∩ A2 uses `rad_ac2p_p2ac_inverse`,
  `rad_p2ac_ac2p_RAD_A2`, `rad_p2ac_RD_closure`, `A2_p2ac` and `rad_ac2p_RD`;
  `rad_p2ac_RD1` and `rad_p2ac_RD2` carry RD1/RD2 (the paper's CSP1/CSP2) to
  CSPA1/CSPA2. Keep these encoding identities separate from healthy closure.
