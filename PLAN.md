# Parallel-by-merge plan

Goal: parallel operators built from a shared state-merge policy `j`, with D/AD
and RD/RAD round-trip correspondence on their stated healthy domains.
For general angelic operands these require A/A2 for AD and RAD/A2 for RAD;
correspondence outside A2 remains open.

This file lists open work only. Finished work is in the commit history and the
guides; [docs/reviews](docs/reviews/README.md) lists the milestones.

**Current focus: AD and RAD laws off A2** (operands with angelic choice). AP is
deferred. The D/AD and ordinary RD/RAD constructions, closure, correspondence
and scoped associativity are installed; see the [parallel guides](docs/parallel/README.md).

## Route and proof obligations

Use the same `j` within each ordinary/angelic pair; the two pairs have different
state alphabets. The selected recipes are:

| Pair | Route | Status |
| --- | --- | --- |
| D/AD | D: `M_D j = H1m (merge_des_raw j) ;; II_D`. AD: `merge_ades j ≡ H1m (ades_lift_merge j) ;; II_D`. | Both installed. |
| RD/RAD | `j → merge_rdes j → ∥RD[j]`; `P ∥RAD[j] Q = P ∥[merge_rad j] Q`. | Exact `p2ac`/`ac2p` correspondence and round trips on RAD+A2, RD/RAD closure and associativity for nondivergent operands are proved. |
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
| 0a | Complete | Validated project baseline. |
| 0b | Partly complete, deferred | Publication and organisation; not a local proof prerequisite. |
| 0c | Complete | D closure and its guide. |
| 1 | Partly complete | AD recipe, merge healthiness and closure are installed; optional research remains. |
| 2 | Pending | D/RD law parity; ordinary RD associativity for nondivergent operands is proved. |
| 3 | Dropped | D → RD embedding; not pursued (5 November 2026). |
| 4 | Optional research | Broader RD associativity for divergent operands. |
| 5a–b | Complete | Flat RD/RAD correspondence, lifted merge healthiness and closure. |
| 5c | Partial | Commutativity and scoped associativity proved; qualified Chaos and Miracle laws remain to assess. |
| 5d | Optional research | Transfer a broader Stage 4 associativity result if one is pursued. |
| 6 | Pending | AP specialisation can use 5a–b; broader associativity depends on 5d. |
| Off A2 | Active | AD and RAD laws for operands with angelic choice. |

For each mechanisation stage, complete a clean build and update `docs/parallel`.
Checkboxes track work, not conjectured truth. The
[documentation conventions](docs/agents/documentation.md) say where evidence goes.

## Off-A2 AD and RAD laws

The installed AD laws `ades_par_assoc` and `ades_par_assoc_nd` need A2 operands.
[`ades_par_assoc_det`](angelic-designs/utp_ades_parallel_algebra.thy#L315) needs no
operand premise when `j` is `Functional`, `mergeable`, symmetric and associative;
[`ades_par_assoc_det_nd`](angelic-designs/utp_ades_parallel_algebra.thy#L326) drops
`mergeable` for nondivergent operands. A nondeterministic `j` breaks associativity
(see the [AD guide](docs/parallel/AD.md)).

- [ ] AD normal form at a fixed prior: `U = ⋃ ↑A`, `P = ⊓ ⊔ ⟨a⟩`. True
  precondition first, then A0/H1/H3.
- [ ] Characterise `∥AD` off A2 for a general `j`; the deterministic case at a
  started prior is installed.
- [ ] Unit and zero laws (Chaos, Miracle, unit), compared with D.
- [ ] RAD normal form and characterisation through ordinary RD parallel.
- [ ] RAD associativity with divergent operands. The nondivergent case off A2 is
  installed (`rad_par_assoc_det_nd`, deterministic `j`); with divergence RAD releases
  only trace extensions, and RD itself has no associativity law there (item 12).

## Stage 0b — publication and organisation · deferred

- [ ] Before publishing, add a proportionate reproducibility check (CI) for proof
  replay, doc links and submodule availability.
- [ ] Maintenance, unscheduled: clear build warnings, and switch definitions from
  object equality to `≡` where they are touched. Do not mass-edit proofs.

## Stage 1 — AD recipe and closure · optional research

- [ ] Necessity of the `A0m`/`A1m`/`A2m` closure rules. Only left-to-right is
  proved; these candidate equivalences are **unproved**:

  ```isabelle
  (M is A0m) ⟷ (∀P Q. (P ∥[M] Q) is A0)
  (M is A1m) ⟷ (∀P Q. (P is H1) ∧ (Q is H1) ⟶ ((P ∥[M] Q) is A1))
  (M is A2m) ⟷ (∀P Q. (P is A2) ∧ (Q is A2) ⟶ ((P ∥[M] Q) is A2))
  ```

  Prove the converses or give a checked counterexample. Do not add premises
  (H1m, H1, …) and present the restricted converse as the original claim.
  `H1m`, `H2m` and `H3m` stay as the premises of their rules.
- [ ] Conditional commutation and one-way preservation between the merge
  transformers. The unconditional pairwise results
  ([AD guide](docs/parallel/AD.md#generic-merge-healthiness-and-closure)) do not
  settle these questions or idempotence of arbitrary noncommuting compositions.
- [ ] Record the two completion orders, their empty-set rationale, and their
  correspondence scope as an ADR. AD completes after lifting, keeping the
  empty-set behaviour H1 and A3 need. RAD lifts the completed ordinary RD merge:
  RA1 excludes `{}` (`RAD_empty`), and CSPA1 supplies unstarted behaviour with a
  trace-feasible choice. Both are chosen constructions; empty-set behaviour alone
  does not force them.

## Stage 2 — D/RD law parity · pending

Outcome: a D | RD law table with exact premises and proved/refuted/open status.
Retain the existing `des_par_assoc` and conditional `rdes_parallel_assoc` with
their exact premises.

- [ ] D: `des_completion` (iff; implied by `mergeable`) and `des_par_Chaos_iff`
  with explicit unstarted feasibility. `des_completion_iff` and
  `des_completion_mergeable` are scratch-checked, not installed.
- [ ] Optional: prove the D Chaos zero law under self-mergeability,
  `∀s0 s. ∃y. j(s0,s,s,y)`, instead of `mergeable j`.
- [ ] RD: derive a sufficient Chaos zero law from `rdes_parallel_Chaos_iff`, with
  explicit operand-feasibility and merge-compatibility premises. For SRD operands
  and an RDM seed, the exact criterion requires, at every active initial observation,
  actual branch observations forming a divergent pair and a merge witness at the
  initial trace. Accepting empty increments alone is insufficient; the witness is
  distinct from the actual final output. Preserve the existing
  `Chaos ∥R[M] Miracle = Miracle` law under `M is RDM`.
- [ ] A unit-state lifted RD Chaos zero law with premises on `j`, specialising
  the RD item above via `rdes_parallel_Chaos_iff` and `unit_state_rd_merge_eval`.
- [ ] Record each agreed D | RD row with exact premises and its status: proved,
  refuted at that scope, or open.

## Stage 4 — broader RD associativity · optional research

D, RD and RAD have generic associativity laws with operand healthiness and merge
premises: `par_by_merge_assoc_NDD`, `par_by_merge_assoc_NDRD` and
`par_by_rad_lift_merge_assoc_NDRAD`, all through `par_by_merge_assoc_guard`.
For `merge_rdes j`, `rdes_lift_parallel_assoc_nd` proves associativity when
`j is SymMerge` and `AssocMerge j` and all three operands are RD and NDRD.
Completion can extend a divergent intermediate trace, so this does not establish
the law for arbitrary RD operands. The stateful `rdes_parallel_assoc` requires
associativity of the completed merge; `BasicMerge_completed_not_AssocMerge`
refutes that premise for BasicMerge, not associativity of parallel on healthy
operands.

- [ ] Decide whether a broader ordinary RD law is needed. If so, specify an
  operand class `S`, prove the required closure and completion compatibility,
  and establish a scoped theorem or counterexample. Prefix-closed operands are
  one candidate, not an established result.
- [ ] If a generic theorem for completed `N ;; K` merges is useful, check
  existing Circus results and require compatibility for the actual intermediate
  results.

`SRD_Continuous`, `RD3_Continuous` and `NSRD_Continuous` are available for
stateful research.

## Stage 5 — RAD from ordinary RD parallel

Take `M = merge_rdes j`. Ordinary `P ∥RD[j] Q` uses `M` directly;
`P ∥RAD[j] Q = P ∥[rad_lift_merge M] Q` uses its RAD choice-set lift. The
round trip between flat RD and RAD ∩ A2 uses `rad_ac2p_p2ac_inverse`,
`rad_p2ac_ac2p_RAD_A2`, `rad_p2ac_RD_closure`, `A2_p2ac` and `rad_ac2p_RD`;
`rad_p2ac_RD1` and `rad_p2ac_RD2` carry RD1/RD2 (the paper's CSP1/CSP2) to
CSPA1/CSPA2. See the [RD guide](docs/parallel/RD.md) and the
[RAD guide](docs/parallel/RAD.md).

- [ ] 5c: assess whether the selected operator needs qualified Chaos and Miracle
  laws; retain the exact operand, merge and feasibility premises in any result.
- [ ] 5d: if Stage 4 establishes a broader ordinary RD law, transfer it through
  `rad_par_form` at the corresponding RAD/A2 operand scope. Not a prerequisite
  for AP.

## Stage 6 — AP and documentation

- [ ] Transfer associativity to AP at the scope available from 5c; pursue a
  broader law only if 5d supplies one.
- [ ] Decide how angelic choice should behave against a synchronising partner.
  The shared choice-set lift needs a merge for every pair of kept-open
  alternatives, so with a synchronising RAD merge
  `(a→Skip) ∥ ((a→Skip) ⊔ (b→Skip))` never progresses past the choice, and an
  AD equality merge makes the analogous composition infeasible. The lift is
  canonical under the [shared admissibility conditions](docs/parallel/AD.md#shared-choice-set-canonicity),
  so no such lift avoids the blocking or gives the blind
  product. Options: keep the lift and document that angelic choice does not
  cooperate with synchronisation (use external choice for that); change angelic
  choice at the process level; or drop up-closure for parallel operands. Check AP
  and waiting priors before deciding. See the
  [geometry review](docs/reviews/2026-11-20-ad-parallel-geometry/README.md).
- [ ] Update the guides: label the A2 laws as the ordinary fragment, add an
  off-A2 table for RAD, and retire superseded historical notes.

## Remaining decisions

- Stage 0b: where generic par-by-merge lemmas should live.
- Stage 4: whether associativity beyond NDRD operands is needed.
- Stage 5c: whether qualified Chaos and Miracle laws are needed for the selected merge.
- Stage 6: whether angelic choice should cooperate with a synchronising partner; the choice-set lift itself is canonical.
- Off A2: which geometry-review results to install.
