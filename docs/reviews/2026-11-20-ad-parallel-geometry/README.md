# Geometry of AD parallel, and angelic choice against a synchronising partner

Date: 2026-11-20. Scope: what the choice-set lift behind `P ∥AD[j] Q` and
`P ∥RAD[j] Q` means for angelic choice, checked in isolated scratch theories.
No production theory, operator or guide was changed. The open decision is
recorded in [PLAN.md](../../../PLAN.md#stage-6--ap-and-documentation).

## Picture

Fix a started prior `s`. An AD offers a family of sets `ac'` (faces of the
simplex of final states): the demon offers a set, and the angel picks a state in
it. Refinement shrinks the family; `⊓` is union of families and `⊔` is pairwise
union of sets. The AD lift
[`ac'_lift_merge`](../../../angelic-designs/utp_ades_parallel_laws.thy#L527),
shared by RAD through
[`rad_lift_merge`](../../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L120),
needs a merge result in `ac'` for every pair of branch states:

```isabelle
∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'. j(s,sL,sR,s')
```

So every angelic choice is resolved after both branches' demonic choices, and
every alternative the angel keeps open must merge with every alternative of the
partner.

## Encoding

[`ad_of`](ad/AD_Geometry_Probe.thy#L8) `R` is `true ⊢ R s ac'`, an AD with true
precondition offering any `ac'` with `R s ac'`;
[`est`](ad/AD_Geometry_Probe.thy#L16) `P s ψ` says `P` cannot diverge from `s`
and every set it offers meets `ψ`. The evaluation lemmas
[`ad_par_ad_of`](ad/AD_Geometry_Probe.thy#L48),
[`ad_seq_ad_of`](ad/AD_Geometry_Probe.thy#L37) and
[`est_par_fun`](ad/AD_Geometry_Probe.thy#L77) are proved from
[`merge_ades_obs`](../../../angelic-designs/utp_ades_parallel_lift.thy#L28) and
`angelic_design_seq`. Frame-disjoint laws use branches lifted from one variable
by [`lftL`](ad/AD_Geometry_Probe.thy#L249) and
[`lftR`](ad/AD_Geometry_Probe.thy#L252) and the merge
[`jfd`](ad/AD_Geometry_Probe.thy#L109) that keeps the left branch's first
component and the right branch's second. "No angelic choice" is
[`a2f`](ad/AD_Geometry_Laws.thy#L34), which gives the repo's `A2`
([`ad_of_A2`](ad/AD_Geometry_Laws.thy#L83)); "no demonic choice" is
[`angf`](ad/AD_Geometry_Laws.thy#L38), one least offered set. The blind product
[`blindfd`](ad/AD_Geometry_Laws.thy#L25) is the blocker of the product of
blockers; the repo has no operator for it.

## Results with a total merge (frame-disjoint)

| Result | Premises | Lemma |
| --- | --- | --- |
| The angel in one branch reacts to the demon in the other | - | [`probe_par_clairvoyant`](ad/AD_Geometry_Probe.thy#L125), [`probe_seq_ang_dem`](ad/AD_Geometry_Probe.thy#L142) |
| `P;;Q ⊑ P∥Q` and `Q;;P ⊑ P∥Q` | Lifted operands | [`par_refines_seq_LR`](ad/AD_Geometry_Probe.thy#L261), [`par_refines_seq_RL`](ad/AD_Geometry_Probe.thy#L304) |
| Blind product `⊑` both sequential orders | Lifted operands | [`blind_fref_seq_LR`](ad/AD_Geometry_Laws.thy#L167), [`blind_fref_seq_RL`](ad/AD_Geometry_Laws.thy#L192) |
| `P∥Q = P;;Q` | `P` has no angelic choice | [`ades_par_eq_seq_a2`](ad/AD_Geometry_Laws.thy#L573) |
| `P∥Q = Q;;P` | `P` has no demonic choice | [`ades_par_eq_seq_ang`](ad/AD_Geometry_Laws.thy#L586) |
| Blind product `= P∥Q` | Neither operand has angelic choice | [`blind_eq_par_a2`](ad/AD_Geometry_Laws.thy#L364) |
| `(P∥Q);;(P'∥Q') ⊑ (P;;P')∥(Q;;Q')`, strict in general | Lifted operands | [`ades_exchange`](ad/AD_Geometry_Laws.thy#L533), [`probe_exchange_seq`](ad/AD_Geometry_Probe.thy#L218) |

[`AD_Seq_Par`](ad/AD_Seq_Par.thy) restates these comparisons and the exchange law for
the real AD operators, with `A`, `NDAD` operands: `P` ignores a lens `a`, `Q` uses only
`a`, and `j` takes `a` from `Q`. It also shows that these two premises say `P` commutes
with every assignment to `a` and `Q` with every assignment that keeps `a`. They stay
here because they hold for one merge only; the
[AD guide](../../parallel/AD.md#parallel-and-sequential-composition) states the result.

## Results for any merge

| Result | Premises | Lemma |
| --- | --- | --- |
| `(P∥Q) ⊔ (P'∥Q) ⊑ (P⊔P')∥Q`, strict in general | - | [`ades_par_angelic_subdist`](ad/AD_Geometry_Probe.thy#L407), [`probe_par_angelic_right`](ad/AD_Geometry_Probe.thy#L171) |
| …an equality | `Q` has no demonic choice; `P`, `P'` up-closed | [`ades_par_angelic_dist_eq`](ad/AD_Geometry_Laws.thy#L456) |
| The keep-either merge gives `P ⊓ Q` | Up-closed, feasible, no `∅` | [`par_either_demonic`](ad/AD_Geometry_Probe.thy#L355) |
| Blocker duality `b(b(U)) = U`; bottleneck minimax on a finite state space | Up-closed; `U ≠ {}`, `{} ∉ U` | [`blk_blk`](ad/AD_Geometry_Laws.thy#L134), [`bottleneck_minmax`](ad/AD_Geometry_Laws.thy#L623) |

## Partial merges: unmatched angelic alternatives block

With an equality merge [`jeq`](ad/AD_Geometry_Laws.thy#L671), an angelic
alternative the partner cannot match makes the composition infeasible at a
started prior:

```isabelle
v1 ≠ v2 ⟹ ¬ (x := v1 ∥AD[jeq] (x := v1 ⊔ x := v2)) (ades_obs True s0 ok' ac')
```

([`ades_par_eq_angelic_miracle`](ad/AD_Geometry_Laws.thy#L678);
`x := v1 ∥AD[jeq] x := v1` ends in `v1` by
[`ades_par_eq_same`](ad/AD_Geometry_Laws.thy#L701)).

RAD keeps the observations taken before an event, so the same effect blocks
progress instead. The probe uses the repo's `PrefixSkip_RAD`, `⊓`, `⊔` and
`merge_rad`, the merge [`jsync`](rad/RAD_Probe.thy#L40) that synchronises on
every event (traces agree, refusals unite), `a ≠ b`, and a started,
non-waiting prior:

| Composite | Result | Lemma |
| --- | --- | --- |
| `(a→Skip) ∥ (a→Skip)` | Can terminate after `a` | [`rad_sync_progress`](rad/RAD_Probe.thy#L105) |
| `(a→Skip) ∥ ((a→Skip) ⊓ (b→Skip))` | Can terminate after `a` | [`rad_sync_demonic_progress`](rad/RAD_Probe.thy#L115) |
| `(a→Skip) ∥ ((a→Skip) ⊔ (b→Skip))` | Every offered set holds an observation before either event | [`rad_sync_angelic_stuck`](rad/RAD_Probe.thy#L126), [`rad_sync_angelic_no_progress`](rad/RAD_Probe.thy#L151) |
| `((a→Skip) ⊓ (b→Skip)) ∥ ((a→Skip) ⊔ (b→Skip))` | Same | [`rad_sync_demonic_angelic_stuck`](rad/RAD_Probe.thy#L166) |

CSP external choice gives `(a→Skip) ∥ ((a→Skip) □ (b→Skip)) = a→Skip`, so the
current lift does not let angelic choice cooperate with a synchronising partner.
The clairvoyance above needs a merge that combines every pair of offered states.

## The shared lift is canonical

[`AD_Lift_Canonical`](ad/AD_Lift_Canonical.thy) compares an arbitrary merge `M`
on choice sets with `ABm (ac'_lift_merge N)` for an inner merge `N` on single
states. `merge_rad j` is exactly this lift with `N = merge_rdes j`; `merge_ades j`
wraps it in `H1m` and `H3m`
([`merge_ades_design_lift`](../../../angelic-designs/utp_ades_parallel_lift.thy#L39)).
Call `M` admissible when it relates only nonempty branch sets
([`nonempty_m`](ad/AD_Lift_Canonical.thy#L19)), never gains from larger nonempty
branch sets ([`antitone_m`](ad/AD_Lift_Canonical.thy#L13)), and merges single
states no more than `N` ([`sound_m`](ad/AD_Lift_Canonical.thy#L24)):

```isabelle
M({sL},{sR},Z) ⟹ ∃s' ∈ Z. N(s,sL,sR,s')
```

| Result | Premises | Lemma |
| --- | --- | --- |
| The lift is admissible and equals `N` on single states | - | [`lift_antitone`](ad/AD_Lift_Canonical.thy#L47), [`lift_sound`](ad/AD_Lift_Canonical.thy#L53), [`lift_singleton`](ad/AD_Lift_Canonical.thy#L57) |
| Every admissible `M` lies inside the lift, so `P ∥[ABm (ac'_lift_merge N)] Q ⊑ P ∥[M] Q` | `M` admissible | [`lift_greatest_obs`](ad/AD_Lift_Canonical.thy#L64), [`par_lift_canonical`](ad/AD_Lift_Canonical.thy#L109) |
| Antitonicity is free: `P ∥[ABm M] Q = P ∥[M] Q` | `P`, `Q` `PBMH_ades`; `M` nonempty | [`par_ABm_eq`](ad/AD_Lift_Canonical.thy#L136), [`par_lift_canonical_PBMH`](ad/AD_Lift_Canonical.thy#L181) |
| `P ∥AD[j] Q ⊑ P ∥[H3m (H1m M)] Q` | `M` admissible for `merge_des j` | [`ades_par_canonical`](ad/AD_Lift_Canonical.thy#L190) |
| The RAD blocking holds for every admissible `M` | `M` admissible for `merge_rdes jsync` | [`rad_sync_angelic_stuck_any_lift`](rad/RAD_Probe.thy#L210) |

So the shared lift is the least refined merge that agrees with the inner merge on
single states. No admissible lift lets `(a→Skip) ∥ ((a→Skip) ⊔ (b→Skip))`
progress. Nor can one give the blind product where it differs from `∥AD[j]`,
because that product is less refined. This follows from
[`blind_fref_seq_RL`](ad/AD_Geometry_Laws.thy#L192) and
[`probe_seq_ang_dem`](ad/AD_Geometry_Probe.thy#L142) and is argued here, not
stated as one lemma. Merging only the compatible pairs is not admissible: by
up-closure `x := 2` also offers `{1,2}`, so `x := 2 ∥[jeq] x := 1` would offer
`{1}`.

The production [shared choice-set canonicity results](../../parallel/AD.md#shared-choice-set-canonicity)
use `ABm` directly, with [RAD](../../parallel/RAD.md#canonicity) and
[AP](../../parallel/AP.md#canonicity-through-rad) consequences. The original
`AD_Lift_Canonical` theory above remains as support for the open RAD geometry probes.

## Not checked

- The synchronisation examples at AP level, waiting or diverging priors, and
  other synchronisation sets. The general transported AP refinement is covered
  by the production canonicity result linked above.
- Alternatives outside the canonicity result: parallel on operands without
  up-closure, or a different process-level angelic choice.
- Laws for operands with a precondition other than `true`.
- That the bottleneck value is the Choquet (Lovász) integral for the 0/1
  capacity `b(U)`: classical, and checked only by [`brute_force.py`](brute_force.py).

## Rebuilding

The [ROOT](ROOT) defines `AD_Geometry_Probe` on `UTP-Angelic-Designs` and
`RAD_Geometry_Probe` on `UTP-Reactive-Angelic-Designs`. From the repository
root, with the patched Isabelle2026 profile (about 20 s once the parent heaps
exist):

```sh
PROJECT_DIR="$PWD" ISABELLE_IDENTIFIER=utp-2026-patched timeout 600s \
  "$HOME/Applications/Isabelle2026-patched.app/bin/isabelle" build -o timeout=60 \
  -d deps -d . -d docs/reviews/2026-11-20-ad-parallel-geometry \
  AD_Geometry_Probe RAD_Geometry_Probe
```
