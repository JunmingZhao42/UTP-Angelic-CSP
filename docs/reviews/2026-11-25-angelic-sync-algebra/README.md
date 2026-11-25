# Angelic choice against a synchronising partner: which algebra

Date: 2026-11-25. Scope: compare definitions of parallel, the choice-set lift and
angelic choice by the laws they keep, for the open
[Stage 6 item](../../../PLAN.md#stage-6--ap-and-documentation). No production
theory, operator or guide was changed. The examples, `jsync` and the current
results come from the [geometry review](../2026-11-20-ad-parallel-geometry/README.md).

## Answer

- No candidate has every law. Three results rule out the full list (proved here):
  - no parallel that agrees with assignments distributes over both `⊔` and `⊓`;
  - while `⊔` is a join, no monotone parallel gives `a→Skip ∥ (a→Skip ⊔ b→Skip) = a→Skip`;
  - in RAD, no monotone parallel that agrees with RAD parallel on CSP processes
    distributes over `⊔`. A process that may diverge can be joined into one that
    does not, while its parallel still diverges (C8).
- The best law set comes from **F**, the join of `g ∥ h` over the CSP (A2)
  processes `g ⊑ P` and `h ⊑ Q`. This is candidate (b) built from the join normal form.
  F keeps `⊔` as the join and keeps up-closure. It is RAD-healthy and commutative,
  and it has the Miracle and Chaos zeros (proved). It gains:
  - the best cooperation that monotonicity allows, `a→Skip ⊔ Stop`;
  - distribution over `⊔` for nondivergent operands (brute force);
  - associativity for relational merges such as interleaving, where the current
    lift fails (brute force, also with divergence).

  F loses distribution over `⊓` off A2, which the first result forces, and it is
  not par-by-merge.
- **Recommendation:** if Stage 6 wants `⊔` to cooperate with synchronisation, define
  AD/RAD/AP parallel off A2 by F. Otherwise keep the current lift. In both cases use
  `□` for choices the partner resolves: `a→Skip ∥ (a→Skip □ b→Skip) = a→Skip`.
  Do not pursue minimal sets (a), giving up (c) or `H` (f): (a) and (c) break
  monotonicity, and `H` loses both distributivities. Roscoe's choice (d) cooperates,
  but it is not a join, and the paper notes that it ignores divergence.
- **Decision (2026-11-25):** production keeps the lift and documents the
  behaviour in the [RAD guide](../../parallel/RAD.md#angelic-choice-against-a-synchronising-partner).
  Associativity of F stays open as a deferred research item.

## Setting

Fix a started, non-waiting prior. A process offers an up-closed family `U` of
nonempty sets `ac'`: the demon offers a set, and the angel picks a state in it.
`P ⊑ Q` iff `U_Q ⊆ U_P`, `⊓` is union of families and `⊔` is intersection. A merge
`j` maps a pair of branch states to a set of merged states, possibly empty. `b(U)`
is the blocker: the sets that meet every member of `U`.

| Candidate | Offers `ac'` iff |
| --- | --- |
| (e) lift (current) | some `X ∈ U_P`, `Y ∈ U_Q` with `ac' ∩ j(x,y) ≠ {}` for all `x ∈ X`, `y ∈ Y` |
| (b) F, join normal form | `ac' ∩ j[G × H] ≠ {}` for all `G ∈ b(U_P)`, `H ∈ b(U_Q)` |
| (f) H, deterministic atoms (new) | the meet, over deterministic refinements `d_G` of each blocker `G`, of the joins of `d_G ∥ e_H` |
| (a) minimal sets | as (e) on minimal `X`, `Y`, over the pairs that merge (at least one) |
| (c) give up | as (a); an unmatched pair with an angelic alternative adds a deadlock outcome, an unmatched demonic pair blocks |
| (d) Roscoe's `⊞` | CSP parallel; `⊔` replaced by `⊞`, read demon first: the `⊓` over deterministic refinements `p`, `q` of the deterministic process with the traces of both |

The lift is the meet normal form `P = ⊓_{A∈U} ⊔_{a∈A} ⟨a⟩` distributed over
single observations. The same distribution over coarser A2 blocks depends on how
`P` is split: one block gives F and single observations give the lift, so it is
not well defined. The join normal form `P = ⊔_{G∈b(U)} ⊓_{g∈G} ⟨g⟩` is canonical,
because A2 processes are join-prime at each prior. Distributing over it gives F.
For a functional `j`, F is the blocker dual of the lift on the dual operands, the
blind product [`blindfd`](../2026-11-20-ad-parallel-geometry/ad/AD_Geometry_Laws.thy#L25).

## Comparison

**P** marks a result proved in Isabelle (here or in production), **B** one checked by
brute force, and **A** one only argued. A ✗ cell names its counterexample below. "CSP" means
the law is the standard CSP law.

| Law | (e) lift | (b) F | (f) H | (a) minimal sets | (c) give up | (d) `⊞` |
| --- | --- | --- | --- | --- | --- | --- |
| L1 agrees on A2 | ✓ P | ✓ P | ✓ B | ✓ B | ✓ B | ✓ CSP |
| L2 monotone | ✓ P | ✓ P | ✓ B | ✗ C3 | ✗ C4 | ✓ B |
| L3 `a→Skip ∥ (a→Skip ⊔ b→Skip)` | `a→Miracle` P; with `□`: `a→Skip` B | `a→Skip ⊔ Stop` P, B | `a→Skip ⊔ Stop` B | `a→Skip ⊓ Stop` B | never does `a` B | `a→Skip` B |
| L4 distributes over the angelic choice | ✗ C1 P; one way P | ✗ C8 P; ✓ B without divergence; one way P | ✗ B | ✗ B | ✗ B | ✗ C6 B; one way B |
| L4 distributes over `⊓` | ✓ P | ✗ C2 P; one way P | ✗ C5 B | ✗ B | ✗ B | ✓ CSP |
| L5 commutative | ✓ P | ✓ P | ✓ B | ✓ B | ✓ B | ✓ CSP |
| L5 associative, functional `j` | ✓ P | ✓ B | ✓ B | ✗ B | ✓ B | ✓ CSP |
| L5 associative, relational `j` | ✗ C7 B | ✓ B, also with divergence | not checked | ✗ B | not checked | ✓ CSP |
| L5 Miracle and Chaos zeros | ✓ P | ✓ P | not checked | ✓ B | ✓ B | not checked |
| L6 A2 closure | ✓ P | ✓ P | ✓ B | ✓ B | ✓ B | ✓ A |
| L6 RAD closure | ✓ P | ✓ P | open | open | open; C4 result not refusal-closed | ✓ A |
| Angelic choice is a join | ✓ | ✓ | ✓ | ✓ | ✓ | ✗ B |
| Par-by-merge | ✓ | ✗ | ✗ | ✗ | ✗ | on A2 |

Proved entries:
- (e) L1–L6: [`rad_par_form`](../../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L54), [`rad_par_mono`](../../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L9), [`par_by_merge_disj_distl`](../../../deps/UTP/utp_concurrency.thy#L332), [`rad_par_comm`](../../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L15), [`ades_par_assoc_det`](../../../angelic-designs/utp_ades_parallel_algebra.thy#L351), [`rad_par_assoc_det_nd`](../../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L438), [`rad_par_miracle`](../../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L25), [`rad_par_chaos`](../../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L35) and [`rad_par_RAD`](../../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L91).
- (e) L3: [`rad_sync_angelic_miracle`](../2026-11-20-ad-parallel-geometry/rad/RAD_Probe.thy#L242), and [`ap_sync_angelic_miracle`](../2026-11-20-ad-parallel-geometry/ap/AP_Probe.thy#L105) for AP.
- (e) one-way distribution over `⊔`: [`rad_par_angelic_subdist`](Sync_Algebra.thy#L189).
- F, L1–L3: [`rad_par_F_A2`](Sync_Algebra.thy#L268), [`rad_par_F_mono`](Sync_Algebra.thy#L291) and [`rad_par_F_cooperates`](Sync_Algebra.thy#L391). The value `a→Skip ⊔ Stop` is brute force; Isabelle shows that F can end after `a`, which the lift cannot.
- F, L4–L6: [`rad_par_F_angelic_subdist`](Sync_F_Laws.thy#L223), [`rad_par_F_demonic_subdist`](Sync_F_Laws.thy#L244), [`rad_par_F_comm`](Sync_F_Laws.thy#L200) (symmetric `j`), [`rad_par_F_miracle`](Sync_F_Laws.thy#L268) and [`rad_par_F_chaos`](Sync_F_Laws.thy#L302) (the premises of the RAD laws), [`rad_par_F_A2_closed`](Sync_F_Laws.thy#L192), and [`rad_par_F_RAD`](Sync_F_Laws.thy#L171) for RAD operands and any `j`. RAD closure uses [`RAD_Inf_closed`](Sync_F_Laws.thy#L145): a nonempty join of RAD processes is RAD.

Associativity with Chaos needs a total merge, as for the installed laws. With a
partial `j`, both the lift and F fail.

### Counterexamples

Here `a`, `b`, `Stop` and `Miracle` stand for `a→Skip`, `b→Skip`, `Stop_RAD` and
`a→Miracle`, with `jsync`, unless stated.

- **C1, lift over `⊔`.** `a ∥ (a ⊔ b) = a→Miracle`, but `(a ∥ a) ⊔ (a ∥ b) = a ⊔ Stop`.
  The latter offers `{done_a, stop_ab}`, a set the lift never offers
  ([`rad_par_not_angelic_dist`](Sync_Algebra.thy#L221)). AD with the frame-disjoint
  merge: [`ades_par_jfd_not_angelic_dist`](Sync_Algebra.thy#L105).
- **C2, F over `⊓`.** `F(a ⊔ b, a ⊓ b) = (a ⊓ Stop) ⊔ (Stop ⊓ b)`, but
  `F(a ⊔ b, a) ⊓ F(a ⊔ b, b) = (a ⊔ Stop) ⊓ (Stop ⊔ b)` (brute force). The first offers
  `{done_a, done_b}`: every CSP process below `a ⊔ b` can end after `a` or after `b`,
  and `a ⊓ b` matches either. The second does not, because `b ∥ a` and `a ∥ b`
  deadlock ([`rad_par_F_not_demonic_dist`](Sync_F_Laws.thy#L634)). AD: `(x:=0 ⊔ x:=1) ∥ (y:=0 ⊓ y:=1)`
  is `⊔_u ⊓_v (x,y):=(u,v)` for F and `⊓_v ⊔_u (x,y):=(u,v)` for the lift
  ([`ades_angel_first_ne_demon_first`](Sync_Algebra.thy#L48)).
- **C3, minimal sets, monotonicity.** With the equality merge, `x:=2 ⊑ x:=1 ⊔ x:=2`.
  But `x:=2 ∥ x:=1 = Miracle`, while `(x:=1 ⊔ x:=2) ∥ x:=1 = x:=1`. In RAD,
  `b ⊑ a ⊔ b` and `a ∥ b = Stop`, but `a ∥ (a ⊔ b) = a ⊓ Stop`, which is not above `Stop`.
- **C4, give up, monotonicity.** `b→Skip ⊑ b→Skip ⊔ (Stop ⊓ a→Skip)`, with partner
  `b→Skip ⊓ b→Stop`. The demon pairs observations taken at different times, so
  every pair "gives up". For the same reason `a ∥ (a ⊔ b)` only waits at the start,
  with refusals `∅`, `{b}` and `{a,b}` but not `{a}`.
- **C5, H over `⊓`.** `a□b` is a deterministic refinement of `a ⊓ b`, so
  `H(a ⊓ b, a ⊔ b)` gains the term `(a□b) ∥ (a ⊔ b) = a ⊔ b` and falls below
  `H(a, a ⊔ b) ⊓ H(b, a ⊔ b)`.
- **C6, CSP parallel over `⊞`.** Take `P = a ⊓ b`, `Q = a` and `R = b`. Then
  `P ∥ (Q ⊞ R) = P`, while `(P∥Q) ⊞ (P∥R) = (a ⊓ Stop) ⊞ (Stop ⊓ b)` can deadlock at
  once. The law holds when `P` is deterministic.
- **C7, lift associativity with a relational merge.** For interleaving, take
  `P = b→Stop`, `Q = a→Stop` and `R = Skip ⊔ a→Stop`. For AD,
  `j(0,x) = {x}` and `j(1,1) = {0,1}` give
  `⟨1⟩ ∥ ⟨1⟩ ∥ (⟨0⟩ ⊔ ⟨1⟩)` as `⟨1⟩` or `⟨0⟩ ⊓ ⟨1⟩`
  ([AD guide](../../parallel/AD.md#lifted-merge-and-laws)). F gives `⟨0⟩ ⊓ ⟨1⟩` both ways.
- **C8, any monotone `∥` over `⊔`, with divergence.** Let `b'` be `b→Skip` with every
  observation from a started prior allowed to diverge as well
  ([`rad_div`](Sync_F_Laws.thy#L352)). It is RAD and A2, and `b' ⊑ b`. Since `a` never
  diverges there, `a ⊔ b' = a ⊔ b` ([`rad_div_join`](Sync_F_Laws.thy#L464)). But
  `a ∥ b'` can diverge at the start, so `(a ∥ a) ⊔ (a ∥ b')` can end after `a`. A
  monotone `a ∥ (a ⊔ b)` lies above `a ∥ b = Stop`, so it cannot end after `a`. This
  holds for every `∥` that agrees with RAD parallel on these three CSP pairs
  ([`sync_no_angelic_dist`](Sync_F_Laws.thy#L505)), including F
  ([`rad_par_F_not_angelic_dist`](Sync_F_Laws.thy#L537)).
  CSP closes divergence under extension, which would make `b'` Chaos and remove the
  example. In the abstract model, F distributes over `⊔` when `Q` and `R` are
  nondivergent or diverge on the same sets.

## Impossibility results

| Result | Status | Lemma |
| --- | --- | --- |
| No `∥` with `(x := u) ∥ (y := v) = (x,y) := (u,v)` distributes over `⊔` on the left and over `⊓` on the right: the two orders give `⊔_u ⊓_v` and `⊓_v ⊔_u` | P | [`dist_interchange`](Sync_Algebra.thy#L13), [`no_par_dist_both`](Sync_Algebra.thy#L92) |
| Every par-by-merge `∥` is monotone and distributes over `⊓`, for any merge; so none that agrees on assignments distributes over `⊔` | P | [`par_by_merge_disj_distl`](../../../deps/UTP/utp_concurrency.thy#L332), [`par_by_merge_mono_left`](../../../deps/UTP/utp_concurrency.thy#L355), [`ades_par_jfd_not_angelic_dist`](Sync_Algebra.thy#L105) |
| Any `∥` monotone on the right that agrees with `∥RAD[jsync]` on `a→Skip ∥ b→Skip` has `a→Skip ∥ (a→Skip ⊔ b→Skip) ≠ a→Skip` | P | [`sync_no_strong_cooperation`](Sync_Algebra.thy#L159) |
| F lies below every monotone `∥` that agrees with RAD parallel on RAD ∩ A2, and below the lift | P | [`rad_par_F_least`](Sync_Algebra.thy#L310), [`rad_par_F_below`](Sync_Algebra.thy#L326) |
| So `a→Skip ⊔ Stop`, F's value, is the least value of `a→Skip ∥ (a→Skip ⊔ b→Skip)` for such `∥` | P, B | - |
| In RAD, no `∥` that is monotone on the right and agrees with `∥RAD[jsync]` on `a ∥ a`, `a ∥ b` and `a ∥ b'` distributes over `⊔` (C8) | P | [`sync_no_angelic_dist`](Sync_F_Laws.thy#L505) |
| Without divergence, F is the only such `∥` that distributes over `⊔`: distribution and agreement fix it on joins of A2 processes | A | - |
| Within par-by-merge, a merge on choice sets that needs nonempty branch sets and merges single states no more than `j` gives at least the lift on up-closed operands, so `a→Skip ∥ (a→Skip ⊔ b→Skip)` stays at `a→Miracle` or above | P | [`par_lift_canonical`](../2026-11-20-ad-parallel-geometry/ad/AD_Lift_Canonical.thy#L109), [`par_ABm_eq`](../2026-11-20-ad-parallel-geometry/ad/AD_Lift_Canonical.thy#L136), [`rad_sync_angelic_stuck_any_lift`](../2026-11-20-ad-parallel-geometry/rad/RAD_Probe.thy#L303) |
| In AD with the equality merge, `x:=1 ∥ x:=2 = Miracle` is the top, so L1 and L2 force `x:=1 ∥ (x:=1 ⊔ x:=2) = Miracle` for every candidate | A, B | [`ades_par_eq_angelic_miracle`](../2026-11-20-ad-parallel-geometry/ad/AD_Geometry_Laws.thy#L678) |

So "no miracle from feasible operands" is possible only in reactive models,
where a failed synchronisation is `Stop`. There F reaches it, and no definition that
keeps `⊔` a join and `∥` monotone can do better.

## Who sees whom

The lift resolves every angel after both branches' demons. So the angel in one
branch reacts to the demon in the other without any communication
([`probe_par_clairvoyant`](../2026-11-20-ad-parallel-geometry/ad/AD_Geometry_Probe.thy#L125)),
and `P ;; Q ⊑ P ∥ Q` for frame-disjoint operands. F lets each angel see only its own
branch, so `F ⊑ P ;; Q`
([`blind_fref_seq_LR`](../2026-11-20-ad-parallel-geometry/ad/AD_Geometry_Laws.thy#L167)).
The two differ only in this order of resolution; on CSP processes they agree
([`blind_eq_par_a2`](../2026-11-20-ad-parallel-geometry/ad/AD_Geometry_Laws.thy#L364)).

Neither lets the angel learn which event the partner offers. With
`(a→Skip ⊓ b→Skip) ∥ (a→Skip ⊔ b→Skip)`, the angel would ideally give
`(a ⊔ Stop) ⊓ (Stop ⊔ b)`. The lift gives a process stuck at the start
([`rad_sync_demonic_angelic_stuck`](../2026-11-20-ad-parallel-geometry/rad/RAD_Probe.thy#L259)),
F gives `(a ⊓ Stop) ⊔ (Stop ⊓ b)`, and `H` gives `(a ⊔ Stop) ⊓ (Stop ⊔ b) ⊓ (a ⊔ b)`
(brute force). Reaching the ideal would need a choice resolved when events happen.
The one-shot UTP relation does not record that.

## Evidence

- **Isabelle:** session `Angelic_Sync_Probe` on `RAD_Geometry_Probe`. It uses real AD
  and RAD operators (`assigns_ades`, `⊓AD`, `⊔AD`, `∥AD`, `PrefixSkip_RAD`, `⊔RAD`,
  `⊓RAD`, `∥RAD`).
  - [`Sync_Algebra.thy`](Sync_Algebra.thy) has the impossibility results, the lift's
    failures and the definition of F as [`rad_par_F`](Sync_Algebra.thy#L250).
  - [`Sync_F_Laws.thy`](Sync_F_Laws.thy) has F's healthiness, zero laws,
    commutativity, one-way distributions, C2 and C8.
- **Brute force:** [`brute_force.py`](brute_force.py), about 30 s with a fixed seed.
  - Part A is the abstract model, with 2 and 3 states. It covers all 256 merges on
    2 states, random merges on 3, every symmetric associative merge on 3 states
    (4067), and the named AD examples.
  - Part B is the RAD observation model (`wait`, `tr`, `ref`) over `{a, b}`, with
    `jsync` and interleaving.
  - Part C is the CSP fragment with `⊞`.
- **Brute force with divergence:** [`brute_force_divergence.py`](brute_force_divergence.py),
  under a second. At one prior, a process is a pair of families: the sets offered
  with `ok'` true and those with `ok'` false. The merge follows `merge_rdes`. It
  checks F over `⊔` on all operands (it fails, as in C8) and on nondivergent ones
  (no failures). It also checks associativity for every total symmetric associative
  merge on 2 states (no failures).
- **Argued only:**
  - Without divergence, F distributes over `⊔`. The brute force confirms it; a proof
    would show per-prior join-primeness of A2, whose single instance used is
    [`A2_below_angelic_pick`](Sync_Algebra.thy#L330). It would also need each A2
    process below `Q` at one prior to extend to a RAD process below `Q`.
  - Without divergence, F is the only `⊔`-distributive candidate.
  - The meet normal form over A2 blocks is ill defined.
  - The AP versions follow at started priors, where
    [`ap_par_started`](../2026-11-20-ad-parallel-geometry/ap/AP_Probe.thy#L9) reduces
    AP parallel to RAD parallel.

## Not checked

- Divergence in the reactive and `⊞` brute-force models; the divergence script
  covers one prior only. The brute-force Chaos convention (`Chaos ∥ P = Chaos` for
  feasible `P`) holds only for total merges.
- F over `⊔` on operands whose divergence is closed under extension, as in CSP.
- Roscoe's operational `⊞` itself. Only the demon-first denotational reading was
  checked. The paper notes that it ignores divergence
  (Ribeiro & Cavalcanti 2019, p. 20).
- In Isabelle: AP closure of F, its `⊔`-distribution on nondivergent operands, and
  its associativity.
- Synchronisation on a proper subset of events; associativity of `H` and of give-up
  with relational merges.

## Rebuilding

From the repository root, with the patched Isabelle2026 profile (about 10 s once the
geometry probe heaps exist):

```sh
PROJECT_DIR="$PWD" ISABELLE_IDENTIFIER=utp-2026-patched timeout 400s \
  "$HOME/Applications/Isabelle2026-patched.app/bin/isabelle" build -o timeout=120 \
  -d deps -d . -d docs/reviews/2026-11-20-ad-parallel-geometry \
  -d docs/reviews/2026-11-25-angelic-sync-algebra Angelic_Sync_Probe
python3 -I docs/reviews/2026-11-25-angelic-sync-algebra/brute_force.py
python3 -I docs/reviews/2026-11-25-angelic-sync-algebra/brute_force_divergence.py
```
