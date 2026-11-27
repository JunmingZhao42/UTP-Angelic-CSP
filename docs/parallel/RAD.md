# Reactive angelic design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [RD](RD.md) · [AD](AD.md) · [AP](AP.md)

Source files, in import order:

- [`utp_rad_parallel_merge.thy`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy)
- [`utp_rad_parallel_laws.thy`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy)
- [`utp_rad_parallel_lifted_merge.thy`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy)
- [`utp_rad_parallel_operator.thy`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy)
- [`utp_rad_parallel_algebra.thy`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy)

[Shared notation](README.md#shared-notation).

A RAD observation has an outer `ok` flag. The prior carries one inner state
(`wait`, trace, refusals); the branches and output carry choice sets
`acL`, `acR`, `ac'`. We lift the RD
merge of a state merge `j` to obtain `P ∥RAD[j] Q`, and give each law for any RAD
merge `M`, with its instance for `∥RAD[j]`.
[Canonicity](Canonicity.md#rad) compares this lift with other merges on choice sets.

- [Merge conditions](#merge-conditions)
- [The lifted merge](#the-lifted-merge)
- [Closure](#closure)
- [Monotonicity and choice](#monotonicity-and-choice)
- [Symmetry and associativity](#symmetry-and-associativity)
- [Zero laws](#zero-laws)
- [Correspondence with RD](#correspondence-with-rd)
- [Angelic choice against a synchronising partner](#angelic-choice-against-a-synchronising-partner)

## Merge conditions

RAD reuses `PBMHm` and `H2m` from [AD](AD.md#merge-conditions):

```isabelle
RA1m M   ≡ let X = {v ∈ ac'. tr ≤ v.tr} in X ≠ {} ∧ M[X/ac']
RA2m M   ≡ RA1m (M[0, acL − tr, acR − tr, ac' − tr / tr, acL, acR, ac'])
RA2APm M ≡ M[0, acL − tr, acR − tr, {v ∈ ac'. tr ≤ v.tr} − tr / tr, acL, acR, ac']
RA3m M   ≡ (acL ≠ {} ∧ acR ≠ {} ∧ II_Rac((ok,s),(ok',ac'))) ◁ wait ▷ M
CSPA1m M ≡ M ∨ (¬ok ∧ acL ≠ {} ∧ acR ≠ {} ∧ (∃v ∈ ac'. tr ≤ v.tr))
CSPA2m M ≡ M ;; J       (* this is just H2 *)

RADm ≡ RA2m ∘ RA3m ∘ CSPA1m ∘ PBMHm ∘ CSPA2m
RAm  ≡ RA2m ∘ RA3m
```

- All conditions are idempotent and monotone.
- They commute pairwise without premises, so the factors of `RADm` and `RAm` can
  be applied in any order ([`RADm_comms`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L330)).
- `RA2m` already supplies `RA1m` ([`RA1m_RA2m_absorb`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L191)), so the combined
  conditions omit `RA1m`.
- [`RA2APm`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L41) is `RA2m` without the trace-extension check on the output:
  `RA2m M = RA2APm M ∧ (∃v ∈ ac'. tr ≤ v.tr)`. RA2 closure needs only `RA2APm`,
  and every `RA2m` merge is `RA2APm` ([`RA2m_is_RA2APm`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L166)).

## The lifted merge

We lift RD merges with the [AD choice-set lift](AD.md#the-lifted-merge)
[`ac'_lift_merge`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L17):
both branch sets must be nonempty, and every pair of branch states needs a witness
in `ac'`. Writing `obs(ok,s)` for an RD observation,
[`ac'_lift_merge_obs`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L27)
unfolds the lift as:

```isabelle
ac'_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  acL ≠ {} ∧ acR ≠ {} ∧
  (∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'.
    M(obs(ok,s),obs(okL,sL),obs(okR,sR),obs(ok',s')))
```

For `j :: ('t × 'e set) merge`, we lift the completed [RD merge](RD.md#the-lifted-merge)
with `ac'_lift_merge`. The RD merge supplies the divergence behaviour:

```isabelle
merge_rad ≡ ac'_lift_merge ∘ merge_rdes

P ∥RAD[j] Q ≡ P ∥[merge_rad j] Q
```

## Closure

Each closure rule holds for any `M` that satisfies its merge premises.
[`merge_rad`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L35) `j` lifts `merge_rdes j`, which is `ORDm` ([`merge_rdes_ORDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L124)), and
the lift lemmas turn `ORDm` into each merge premise. So
[`ac'_lift_merge_RADm`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L261) makes `merge_rad j` `RADm` for every `j`:

| `P ∥[M] Q` is | Operand premises | Merge premises | Lemma | `merge_rad j` | `P ∥RAD[j] Q` |
| --- | --- | --- | --- | --- | --- |
| `RA1` | - | [`RA1m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L20) | [`rad_par_by_merge_RA1`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L9) | [`ac'_lift_merge_RA1m`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L208) | - |
| `RA2` | Both `RA2`, `PBMH_ades` | [`RA2APm`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L41) | [`rad_par_by_merge_RA2`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L53) | [`ac'_lift_merge_RA2m`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L216), [`RA2m_is_RA2APm`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L166) | - |
| `RA3` | Both `RA3` | [`RA3m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L51) | [`rad_par_by_merge_RA3`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L34) | [`ac'_lift_merge_RA3m`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L234) | - |
| `RA` | Both `RA`, `PBMH_ades` | `RAm` | [`rad_par_by_merge_RA`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L137) | - | - |
| `CSPA1` | Both `CSPA1` | [`CSPA1m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L60) | [`rad_par_by_merge_CSPA1`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L17) | [`ac'_lift_merge_CSPA1m`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L226) | - |
| `CSPA2` | - | [`CSPA2m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L70) | [`rad_par_by_merge_CSPA2`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L154) | [`ac'_lift_merge_CSPA2m`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L113) | - |
| `PBMH_ades` | - | [`PBMHm`](../../angelic-designs/utp_ades_parallel_merge.thy#L176) | [`PBMH_ades_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L15) | [`ac'_lift_merge_PBMHm`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L34) | - |
| `RAD` | Both `RAD` | `RADm` | [`rad_par_by_merge_RAD`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L148) | [`ac'_lift_merge_RADm`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L261) | [`rad_par_RAD`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L91) |

The `RA2` rule asks for `PBMH_ades` operands: a branch observation then survives trace
normalisation with all its choices, not just the trace extensions. RAD operands are `PBMH_ades`
([`RAD_is_PBMH_ades`](../../reactive-angelic-designs/utp_rad_designs.thy#L322)), so the `RAD` rule needs no extra premise.

For `∥RAD[j]`, parallel also preserves:

| Result of `P ∥RAD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `A2` | Both `RAD`, `A2` | [`rad_par_A2`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L86) |
| `NDRAD` | Both `RAD`, `A2`, `NDRAD` | [`rad_par_NDRAD`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L96) |

## Monotonicity and choice

RAD choices are disjunction and conjunction, so the
[generic laws](Generic.md#parallel-operator) give the laws below for any `M`. The
last column gives each law for `∥RAD[j]`. These `∥RAD[j]` laws, and those of the
next two sections, hold off A2, for operands with angelic choice, unless a row
lists `A2`.

| Property | Law for `P ∥[M] Q` | Lemma | `P ∥RAD[j] Q` |
| --- | --- | --- | --- |
| Monotonic | `P ⊑ P' ∧ Q ⊑ Q' ⟹`<br>`P ∥[M] Q ⊑ P' ∥[M] Q'` | [`par_by_merge_mono`](../../deps/UTP/utp_concurrency.thy#L370) | [`rad_par_mono`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L9) |
| Distributes over `⊓RAD` | `P ∥[M] (Q ⊓RAD R) =`<br>`(P ∥[M] Q) ⊓RAD (P ∥[M] R)` | [`rad_par_by_merge_demonic_distl`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L165) | [`rad_par_demonic_distl`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L174) |
| Distributes over `⊓RAD` | `(P ⊓RAD Q) ∥[M] R =`<br>`(P ∥[M] R) ⊓RAD (Q ∥[M] R)` | [`rad_par_by_merge_demonic_distr`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L171) | [`rad_par_demonic_distr`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L179) |
| Subdistributes over `⊔RAD` | `(P ∥[M] Q) ⊔RAD (P ∥[M] R) ⊑`<br>`P ∥[M] (Q ⊔RAD R)` | [`rad_par_by_merge_angelic_subdistl`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L177) | [`rad_par_angelic_subdistl`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L184) |
| Subdistributes over `⊔RAD` | `(P ∥[M] R) ⊔RAD (Q ∥[M] R) ⊑`<br>`(P ⊔RAD Q) ∥[M] R` | [`rad_par_by_merge_angelic_subdistr`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L183) | [`rad_par_angelic_subdistr`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L189) |

For `∥RAD[j]`, the subdistributions become equalities under extra premises:

| Property | Law | Operand premises | Lemma |
| --- | --- | --- | --- |
| Distributes over `⊔RAD` | `(P ∥RAD[j] R) ⊔RAD (Q ∥RAD[j] R) =`<br>`(P ⊔RAD Q) ∥RAD[j] R` | `P`, `Q` both `RAD`; all `NDRAD`; `R` intersection-closed | [`rad_par_angelic_distr`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L199) |
| Distributes over `⊔RAD` | `(P ∥RAD[j] Q) ⊔RAD (P ∥RAD[j] R) =`<br>`P ∥RAD[j] (Q ⊔RAD R)` | `Q`, `R` both `RAD`; all `NDRAD`; `P` intersection-closed | [`rad_par_angelic_distl`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L273) |

- `R` is intersection-closed when `R(True,s,True,Y)` and `R(True,s,True,Y')` imply
  `R(True,s,True,Y ∩ Y')` for every prior state `s`, waiting ones included.
- The `⊔` equalities use nondivergence; whether RAD needs nondivergence is open.
- AD's counterexample does not carry over, since RAD's merge sets
  `ok' = okL ∧ okR` and a diverging branch yields only diverging observations.

## Symmetry and associativity

For any `M`, the [generic laws](Generic.md#parallel-operator) give symmetry from
`SymMerge` ([`par_by_merge_comm`](../../deps/UTP/utp_concurrency.thy#L414)), and associativity from `SymMerge` and
`AssocMerge` ([`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30)) or, on nondivergent operands, from
`AssocMerge` of the guarded merge ([`par_by_merge_assoc_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L75)). With
premises on `j`, the lifted merge has these properties:

| Property of `merge_rad j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `SymMerge` | `SymMerge` | [`ac'_lift_merge_SymMerge`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L40), [`merge_rdes_SymMerge`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L159) |
| `AssocMerge` on nondivergent branches | `Functional`, `AssocMerge` | [`merge_rad_guard_AssocMerge`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L353) |

So `∥RAD[j]` is symmetric and associative:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `P ∥RAD[j] Q = Q ∥RAD[j] P` | - | `SymMerge` | [`rad_par_comm`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L15) |
| `(P ∥RAD[j] Q) ∥RAD[j] R =`<br>`P ∥RAD[j] (Q ∥RAD[j] R)` | All `NDRAD` | `SymMerge`, `AssocMerge`, `Functional` | [`rad_par_assoc_det_nd`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L438) |
| `(P ∥RAD[j] Q) ∥RAD[j] R =`<br>`P ∥RAD[j] (Q ∥RAD[j] R)` | All `RAD`, `A2`, `NDRAD` | `SymMerge`, `AssocMerge` | [`rad_par_assoc`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L134) |
| `(P ∥RAD[j] Q) ∥RAD[j] R =`<br>`P ∥RAD[j] (Q ∥RAD[j] R)` | All `RAD`, `A2`; all `ac2p` images `NRD` | `SymMerge`, `AssocMerge`, absorbing | [`rad_par_assoc_nrd`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L147) |

- With a deterministic `j`, each branch pair has one intermediate result, so
  `rad_par_assoc_det_nd` needs no A2 and allows a partial `j`.
- Associativity with divergent operands off A2 is open.
- On A2 operands, `rad_par_assoc` and `rad_par_assoc_nrd` transfer RD associativity
  through `ac2p`, with the [RD](RD.md#symmetry-and-associativity) premises on `j`
  ([Correspondence with RD](#correspondence-with-rd)).

## Zero laws

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `P ∥RAD[j] ⊤RAD =`<br>`⊤RAD ∥RAD[j] P = ⊤RAD` | `P is RAD` | - | [`rad_par_miracle`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L25) |
| `P ∥RAD[j] Chaos_RAD =`<br>`Chaos_RAD ∥RAD[j] P = Chaos_RAD` | `P is RAD`, `(ac2p P ∧ tr' = tr) is H4` | merges empty traces | [`rad_par_chaos`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L35) |

- Every RAD process lies between `Chaos_RAD` and `⊤RAD`, which agree at unstarted
  and waiting priors ([`Chaos_RAD_eval`](../../reactive-angelic-designs/utp_rad_choice.thy#L279), [`top_RAD_eval`](../../reactive-angelic-designs/utp_rad_choice.thy#L287)). So the zero laws
  compare only active priors, through [`RAD_eq_active`](../../reactive-angelic-designs/utp_rad_choice.thy#L299).
- At an active prior `⊤RAD` has no observation, which gives the Miracle law.
- The Chaos law has the premises of the [RD Chaos law](RD.md#zero-laws),
  with the prior-trace observation taken from `ac2p P`, a singleton choice of `P`.
  Off A2 this is sufficient, not exact.

## Correspondence with RD

For an RD merge `M`, let `AM` be its choice-set lift:

```isabelle
AM = ac'_lift_merge M
```

| Equality | Operand premises | Premises on `M` | Lemma | `P ∥RAD[j] Q` |
| --- | --- | --- | --- | --- |
| `P ∥[AM] Q =`<br>`p2ac (ac2p P ∥[M] ac2p Q)` | Both `RAD`, `A2` | - | [`rad_par_by_merge_form`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L18) | [`rad_par_form`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L54) |
| `ac2p (P ∥[AM] Q) =`<br>`ac2p P ∥[M] ac2p Q` | Both `RAD`, `A2` | - | [`rad_par_by_merge_ac2p`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L27) | [`rad_par_ac2p`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L73) |
| `(P ∥[AM] Q) ∥[AM] R =`<br>`P ∥[AM] (Q ∥[AM] R)` | All `RAD`, `A2`, `NDRAD` | the [RD](RD.md#symmetry-and-associativity) premises of `par_by_merge_assoc_NDRD` | [`par_by_ac'_lift_merge_assoc_NDRAD`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L109) | [`rad_par_assoc`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L134) |

The last column takes `M = merge_rdes j`, since `merge_rad j = AM` there. The
lifted operator also gives:

| Equality | Operand premises | Lemma |
| --- | --- | --- |
| `p2ac D ∥RAD[j] p2ac E =`<br>`p2ac (D ∥RD[j] E)` | - | [`rad_par_p2ac`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L47) |
| `D ∥RD[j] E =`<br>`ac2p (p2ac D ∥RAD[j] p2ac E)` | - | [`rad_par_ac2p_p2ac`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L79) |
| `Chaos_RAD = p2ac ⊥RD` | - | [`Chaos_RAD_p2ac`](../../reactive-angelic-designs/utp_rad_choice.thy#L263) |

RAD rejects empty output sets ([`RAD_empty`](../../reactive-angelic-designs/utp_rad_designs.thy#L538)), so there is no `d2ac` route as
in AD.

## Angelic choice against a synchronising partner

The lift merges every pair of kept-open alternatives before the angel picks, so
an alternative the partner cannot match still blocks. With `jsync`, which
synchronises on every event, and `a ≠ b` ([`rad_sync_angelic_miracle`](../reviews/2026-11-20-ad-parallel-geometry/rad/RAD_Probe.thy#L242)):

```isabelle
PrefixSkip_RAD a ∥RAD[jsync] (PrefixSkip_RAD a ⊔RAD PrefixSkip_RAD b) = a →RAD ⊤RAD
```

- By [canonicity](Canonicity.md#rad), no admissible lift avoids this.
- We use external choice for a choice the partner resolves: in CSP,
  `a→Skip ∥ (a→Skip □ b→Skip) = a→Skip`.
- We keep the lift, since no monotone parallel gives `a→Skip` while `⊔` is a join
  ([`sync_no_strong_cooperation`](../reviews/2026-11-25-angelic-sync-algebra/Sync_Algebra.thy#L159)).

The least monotone parallel F that agrees with RAD parallel on A2 operands is the
join of `g ∥RAD[j] h` over A2 processes `g ⊑ P` and `h ⊑ Q`
([`rad_par_F_least`](../reviews/2026-11-25-angelic-sync-algebra/Sync_Algebra.thy#L310)):

- F gives `a→Skip ⊔ Stop` (by brute force);
- F is not par-by-merge and does not distribute over `⊓` off A2;
- the [comparison of candidate algebras](../reviews/2026-11-25-angelic-sync-algebra/README.md)
  has the laws of F; the associativity of F is [open](../../PLAN.md#stage-6--ap-and-documentation).
