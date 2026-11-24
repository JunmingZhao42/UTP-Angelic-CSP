# Reactive angelic design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [RD](RD.md) · [AD](AD.md) · [AP](AP.md)

Source, in import order: [`utp_rad_parallel_merge.thy`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy),
[`utp_rad_parallel_laws.thy`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy),
[`utp_rad_parallel_lifted_merge.thy`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy),
[`utp_rad_parallel_operator.thy`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy) and
[`utp_rad_parallel_algebra.thy`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy).
[Shared notation](README.md#shared-notation).

A RAD observation has an outer `ok` flag. The prior carries one inner state
(`wait`, trace, refusals); the branches and output carry choice sets
`acL`, `acR`, `ac'`. We first give laws for any RAD merge `M`, then lift the
RD merge of a state merge `j` to obtain `P ∥RAD[j] Q`.

- [Reactive angelic design parallel](#reactive-angelic-design-parallel)
  - [Generic merge healthiness and closure](#generic-merge-healthiness-and-closure)
    - [Generic correspondence with RD](#generic-correspondence-with-rd)
  - [Lifted merge and laws](#lifted-merge-and-laws)
    - [Choice-set lifting](#choice-set-lifting)
  - [ac2p/p2ac mapping laws](#ac2pp2ac-mapping-laws)

## Generic merge healthiness and closure

RAD reuses `PBMHm`, `ABm` and `H2m` from [AD](AD.md#generic-merge-healthiness-and-closure):

```isabelle
RA1m M   ≡ let X = {v ∈ ac'. tr ≤ v.tr} in X ≠ {} ∧ M[X/ac']
RA2m M   ≡ RA1m (M[0, acL − tr, acR − tr, ac' − tr / tr, acL, acR, ac'])
RA3m M   ≡ (acL ≠ {} ∧ acR ≠ {} ∧ II_Rac((ok,s),(ok',ac'))) ◁ wait ▷ M
CSPA1m M ≡ M ∨ (¬ok ∧ acL ≠ {} ∧ acR ≠ {} ∧ (∃v ∈ ac'. tr ≤ v.tr))
CSPA2m M ≡ M ;; J       (* this is just H2 *)

RADm ≡ RA2m ∘ RA3m ∘ CSPA1m ∘ PBMHm ∘ ABm ∘ CSPA2m
RAm  ≡ RA2m ∘ RA3m ∘ ABm
```

All conditions are idempotent and monotone. They commute pairwise
without premises, so the factors of `RADm` and `RAm` can be applied in any
order ([`RADm_comms`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L319)).
`RA2m` already supplies `RA1m`
([`RA1m_RA2m_absorb`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L136)),
so the combined conditions omit it.

| Law for `P ∥[M] Q` | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| `is RA1` | - | [`RA1m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L20) | [`rad_par_by_merge_RA1`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L31) |
| `is RA2` | Both `RA1`, `RA2` | [`RA2m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L27), [`ABm`](../../angelic-designs/utp_ades_parallel_merge.thy#L240) | [`rad_par_by_merge_RA2`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L70) |
| `is RA3` | Both `RA3` | [`RA3m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L38) | [`rad_par_by_merge_RA3`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L56) |
| `is RA` | Both `RA` | `RAm` | [`rad_par_by_merge_RA`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L137) |
| `is CSPA1` | Both `CSPA1` | [`CSPA1m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L47) | [`rad_par_by_merge_CSPA1`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L39) |
| `is CSPA2` | - | [`CSPA2m`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L57) | [`rad_par_by_merge_CSPA2`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L154) |
| `is PBMH_ades` | - | [`PBMHm`](../../angelic-designs/utp_ades_parallel_merge.thy#L235) | [`PBMH_ades_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L15) |
| `is RAD` | Both `RAD` | `RADm` | [`rad_par_by_merge_RAD`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L161) |
| `P ∥[M] (Q ⊓RAD R) =`<br>`(P ∥[M] Q) ⊓RAD (P ∥[M] R)` | - | - | [`rad_par_by_merge_demonic_distl`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L177) |
| `(P ⊓RAD Q) ∥[M] R =`<br>`(P ∥[M] R) ⊓RAD (Q ∥[M] R)` | - | - | [`rad_par_by_merge_demonic_distr`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L183) |
| `(P ∥[M] Q) ⊔RAD (P ∥[M] R) ⊑`<br>`P ∥[M] (Q ⊔RAD R)` | - | - | [`rad_par_by_merge_angelic_subdistl`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L189) |
| `(P ∥[M] R) ⊔RAD (Q ∥[M] R) ⊑`<br>`(P ⊔RAD Q) ∥[M] R` | - | - | [`rad_par_by_merge_angelic_subdistr`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L195) |

### Generic correspondence with RD

For an RD merge `M` and a RAD merge `AM`, let:

```isabelle
rad_lift_merge ≡ ABm ∘ ac'_lift_merge
AM = rad_lift_merge M
```

| Equality | Operand premises | Premises on `M` | Lemma |
| --- | --- | --- | --- |
| `P ∥[AM] Q =`<br>`p2ac (ac2p P ∥[M] ac2p Q)` | Both `RAD`, `A2` | - | [`rad_par_by_merge_form`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L18) |
| `ac2p (P ∥[AM] Q) =`<br>`ac2p P ∥[M] ac2p Q` | Both `RAD`, `A2` | - | [`rad_par_by_merge_ac2p`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L27) |

## Lifted merge and laws

### Choice-set lifting

[`rad_lift_merge`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L120)
uses the [AD choice-set lift](AD.md#lifted-merge-and-laws): both branch sets
must be nonempty, and every pair of branch states needs a witness in `ac'`.
Writing `obs(ok,s)` for an RD observation,
[`rad_lift_merge_obs`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L125)
unfolds it as:

```isabelle
rad_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  acL ≠ {} ∧ acR ≠ {} ∧
  (∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'.
    M(obs(ok,s),obs(okL,sL),obs(okR,sR),obs(ok',s')))
```

The RD merge supplies the divergence behaviour. For
`j :: ('t × 'e set) merge`, we lift the completed [RD merge](RD.md#lifted-merge-and-laws):

```isabelle
merge_rad ≡ rad_lift_merge ∘ merge_rdes

P ∥RAD[j] Q ≡ P ∥[merge_rad j] Q
```

[`merge_rdes_ORDm`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_lift.thy#L124)
and [`rad_lift_merge_RADm`](../../reactive-angelic-designs/utp_rad_parallel_lifted_merge.thy#L312)
ensure [`merge_rad`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L35)
is `RADm` for every `j`. Thus `∥RAD[j]` preserves RAD healthiness:

| Result of `P ∥RAD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `RAD` | Both `RAD` | [`rad_par_RAD`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L91) |
| `A2` | Both `RAD`, `A2` | [`rad_par_A2`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L86) |
| `NDRAD` | Both `RAD`, `A2`, `NDRAD` | [`rad_par_NDRAD`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L96) |

Its algebraic laws:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| monotone in both operands | - | - | [`rad_par_mono`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L9) |
| `P ∥RAD[j] (Q ⊓RAD R) =`<br>`(P ∥RAD[j] Q) ⊓RAD (P ∥RAD[j] R)` | - | - | [`rad_par_demonic_distl`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L66) |
| `(P ⊓RAD Q) ∥RAD[j] R =`<br>`(P ∥RAD[j] R) ⊓RAD (Q ∥RAD[j] R)` | - | - | [`rad_par_demonic_distr`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L71) |
| `(P ∥RAD[j] Q) ⊔RAD (P ∥RAD[j] R) ⊑`<br>`P ∥RAD[j] (Q ⊔RAD R)` | - | - | [`rad_par_angelic_subdistl`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L76) |
| `(P ∥RAD[j] R) ⊔RAD (Q ∥RAD[j] R) ⊑`<br>`(P ⊔RAD Q) ∥RAD[j] R` | - | - | [`rad_par_angelic_subdistr`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L81) |
| `(P ∥RAD[j] Q) ⊔RAD (P' ∥RAD[j] Q) =`<br>`(P ⊔RAD P') ∥RAD[j] Q` | `P`, `P'` both `RAD`; all `NDRAD`; `Q` intersection-closed | - | [`rad_par_angelic_distr`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L91) |
| `(Q ∥RAD[j] P) ⊔RAD (Q ∥RAD[j] P') =`<br>`Q ∥RAD[j] (P ⊔RAD P')` | `P`, `P'` both `RAD`; all `NDRAD`; `Q` intersection-closed | - | [`rad_par_angelic_distl`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L165) |
| `P ∥RAD[j] Q = Q ∥RAD[j] P` | - | `SymMerge` | [`rad_par_comm`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L15) |
| `(P ∥RAD[j] Q) ∥RAD[j] R =`<br>`P ∥RAD[j] (Q ∥RAD[j] R)` | All `RAD`, `A2`, `NDRAD` | `SymMerge`, `AssocMerge` | [`rad_par_assoc`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L49) |
| `(P ∥RAD[j] Q) ∥RAD[j] R =`<br>`P ∥RAD[j] (Q ∥RAD[j] R)` | All `NDRAD` | `SymMerge`, `AssocMerge`, `Functional` | [`rad_par_assoc_det_nd`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L330) |

Here `Q` is intersection-closed when `Q(True,s,True,Y)` and
`Q(True,s,True,Y')` imply `Q(True,s,True,Y ∩ Y')` for every prior state `s`.
This premise covers waiting states and mixed waiting/terminating offers too.
The equalities need no A2 or restriction on `j`. The proof uses nondivergence; whether
it is necessary for RAD is open. AD's counterexample does not carry over directly: RAD's
merge sets `ok' = okL ∧ okR`, so a diverging branch yields only diverging observations,
whereas AD's merge lets it release terminating ones.

[`rad_par_assoc_det_nd`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L330) drops A2: with a deterministic `j` the
intermediate result of each branch pair is fixed, so operands may have angelic choice,
and `j` may be partial. As for AD's `ades_par_assoc_det_nd`, it guards the merge to
nondivergent branches ([`merge_rad_guard_AssocMerge`](../../reactive-angelic-designs/utp_rad_parallel_algebra.thy#L245), with RD's guard: a
started, non-waiting prior gives a terminating result) and applies
[`par_by_merge_assoc_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L75).
Associativity with divergent operands remains open, as for RD.

## Canonicity

`rad_lift_merge N = ABm (ac'_lift_merge N)`, so the
[shared choice-set canonicity results](AD.md#shared-choice-set-canonicity)
specialise directly to RAD's trace, waiting and refusal alphabet. In particular,
[`choice_lift_refine_iff`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L110) gives
`rad_lift_merge N ⊑ M` iff `singleton_refines N M` for `M is ABm`.

| Result | Merge premises | Lemma |
| --- | --- | --- |
| `P ∥RAD[j] Q ⊑ P ∥[M] Q` | `M is ABm`, `singleton_refines (merge_rdes j) M` | [`rad_par_canonical`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L115) |

It needs no operand healthiness or A2 premise. Its comparison
premises do not assert RAD closure of parallel with the arbitrary merge `M`.

## ac2p/p2ac mapping laws

These instantiate the generic correspondence with `M = merge_rdes j`:

| Equality | Operand premises | Lemma |
| --- | --- | --- |
| `p2ac D ∥RAD[j] p2ac E =`<br>`p2ac (D ∥RD[j] E)` | - | [`rad_par_p2ac`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L47) |
| `P ∥RAD[j] Q =`<br>`p2ac (ac2p P ∥RD[j] ac2p Q)` | Both `RAD`, `A2` | [`rad_par_form`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L54) |
| `ac2p (P ∥RAD[j] Q) =`<br>`ac2p P ∥RD[j] ac2p Q` | Both `RAD`, `A2` | [`rad_par_ac2p`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L73) |
| `D ∥RD[j] E =`<br>`ac2p (p2ac D ∥RAD[j] p2ac E)` | - | [`rad_par_ac2p_p2ac`](../../reactive-angelic-designs/utp_rad_parallel_operator.thy#L79) |

RAD rejects empty output sets
([`RAD_empty`](../../reactive-angelic-designs/utp_rad_designs.thy#L534)), so there
is no `d2ac` route as in AD.
