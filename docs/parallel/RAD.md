# Reactive angelic design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [RD](RD.md) · [AD](AD.md) · [AP](AP.md)

Source: [`utp_rad_parallel_laws.thy`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy) and
[`utp_rad_parallel_lift.thy`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy).
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
order ([`RADm_comms`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L321)).
`RA2m` already supplies `RA1m`
([`RA1m_RA2m_absorb`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L138)),
so the combined conditions omit it.

| Law for `P ∥[M] Q` | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| `is RA1` | - | [`RA1m`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L22) | [`rad_par_by_merge_RA1`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L397) |
| `is RA2` | Both `RA1`, `RA2` | [`RA2m`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L29), [`ABm`](../../angelic-designs/utp_ades_parallel_laws.thy#L240) | [`rad_par_by_merge_RA2`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L436) |
| `is RA3` | Both `RA3` | [`RA3m`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L40) | [`rad_par_by_merge_RA3`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L422) |
| `is RA` | Both `RA` | `RAm` | [`rad_par_by_merge_RA`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L503) |
| `is CSPA1` | Both `CSPA1` | [`CSPA1m`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L49) | [`rad_par_by_merge_CSPA1`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L405) |
| `is CSPA2` | - | [`CSPA2m`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L59) | [`rad_par_by_merge_CSPA2`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L520) |
| `is PBMH_ades` | - | [`PBMHm`](../../angelic-designs/utp_ades_parallel_laws.thy#L235) | [`PBMH_ades_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L387) |
| `is RAD` | Both `RAD` | `RADm` | [`rad_par_by_merge_RAD`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L527) |

### Generic correspondence with RD

For an RD merge `M` and a RAD merge `AM`, let:

```isabelle
rad_lift_merge ≡ ABm ∘ ac'_lift_merge
AM = rad_lift_merge M
```

| Equality | Operand premises | Premises on `M` | Lemma |
| --- | --- | --- | --- |
| `P ∥[AM] Q =`<br>`p2ac (ac2p P ∥[M] ac2p Q)` | Both `RAD`, `A2` | - | [`rad_par_by_merge_form`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L331) |
| `ac2p (P ∥[AM] Q) =`<br>`ac2p P ∥[M] ac2p Q` | Both `RAD`, `A2` | - | [`rad_par_by_merge_ac2p`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L340) |

## Lifted merge and laws

### Choice-set lifting

[`rad_lift_merge`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L120)
uses the [AD choice-set lift](AD.md#lifted-merge-and-laws): both branch sets
must be nonempty, and every pair of branch states needs a witness in `ac'`.
Writing `obs(ok,s)` for an RD observation,
[`rad_lift_merge_obs`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L125)
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
and [`rad_lift_merge_RADm`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L312)
ensure [`merge_rad`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L348)
is `RADm` for every `j`. Thus `∥RAD[j]` preserves RAD healthiness:

| Result of `P ∥RAD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `RAD` | Both `RAD` | [`rad_par_RAD`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L391) |
| `A2` | Both `RAD`, `A2` | [`rad_par_A2`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L386) |
| `NDRAD` | Both `RAD`, `A2`, `NDRAD` | [`rad_par_NDRAD`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L396) |

Its algebraic laws:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| monotone in both operands | - | - | [`rad_par_mono`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L414) |
| `P ∥RAD[j] Q = Q ∥RAD[j] P` | - | `SymMerge` | [`rad_par_comm`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L420) |
| `(P ∥RAD[j] Q) ∥RAD[j] R =`<br>`P ∥RAD[j] (Q ∥RAD[j] R)` | All `RAD`, `A2`, `NDRAD` | `SymMerge`, `AssocMerge` | [`rad_par_assoc`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L454) |

## ac2p/p2ac mapping laws

These instantiate the generic correspondence with `M = merge_rdes j`:

| Equality | Operand premises | Lemma |
| --- | --- | --- |
| `p2ac D ∥RAD[j] p2ac E =`<br>`p2ac (D ∥RD[j] E)` | - | [`rad_par_p2ac`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L360) |
| `P ∥RAD[j] Q =`<br>`p2ac (ac2p P ∥RD[j] ac2p Q)` | Both `RAD`, `A2` | [`rad_par_form`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L367) |
| `ac2p (P ∥RAD[j] Q) =`<br>`ac2p P ∥RD[j] ac2p Q` | Both `RAD`, `A2` | [`rad_par_ac2p`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L373) |
| `D ∥RD[j] E =`<br>`ac2p (p2ac D ∥RAD[j] p2ac E)` | - | [`rad_par_ac2p_p2ac`](../../reactive-angelic-designs/utp_rad_parallel_lift.thy#L379) |

RAD rejects empty output sets
([`RAD_empty`](../../reactive-angelic-designs/utp_rad_designs.thy#L534)), so there
is no `d2ac` route as in AD.
