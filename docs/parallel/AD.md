# Angelic design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [D](D.md) · [RAD](RAD.md)

Source: [`utp_ades_parallel_laws.thy`](../../angelic-designs/utp_ades_parallel_laws.thy) and
[`utp_ades_parallel_lift.thy`](../../angelic-designs/utp_ades_parallel_lift.thy).
[Shared notation](README.md#shared-notation).

AD branches and outputs carry choice sets `acL, acR, ac'` instead of single
states. We first give laws for any AD merge `M`, then lift a state merge `j`
through choice sets and obtain `P ∥AD[j] Q`.

- [Angelic design parallel](#angelic-design-parallel)
  - [Generic merge healthiness and closure](#generic-merge-healthiness-and-closure)
    - [Correspondence with Designs](#correspondence-with-designs)
  - [Lifted merge and laws](#lifted-merge-and-laws)
  - [ac2p/d2ac mapping laws](#ac2pd2ac-mapping-laws)

## Generic merge healthiness and closure

AD merges reuse the [design merge conditions](D.md#generic-merge-healthiness-and-closure)
`H1m`, `H2m`, `H3m` and `HDm` unchanged, since these allow the branch and output
alphabets to differ from the prior.

AD adds a merge condition for each AD
healthiness condition, with `m` the merge input `((ok,s),(okL,acL),(okR,acR))`:

```isabelle
A0m M ≡ M ∧ (ok ∧ ac' = {} ⟶ M[false/ok'])
A1m   ≡ HDm ∘ PBMH_ades
ADm   ≡ A0m ∘ A1m
A2m M ≡ (((∃sL. acL = {sL}) ∧ (∃sR. acR = {sR})) ∨ M) ∧
  (∀sL sR. (acL = {} ∨ sL ∈ acL) ∧ (acR = {} ∨ sR ∈ acR) ⟶
    (A2 M)[{sL},{sR}/acL,acR])
PBMHm M ≡ PBMH_ades (M ∧ ac' ≠ {})
ABm M ≡ acL ≠ {} ∧ acR ≠ {} ∧
  (∃X Y. acL ⊆ X ∧ acR ⊆ Y ∧ M[X,Y/acL,acR])
```

These healthiness conditions are idempotent and monotone. The proved commutation laws are:

| Condition | Commutes with |
| --- | --- |
| `H1m` | `A0m`, `A1m`, `A2m` |
| `H2m` | `A0m`, `A1m`, `PBMHm`, `ABm` |
| `H3m`, `HDm` | `A0m`, `A1m` |
| `PBMHm` | `ABm` |

In general, `A0m`, `A1m` and `A2m` do not commute pairwise. `A2m` also
does not commute with `H2m`, `H3m` or `HDm`.

| Law for `P ∥[M] Q` | Operand premises | Merge premises | Lemma |
| --- | --- | --- | --- |
| `is A0` | - | `A0m` | [`A0_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L396) |
| `is A1` | Both `H1` | `A1m` | [`A1_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L408) |
| `is A` | Both `H1` | [`ADm`](../../angelic-designs/utp_ades_parallel_laws.thy#L88) | [`A_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L443) |
| `is A2` | Both `A2` | `A2m` | [`A2_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L453) |
| `is A3` | Both `H1` | `H1m`, `H3m` | [`A3_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L482) |
| `is PBMH_ades` | - | `PBMHm` | [`PBMH_ades_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L387) |

Commutativity and associativity for any `M` are the [generic laws](Generic.md).

### Correspondence with Designs

For a Design merge `M` and an AD merge `AM`, let:

```isabelle
AM = H3m (H1m (ABm (ac'_lift_merge M)))
```

| Equality | Operand premises | Premises on `M` | Lemma |
| --- | --- | --- | --- |
| `P ∥[AM] Q =`<br>`d2ac (ac2p P ∥[M] ac2p Q)` | Both `A`, `A2` | `HDm`, `H3m` | [`ades_par_by_merge_d2ac_ac2p`](../../angelic-designs/utp_ades_parallel_laws.thy#L563) |
| `ac2p (P ∥[AM] Q) =`<br>`ac2p P ∥[M] ac2p Q` | Both `A`, `A2` | `HDm`, `H3m` | [`ades_par_by_merge_ac2p`](../../angelic-designs/utp_ades_parallel_laws.thy#L680) |

## Lifted merge and laws

We lift a design merge `M` by taking ∀∀∃ quantifier over the branches choice sets `acL` `acR` and the final choice set `ac'`:

```isabelle
ac'_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
  ∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'. M((ok,s),(okL,sL),(okR,sR),(ok',s'))
```

We lift the raw design merge of `j`, then apply `ABm`, `H1m` and `H3m`:

```isabelle
merge_ades ≡ H3m ∘ H1m ∘ ABm ∘ ac'_lift_merge ∘ merge_des_raw

P ∥AD[j] Q ≡ P ∥[merge_ades j] Q
```

[`merge_ades_obs`](../../angelic-designs/utp_ades_parallel_lift.thy#L28) unfolds it:
after start the branch sets are nonempty and every pair of branch states can
merge; if both branches terminate, so does the output, with a witness in `ac'`.

```isabelle
merge_ades j ((ok,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  ¬ok ∨ (acL ≠ {} ∧ acR ≠ {} ∧ (∀sL ∈ acL. ∀sR ∈ acR. ∃u. j(s,sL,sR,u)) ∧
         (okL ∧ okR ⟶ ok' ∧ (∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'. j(s,sL,sR,s'))))
```

The lifted merge inherits these properties:

| Property of `merge_ades j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `H1m` | - | [`merge_ades_is_H1m`](../../angelic-designs/utp_ades_parallel_lift.thy#L64) |
| `H2m` | - | [`merge_ades_is_H2m`](../../angelic-designs/utp_ades_parallel_lift.thy#L67) |
| `HDm` | - | [`merge_ades_is_HDm`](../../angelic-designs/utp_ades_parallel_lift.thy#L70) |
| `H3m` | - | [`merge_ades_is_H3m`](../../angelic-designs/utp_ades_parallel_lift.thy#L73) |
| `A0m` | - | [`merge_ades_is_A0m`](../../angelic-designs/utp_ades_parallel_lift.thy#L76) |
| `A1m` | - | [`merge_ades_is_A1m`](../../angelic-designs/utp_ades_parallel_lift.thy#L81) |
| `ADm` | - | [`merge_ades_is_ADm`](../../angelic-designs/utp_ades_parallel_lift.thy#L86) |
| `A2m` | - | [`merge_ades_is_A2m`](../../angelic-designs/utp_ades_parallel_lift.thy#L89) |

So `∥AD[j]` preserves AD healthiness:

| Result of `P ∥AD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `A0` | - | [`ades_par_A0_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L174) |
| `A1` | Both `H1` | [`ades_par_A1_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L179) |
| `A` | Both `H1` | [`ades_par_A_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L185) |
| `A2` | Both `A2` | [`ades_par_A2_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L191) |
| `A3` | Both `H1` | [`ades_par_A3_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L197) |

Its algebraic laws:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `P ∥AD[j] Q = A P ∥AD[j] A Q` | Both `H1`, `A2` | - | [`ades_par_normalise_A`](../../angelic-designs/utp_ades_parallel_lift.thy#L152) |
| monotone in both operands | - | - | [`ades_par_mono`](../../angelic-designs/utp_ades_parallel_lift.thy#L235) |
| `P ∥AD[j] Q = Q ∥AD[j] P` | - | `SymMerge` | [`ades_par_comm`](../../angelic-designs/utp_ades_parallel_lift.thy#L281) |
| `(P ∥AD[j] Q) ∥AD[j] R =`<br>`P ∥AD[j] (Q ∥AD[j] R)` | All `H1`, `A2` | `SymMerge`, `AssocMerge`, `mergeable` | [`ades_par_assoc`](../../angelic-designs/utp_ades_parallel_lift.thy#L351) |
| `(P ∥AD[j] Q) ∥AD[j] R =`<br>`P ∥AD[j] (Q ∥AD[j] R)` | All `H1`, `A2`, `NDAD` | `SymMerge`, `AssocMerge` | [`ades_par_assoc_nd`](../../angelic-designs/utp_ades_parallel_lift.thy#L368) |
| `P ∥AD[j] Miracle =`<br>`Miracle ∥AD[j] P = Miracle` | `P is H1` | - | [`ades_par_miracle`](../../angelic-designs/utp_ades_parallel_lift.thy#L266) |
| `Chaos ∥AD[j] Chaos = Chaos` | - | `∀s. ∃sL sR u. j(s,sL,sR,u)`<br>(`mergeable j` suffices) | [`ades_par_chaos`](../../angelic-designs/utp_ades_parallel_lift.thy#L247) |

The associativity laws transfer [`des_par_assoc`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L215)
and [`des_par_assoc_nd`](../../deps/UTP-Designs/utp_des_nd.thy#L100) to AD through
[`ades_lift_par_assoc_transfer`](../../angelic-designs/utp_ades_parallel_lift.thy#L291):
for `A`, `A2` operands, AD associativity follows from D associativity of their `ac2p` images.

Chaos is `true`, and Miracle is `A false = ¬ok`.

## ac2p/d2ac mapping laws

| Equality | Operand premises | Lemma |
| --- | --- | --- |
| `ac2p (P ∥AD[j] Q) =`<br>`ac2p P ∥D[j] ac2p Q` | `P, Q` both `A`, `A2` | [`ades_par_ac2p`](../../angelic-designs/utp_ades_parallel_lift.thy#L221) |
| `P ∥AD[j] Q =`<br>`d2ac (ac2p P ∥D[j] ac2p Q)` | `P, Q` both `A`, `A2` | [`ades_par_d2ac_ac2p`](../../angelic-designs/utp_ades_parallel_lift.thy#L208) |
| `d2ac D ∥AD[j] d2ac E =`<br>`d2ac (D ∥D[j] E)` | `D, E` both `H` | [`ades_par_d2ac`](../../angelic-designs/utp_ades_parallel_lift.thy#L214) |
| `D ∥D[j] E =`<br>`ac2p (d2ac D ∥AD[j] d2ac E)` | `D, E` both `H` | [`ades_par_ac2p_d2ac`](../../angelic-designs/utp_ades_parallel_lift.thy#L227) |
