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
  - [Parallel and sequential composition](#parallel-and-sequential-composition)
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
| `is A1` | Both `H1` | `A1m` | [`A1_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L447) |
| `is A` | Both `H1` | [`ADm`](../../angelic-designs/utp_ades_parallel_laws.thy#L88) | [`A_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L443) |
| `is A2` | Both `A2` | `A2m` | [`A2_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L453) |
| `is A3` | Both `H1` | `H1m`, `H3m` | [`A3_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L482) |
| `is PBMH_ades` | - | `PBMHm` | [`PBMH_ades_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L387) |

Commutativity and associativity for any `M` are the [generic laws](Generic.md).
Demonic choice `⊓AD` is disjunction and angelic choice `⊔AD` is conjunction, so the
generic [choice laws](Generic.md#parallel-operator) give, for any `M`:

| Law for `P ∥[M] Q` | Lemma |
| --- | --- |
| `P ∥[M] (Q ⊓AD R) =`<br>`(P ∥[M] Q) ⊓AD (P ∥[M] R)` | [`ades_par_by_merge_demonic_distl`](../../angelic-designs/utp_ades_parallel_laws.thy#L500) |
| `(P ⊓AD Q) ∥[M] R =`<br>`(P ∥[M] R) ⊓AD (Q ∥[M] R)` | [`ades_par_by_merge_demonic_distr`](../../angelic-designs/utp_ades_parallel_laws.thy#L506) |
| `(P ∥[M] Q) ⊔AD (P ∥[M] R) ⊑`<br>`P ∥[M] (Q ⊔AD R)` | [`ades_par_by_merge_angelic_subdistl`](../../angelic-designs/utp_ades_parallel_laws.thy#L512) |
| `(P ∥[M] R) ⊔AD (Q ∥[M] R) ⊑`<br>`(P ⊔AD Q) ∥[M] R` | [`ades_par_by_merge_angelic_subdistr`](../../angelic-designs/utp_ades_parallel_laws.thy#L518) |

### Correspondence with Designs

For a Design merge `M` and an AD merge `AM`, let:

```isabelle
AM = H3m (H1m (ABm (ac'_lift_merge M)))
```

| Equality | Operand premises | Premises on `M` | Lemma |
| --- | --- | --- | --- |
| `P ∥[AM] Q =`<br>`d2ac (ac2p P ∥[M] ac2p Q)` | Both `A`, `A2` | `HDm`, `H3m` | [`ades_par_by_merge_d2ac_ac2p`](../../angelic-designs/utp_ades_parallel_laws.thy#L659) |
| `ac2p (P ∥[AM] Q) =`<br>`ac2p P ∥[M] ac2p Q` | Both `A`, `A2` | `HDm`, `H3m` | [`ades_par_by_merge_ac2p`](../../angelic-designs/utp_ades_parallel_laws.thy#L776) |

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
| `SymMerge` | `SymMerge` | [`merge_ades_SymMerge`](../../angelic-designs/utp_ades_parallel_lift.thy#L93) |
| `AssocMerge` | `Functional`, `mergeable`, `AssocMerge` | [`merge_ades_AssocMerge`](../../angelic-designs/utp_ades_parallel_lift.thy#L103) |
| `AssocMerge` on nondivergent branches | `Functional`, `AssocMerge` | [`merge_ades_guard_AssocMerge`](../../angelic-designs/utp_ades_parallel_lift.thy#L164) |

So `∥AD[j]` preserves AD healthiness:

| Result of `P ∥AD[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `A0` | - | [`ades_par_A0_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L306) |
| `A1` | Both `H1` | [`ades_par_A1_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L311) |
| `A` | Both `H1` | [`ades_par_A_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L317) |
| `A2` | Both `A2` | [`ades_par_A2_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L323) |
| `A3` | Both `H1` | [`ades_par_A3_closure`](../../angelic-designs/utp_ades_parallel_lift.thy#L329) |

Its algebraic laws:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| `P ∥AD[j] Q = A P ∥AD[j] A Q` | Both `H1`, `A2` | - | [`ades_par_normalise_A`](../../angelic-designs/utp_ades_parallel_lift.thy#L285) |
| monotone in both operands | - | - | [`ades_par_mono`](../../angelic-designs/utp_ades_parallel_lift.thy#L528) |
| `P ∥AD[j] (Q ⊓AD R) =`<br>`(P ∥AD[j] Q) ⊓AD (P ∥AD[j] R)` | - | - | [`ades_par_demonic_distl`](../../angelic-designs/utp_ades_parallel_lift.thy#L387) |
| `(P ⊓AD Q) ∥AD[j] R =`<br>`(P ∥AD[j] R) ⊓AD (Q ∥AD[j] R)` | - | - | [`ades_par_demonic_distr`](../../angelic-designs/utp_ades_parallel_lift.thy#L392) |
| `(P ∥AD[j] Q) ⊔AD (P ∥AD[j] R) ⊑`<br>`P ∥AD[j] (Q ⊔AD R)` | - | - | [`ades_par_angelic_subdistl`](../../angelic-designs/utp_ades_parallel_lift.thy#L397) |
| `(P ∥AD[j] R) ⊔AD (Q ∥AD[j] R) ⊑`<br>`(P ⊔AD Q) ∥AD[j] R` | - | - | [`ades_par_angelic_subdistr`](../../angelic-designs/utp_ades_parallel_lift.thy#L402) |
| `(P ∥AD[j] Q) ⊔AD (P' ∥AD[j] Q) =`<br>`(P ⊔AD P') ∥AD[j] Q` | `P`, `P'` both `A`; all `NDAD`; `Q` intersection-closed | - | [`ades_par_angelic_distr`](../../angelic-designs/utp_ades_parallel_lift.thy#L411) |
| `(Q ∥AD[j] P) ⊔AD (Q ∥AD[j] P') =`<br>`Q ∥AD[j] (P ⊔AD P')` | `P`, `P'` both `A`; all `NDAD`; `Q` intersection-closed | - | [`ades_par_angelic_distl`](../../angelic-designs/utp_ades_parallel_lift.thy#L469) |
| `P ∥AD[j] Q = Q ∥AD[j] P` | - | `SymMerge` | [`ades_par_comm`](../../angelic-designs/utp_ades_parallel_lift.thy#L574) |
| `(P ∥AD[j] Q) ∥AD[j] R =`<br>`P ∥AD[j] (Q ∥AD[j] R)` | All `H1`, `A2` | `SymMerge`, `AssocMerge`, `mergeable` | [`ades_par_assoc`](../../angelic-designs/utp_ades_parallel_lift.thy#L644) |
| `(P ∥AD[j] Q) ∥AD[j] R =`<br>`P ∥AD[j] (Q ∥AD[j] R)` | All `H1`, `A2`, `NDAD` | `SymMerge`, `AssocMerge` | [`ades_par_assoc_nd`](../../angelic-designs/utp_ades_parallel_lift.thy#L661) |
| `(P ∥AD[j] Q) ∥AD[j] R =`<br>`P ∥AD[j] (Q ∥AD[j] R)` | - | `SymMerge`, `AssocMerge`, `mergeable`, `Functional` | [`ades_par_assoc_det`](../../angelic-designs/utp_ades_parallel_lift.thy#L687) |
| `(P ∥AD[j] Q) ∥AD[j] R =`<br>`P ∥AD[j] (Q ∥AD[j] R)` | All `NDAD` | `SymMerge`, `AssocMerge`, `Functional` | [`ades_par_assoc_det_nd`](../../angelic-designs/utp_ades_parallel_lift.thy#L698) |
| `P ∥AD[j] Miracle =`<br>`Miracle ∥AD[j] P = Miracle` | `P is H1` | - | [`ades_par_miracle`](../../angelic-designs/utp_ades_parallel_lift.thy#L559) |
| `Chaos ∥AD[j] Chaos = Chaos` | - | `∀s. ∃sL sR u. j(s,sL,sR,u)`<br>(`mergeable j` suffices) | [`ades_par_chaos`](../../angelic-designs/utp_ades_parallel_lift.thy#L540) |

The associativity laws transfer [`des_par_assoc`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L215)
and [`des_par_assoc_nd`](../../deps/UTP-Designs/utp_des_nd.thy#L100) to AD through
[`ades_lift_par_assoc_transfer`](../../angelic-designs/utp_ades_parallel_lift.thy#L584):
for `A`, `A2` operands, AD associativity follows from D associativity of their `ac2p` images.
These two laws only cover operands without angelic choice.

[`ades_par_assoc_det`](../../angelic-designs/utp_ades_parallel_lift.thy#L687) needs no
operand premise. As in D, it follows from
[`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30) once the lifted merge is
associative ([`merge_ades_AssocMerge`](../../angelic-designs/utp_ades_parallel_lift.thy#L103)).
A mergeable, `Functional` (deterministic) `j` is a function `f`, so both merge orders
offer `ac'` when `f(f(sP,sQ),sR) = f(sP,f(sQ,sR))` lies in `ac'` for every triple of
offered states. With a nondeterministic `j`, associativity can fail as soon as one
operand has angelic choice: on states `{0,1}`, with `j(sL,sR) = {sL ∨ sR}` except
`j(1,1) = {0,1}`, the two bracketings of `⟨1⟩ ∥ ⟨1⟩ ∥ (⟨0⟩ ⊔ ⟨1⟩)` are `⟨1⟩` and
`⟨0⟩ ⊓ ⟨1⟩`. With a partial `j`, it can fail once an operand diverges: on states
`{0,1}`, with `j(0,0) = j(0,1) = {}` and `j(1,1) = {0}`, take `P = Q = ⟨1⟩` and an `R`
that offers 1 but may diverge.

For nondivergent operands, [`ades_par_assoc_det_nd`](../../angelic-designs/utp_ades_parallel_lift.thy#L698) drops `mergeable`.
As D does, it guards the merge to nondivergent branches
([`merge_ades_guard_AssocMerge`](../../angelic-designs/utp_ades_parallel_lift.thy#L164)) and applies
[`par_by_merge_assoc_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L75).

The angelic laws can be strict. With `j` the exclusive or on states `{0,1}` and
`P = ⟨0⟩ ⊓ ⟨1⟩`, both `P ∥AD[j] ⟨0⟩` and `P ∥AD[j] ⟨1⟩` are `⟨0⟩ ⊓ ⟨1⟩`, so their
angelic choice allows `ac' = {0}`. But `P ∥AD[j] (⟨0⟩ ⊔ ⟨1⟩)` is `⟨0⟩ ⊔ ⟨1⟩`: whichever
state `P` ends with is merged with both 0 and 1, so only `{0,1}` is allowed. On the
left, the two parallels resolve `P`'s demonic choice separately.

[`ades_par_angelic_distr`](../../angelic-designs/utp_ades_parallel_lift.thy#L411) and
[`ades_par_angelic_distl`](../../angelic-designs/utp_ades_parallel_lift.thy#L469) give equality when the shared operand `Q` has no
demonic choice, written as its offered sets being closed under intersection, and no operand
diverges. Then the two witnesses on the left combine into one: the union of the two sets
offered by `P` and `P'`, and the intersection of the two sets offered by `Q`. Divergence
breaks this: if `P` may diverge offering `{1}` or terminate offering `{1}`, and
`P' = Q = ⟨0⟩` with exclusive or, the left side is `⟨0⟩` but the right side is
`⟨0⟩ ⊔ ⟨1⟩`.

Chaos is `true`, and Miracle is `A false = ¬ok`.

## Parallel and sequential composition

Parallel refines both sequential orders when the branches use separate parts of the
state: `P` ignores a variable `a`, `Q` uses only `a`, and `j` takes `a` from `Q` and
the rest from `P`. Then `P ;;AD Q ⊑ P ∥AD[j] Q` and `Q ;;AD P ⊑ P ∥AD[j] Q`. If `P` has
no angelic choice, `P ∥AD[j] Q = P ;;AD Q`; if `P` has no demonic choice,
`P ∥AD[j] Q = Q ;;AD P`.

Both branches start from the prior state, and `ac'` must merge every state `P` offers
with every state `Q` offers. In `P ;;AD Q`, `Q` starts from each state of `P`'s set and
may offer a different set from each. The parallel is the case where `Q` offers the same
set every time, so every `ac'` the parallel offers, the sequence offers too. This is not
the interleaving picture, in which parallel is a demonic choice of orders and a fixed
order refines it: here there is no schedule.

For example, let the state be two Booleans `(b, a)`. `P` sets `b` demonically: it offers
`{(β, a)}` for either `β`. `Q` sets `a` angelically: it offers `{(b, F), (b, T)}`. The
parallel offers `{(β, F), (β, T)}`, which always holds a state with `a = b`, so
`P ∥AD[j] Q` guarantees `a = b`. `Q ;;AD P` also offers `{(T, F), (F, T)}`: from each of
`Q`'s two states, `P` may pick the other value.

Without separate parts the comparison fails: with `j` keeping the left state,
`⟨1⟩ ∥AD[j] ⟨2⟩ = ⟨1⟩` but `⟨1⟩ ;;AD ⟨2⟩ = ⟨2⟩`. These laws hold for one merge and need
independence premises, so they are not in production. The
[geometry review](../reviews/2026-11-20-ad-parallel-geometry/README.md) proves them for the
AD operators in [`AD_Seq_Par`](../reviews/2026-11-20-ad-parallel-geometry/ad/AD_Seq_Par.thy),
with the one-way exchange law `(P ∥ Q) ;; (P' ∥ Q') ⊑ (P ;; P') ∥ (Q ;; Q')`.

## Shared choice-set canonicity

These results concern the shared choice-set alphabet, not AD healthiness.
[RAD](RAD.md#canonicity) specialises the same lift, and
[AP](AP.md#canonicity-through-rad) transports its refinement consequence.
Write `L(N) = ABm (ac'_lift_merge N)` for an ordinary merge `N`.

[`singleton_refines`](../../angelic-designs/utp_ades_parallel_laws.thy#L579)
requires every accepted singleton branch pair to have an `N` witness in `ac'`,
for every prior, all control flags and every output set.

| Result | Premises | Lemma |
| --- | --- | --- |
| On singleton branches, `L(N)` accepts iff `N` has a witness in `ac'` | None | [`choice_lift_singleton`](../../angelic-designs/utp_ades_parallel_laws.thy#L589) |
| `L(N) ⊑ M` iff `singleton_refines N M` | `M is ABm` | [`choice_lift_refine_iff`](../../angelic-designs/utp_ades_parallel_laws.thy#L623) |
| `P ∥[L(N)] Q ⊑ P ∥[M] Q` | `M is ABm`, `singleton_refines N M` | [`par_choice_lift_canonical`](../../angelic-designs/utp_ades_parallel_laws.thy#L638) |
| `P ∥AD[j] Q ⊑ P ∥[H3m (H1m M)] Q` | `M is ABm`, `singleton_refines (merge_des j) M` | [`ades_par_canonical`](../../angelic-designs/utp_ades_parallel_lift.thy#L367) |

So among ABm merges `M` with `singleton_refines N M`, `L(N)` is the least in the
refinement order. No A2 premise is needed.
The last row accounts for AD's additional `H1m` and `H3m` completion.

## ac2p/d2ac mapping laws

| Equality | Operand premises | Lemma |
| --- | --- | --- |
| `ac2p (P ∥AD[j] Q) =`<br>`ac2p P ∥D[j] ac2p Q` | `P, Q` both `A`, `A2` | [`ades_par_ac2p`](../../angelic-designs/utp_ades_parallel_lift.thy#L353) |
| `P ∥AD[j] Q =`<br>`d2ac (ac2p P ∥D[j] ac2p Q)` | `P, Q` both `A`, `A2` | [`ades_par_d2ac_ac2p`](../../angelic-designs/utp_ades_parallel_lift.thy#L340) |
| `d2ac D ∥AD[j] d2ac E =`<br>`d2ac (D ∥D[j] E)` | `D, E` both `H` | [`ades_par_d2ac`](../../angelic-designs/utp_ades_parallel_lift.thy#L346) |
| `D ∥D[j] E =`<br>`ac2p (d2ac D ∥AD[j] d2ac E)` | `D, E` both `H` | [`ades_par_ac2p_d2ac`](../../angelic-designs/utp_ades_parallel_lift.thy#L359) |
