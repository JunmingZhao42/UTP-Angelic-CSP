# Angelic design parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [D](D.md) · [RAD](RAD.md)

Source files, in import order:

- [`utp_ades_parallel_merge.thy`](../../angelic-designs/utp_ades_parallel_merge.thy)
- [`utp_ades_parallel_laws.thy`](../../angelic-designs/utp_ades_parallel_laws.thy)
- [`utp_ades_parallel_choice_lift.thy`](../../angelic-designs/utp_ades_parallel_choice_lift.thy)
- [`utp_ades_parallel_lifted_merge.thy`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy)
- [`utp_ades_parallel_operator.thy`](../../angelic-designs/utp_ades_parallel_operator.thy)
- [`utp_ades_parallel_algebra.thy`](../../angelic-designs/utp_ades_parallel_algebra.thy)

[Shared notation](README.md#shared-notation).

AD branches and outputs carry choice sets `acL, acR, ac'` instead of single
states. We lift a state merge `j` through choice sets to obtain `P ∥AD[j] Q`,
and give each law for any AD merge `M`, with its instance for `∥AD[j]`.
[Canonicity](Canonicity.md) compares this lift with other merges on choice sets.

- [Angelic design parallel](#angelic-design-parallel)
  - [Merge conditions](#merge-conditions)
  - [The lifted merge](#the-lifted-merge)
  - [Closure](#closure)
  - [Monotonicity and choice](#monotonicity-and-choice)
  - [Symmetry and associativity](#symmetry-and-associativity)
  - [Zero and unit laws](#zero-and-unit-laws)
  - [Correspondence with Designs](#correspondence-with-designs)

## Merge conditions

AD merges reuse the [design merge conditions](D.md#merge-conditions)
`H1m`, `H2m`, `H3m` and `HDm` unchanged, since these allow the branch and output
alphabets to differ from the prior. AD adds a merge condition for each AD
healthiness condition, with `m` the merge input `((ok,s),(okL,acL),(okR,acR))`:

```isabelle
A0m M ≡ M ∧ (ok ∧ ac' = {} ⟶ M[false/ok'])
A1m   ≡ HDm ∘ PBMH_ades
ADm   ≡ A0m ∘ A1m
A2m M ≡ (((∃sL. acL = {sL}) ∧ (∃sR. acR = {sR})) ∨ M) ∧
  (∀sL sR. (acL = {} ∨ sL ∈ acL) ∧ (acR = {} ∨ sR ∈ acR) ⟶
    (A2 M)[{sL},{sR}/acL,acR])
PBMHm M ≡ PBMH_ades (M ∧ ac' ≠ {})
```

- `A2m` is the merge condition for A2 closure. An A2 operand's choice sets are
  decided by the empty set and the singletons
  ([`A2_obs`](../../angelic-designs/utp_ades_a2.thy#L151)):
  ```isabelle
  P ⟷ P[{}/ac'] ∨ (∃a ∈ ac'. P[{a}/ac'])
  ```

- `M is A2m` when:
  - on singleton branches, the output is A2:
  `M({a},{b},Z) ⟷ M({a},{b},{}) ∨ (∃z ∈ Z. M({a},{b},{z}))`;
  - larger branches reduce to singletons: `M(X,Y,Z) ⟹ M({a},{b},Z)` for all `a ∈ X`
  and `b ∈ Y`, with any `a` when `X = {}` and any `b` when `Y = {}`.

The AD merge conditions `A0m`, `A1m`, `ADm`, `A2m` and `PBMHm` are idempotent and
monotone. The proved commutation laws with D's merge conditions are:

| Condition | Commutes with |
| --- | --- |
| `H1m` | `A0m`, `A1m`, `A2m` |
| `H2m` | `A0m`, `A1m`, `PBMHm` |
| `H3m`, `HDm` | `A0m`, `A1m` |

`A0m`, `A1m` and `A2m` do not commute pairwise in general, and `A2m` does not
commute with `H2m`, `H3m` or `HDm`.

## The lifted merge

We lift a design merge `M` through choice sets with
[`ac'_lift_merge`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L17): both
branch sets must be nonempty, and every pair of branch states from `acL` and `acR`
must have a merged state in `ac'`:

```isabelle
ac'_lift_merge M ((ok,s),(okL,acL),(okR,acR),(ok',ac')) =
  acL ≠ {} ∧ acR ≠ {} ∧
  (∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'. M((ok,s),(okL,sL),(okR,sR),(ok',s')))
```

The lifted merge applies this lift to the raw design merge
[`merge_des_raw`](D.md#the-lifted-merge) of `j`, then applies `H1m` and `H3m`:

```isabelle
merge_ades ≡ H3m ∘ H1m ∘ ac'_lift_merge ∘ merge_des_raw

P ∥AD[j] Q ≡ P ∥[merge_ades j] Q
```

[`merge_ades_obs`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L25) unfolds `merge_ades j`. After start:

- the branch sets are nonempty, and every pair of branch states can merge;
- if both branches terminate, so does the output, with a witness in `ac'`.

```isabelle
merge_ades j ((ok,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  ¬ok ∨ (acL ≠ {} ∧ acR ≠ {} ∧ (∀sL ∈ acL. ∀sR ∈ acR. ∃u. j(s,sL,sR,u)) ∧
         (okL ∧ okR ⟶ ok' ∧ (∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'. j(s,sL,sR,s'))))
```

## Closure

Each closure rule holds for any `M` that satisfies its merge premises. For every
`j`, `merge_ades j` satisfies each merge premise, which gives the closure law for
`∥AD[j]`:

| `P ∥[M] Q` is | Operand premises | Merge premises | Lemma | `merge_ades j` | `P ∥AD[j] Q` |
| --- | --- | --- | --- | --- | --- |
| `A0` | - | `A0m` | [`A0_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L24) | [`merge_ades_is_A0m`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L73) | [`ades_par_A0_closure`](../../angelic-designs/utp_ades_parallel_operator.thy#L67) |
| `A1` | Both `H1` | `A1m` | [`A1_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L36) | [`merge_ades_is_A1m`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L78) | [`ades_par_A1_closure`](../../angelic-designs/utp_ades_parallel_operator.thy#L72) |
| `A` | Both `H1` | [`ADm`](../../angelic-designs/utp_ades_parallel_merge.thy#L88) | [`A_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L71) | [`merge_ades_is_ADm`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L83) | [`ades_par_A_closure`](../../angelic-designs/utp_ades_parallel_operator.thy#L78) |
| `A2` | Both `A2` | `A2m` | [`A2_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L81) | [`merge_ades_is_A2m`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L86) | [`ades_par_A2_closure`](../../angelic-designs/utp_ades_parallel_operator.thy#L84) |
| `A3` | Both `H1` | `H1m`, `H3m` | [`A3_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L110) | [`merge_ades_is_H1m`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L61), [`merge_ades_is_H3m`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L70) | [`ades_par_A3_closure`](../../angelic-designs/utp_ades_parallel_operator.thy#L90) |
| `PBMH_ades` | - | `PBMHm` | [`PBMH_ades_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L15) | - | - |

`merge_ades j` is also `H2m` and `HDm` ([`merge_ades_is_H2m`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L64),
[`merge_ades_is_HDm`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L67)). On `H1`, `A2` operands, parallel depends only on the `A`
images: `P ∥AD[j] Q = A P ∥AD[j] A Q` ([`ades_par_normalise_A`](../../angelic-designs/utp_ades_parallel_operator.thy#L46)).

## Monotonicity and choice

Demonic choice `⊓AD` is disjunction and angelic choice `⊔AD` is conjunction, so the
[generic laws](Generic.md#parallel-operator) give the laws below for any `M`. The
last column gives each law for `∥AD[j]`. These `∥AD[j]` laws, and those of the next
two sections, hold off A2, for operands with angelic choice, unless a row lists `A2`.

| Property | Law for $P \parallel_M Q$ | Lemma | `P ∥AD[j] Q` |
| --- | --- | --- | --- |
| Monotonic | $P \sqsubseteq P' \land Q \sqsubseteq Q' \implies$<br>$P \parallel_M Q \sqsubseteq P' \parallel_M Q'$ | [`par_by_merge_mono`](../../deps/UTP/utp_concurrency.thy#L370) | [`ades_par_mono`](../../angelic-designs/utp_ades_parallel_algebra.thy#L156) |
| Distributes over `⊓AD` | $P \parallel_M (Q \sqcap_{AD} R) =$<br>$(P \parallel_M Q) \sqcap_{AD} (P \parallel_M R)$ | [`ades_par_by_merge_demonic_distl`](../../angelic-designs/utp_ades_parallel_laws.thy#L128) | [`ades_par_demonic_distl`](../../angelic-designs/utp_ades_parallel_algebra.thy#L15) |
| Distributes over `⊓AD` | $(P \sqcap_{AD} Q) \parallel_M R =$<br>$(P \parallel_M R) \sqcap_{AD} (Q \parallel_M R)$ | [`ades_par_by_merge_demonic_distr`](../../angelic-designs/utp_ades_parallel_laws.thy#L134) | [`ades_par_demonic_distr`](../../angelic-designs/utp_ades_parallel_algebra.thy#L20) |
| Subdistributes over `⊔AD` | $(P \parallel_M Q) \sqcup_{AD} (P \parallel_M R) \sqsubseteq$<br>$P \parallel_M (Q \sqcup_{AD} R)$ | [`ades_par_by_merge_angelic_subdistl`](../../angelic-designs/utp_ades_parallel_laws.thy#L140) | [`ades_par_angelic_subdistl`](../../angelic-designs/utp_ades_parallel_algebra.thy#L25) |
| Subdistributes over `⊔AD` | $(P \parallel_M R) \sqcup_{AD} (Q \parallel_M R) \sqsubseteq$<br>$(P \sqcup_{AD} Q) \parallel_M R$ | [`ades_par_by_merge_angelic_subdistr`](../../angelic-designs/utp_ades_parallel_laws.thy#L146) | [`ades_par_angelic_subdistr`](../../angelic-designs/utp_ades_parallel_algebra.thy#L30) |

For `∥AD[j]`, the subdistributions become equalities under extra premises:

| Property | Law | Operand premises | Lemma |
| --- | --- | --- | --- |
| Distributes over `⊔AD` | $(P \parallel_{AD[j]} R) \sqcup_{AD} (Q \parallel_{AD[j]} R) =$<br>$(P \sqcup_{AD} Q) \parallel_{AD[j]} R$ | `P`, `Q` both `A`; all `NDAD`; `R` intersection-closed | [`ades_par_angelic_distr`](../../angelic-designs/utp_ades_parallel_algebra.thy#L39) |
| Distributes over `⊔AD` | $(P \parallel_{AD[j]} Q) \sqcup_{AD} (P \parallel_{AD[j]} R) =$<br>$P \parallel_{AD[j]} (Q \sqcup_{AD} R)$ | `Q`, `R` both `A`; all `NDAD`; `P` intersection-closed | [`ades_par_angelic_distl`](../../angelic-designs/utp_ades_parallel_algebra.thy#L97) |

The equalities need nondivergent operands (`NDAD`). On the left, `P` may diverge
in `P ∥AD[j] R`, which leaves that output unconstrained, so `Q ∥AD[j] R` alone
decides the left side. On the right, `P ⊔AD Q` diverges only when both `P` and `Q`
do, so the terminating offers of `P` still constrain the result.

## Symmetry and associativity

For any `M`, the [generic laws](Generic.md#parallel-operator) give symmetry from
`SymMerge` ([`par_by_merge_comm`](../../deps/UTP/utp_concurrency.thy#L414)), and
associativity from `SymMerge` and `AssocMerge`
([`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30)) or, on
nondivergent operands, from `AssocMerge` of the guarded merge
([`par_by_merge_assoc_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L75)). With
premises on `j`, the lifted merge has these properties.
[`Functional`](../../deps/UTP/utp_rel.thy#L264) means `j` is deterministic: for each prior state and pair of
branch states, `j` gives at most one merged state.

| Property of `merge_ades j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `SymMerge` | `SymMerge` | [`merge_ades_SymMerge`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L90) |
| `AssocMerge` | `Functional`, `mergeable`, `AssocMerge` | [`merge_ades_AssocMerge`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L100) |
| `AssocMerge` on nondivergent branches | `Functional`, `AssocMerge` | [`merge_ades_guard_AssocMerge`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L161) |

So `∥AD[j]` is symmetric and associative:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| $P \parallel_{AD[j]} Q = Q \parallel_{AD[j]} P$ | - | `SymMerge` | [`ades_par_comm`](../../angelic-designs/utp_ades_parallel_algebra.thy#L238) |
| $(P \parallel_{AD[j]} Q) \parallel_{AD[j]} R =$<br>$P \parallel_{AD[j]} (Q \parallel_{AD[j]} R)$ | - | `SymMerge`, `AssocMerge`, `mergeable`, `Functional` | [`ades_par_assoc_det`](../../angelic-designs/utp_ades_parallel_algebra.thy#L351) |
| $(P \parallel_{AD[j]} Q) \parallel_{AD[j]} R =$<br>$P \parallel_{AD[j]} (Q \parallel_{AD[j]} R)$ | All `NDAD` | `SymMerge`, `AssocMerge`, `Functional` | [`ades_par_assoc_det_nd`](../../angelic-designs/utp_ades_parallel_algebra.thy#L362) |
| $(P \parallel_{AD[j]} Q) \parallel_{AD[j]} R =$<br>$P \parallel_{AD[j]} (Q \parallel_{AD[j]} R)$ | All `H1`, `A2` | `SymMerge`, `AssocMerge`, `mergeable` | [`ades_par_assoc`](../../angelic-designs/utp_ades_parallel_algebra.thy#L308) |
| $(P \parallel_{AD[j]} Q) \parallel_{AD[j]} R =$<br>$P \parallel_{AD[j]} (Q \parallel_{AD[j]} R)$ | All `H1`, `A2`, `NDAD` | `SymMerge`, `AssocMerge` | [`ades_par_assoc_nd`](../../angelic-designs/utp_ades_parallel_algebra.thy#L325) |

On A2 operands, associativity needs no `Functional` premise, so `j` may be
nondeterministic. These laws, `ades_par_assoc` and `ades_par_assoc_nd`, transfer
from D through `ac2p` ([Correspondence with Designs](#correspondence-with-designs)).

## Zero and unit laws

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| $P \parallel_{AD[j]} \mathit{Miracle} =$<br>$\mathit{Miracle} \parallel_{AD[j]} P = \mathit{Miracle}$ | `P is H1` | - | [`ades_par_miracle`](../../angelic-designs/utp_ades_parallel_algebra.thy#L223) |
| $P \parallel_{AD[j]} \mathit{Chaos} =$<br>$\mathit{Chaos} \parallel_{AD[j]} P = \mathit{Chaos}$ | `P is A`, `H4` | `mergeable` | [`ades_par_chaos`](../../angelic-designs/utp_ades_parallel_algebra.thy#L191) |
| $\mathit{Chaos} \parallel_{AD[j]} \mathit{Chaos} = \mathit{Chaos}$ | - | `∀s. ∃sL sR u. j(s,sL,sR,u)`<br>(`mergeable j` suffices) | [`ades_par_chaos_chaos`](../../angelic-designs/utp_ades_parallel_algebra.thy#L168) |

## Correspondence with Designs

For a Design merge `M`, let `AM` be its AD lift:

```isabelle
AM = (H3m ∘ H1m ∘ ac'_lift_merge) M
```

For any Design merge `M` that is `HDm` and `H3m`:

| Equality | Operand premises | Lemma | `P ∥AD[j] Q` |
| --- | --- | --- | --- |
| `P ∥[AM] Q =`<br>`d2ac (ac2p P ∥[M] ac2p Q)` | Both `A`, `A2` | [`ades_par_by_merge_d2ac_ac2p`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L222) | [`ades_par_d2ac_ac2p`](../../angelic-designs/utp_ades_parallel_operator.thy#L101) |
| `ac2p (P ∥[AM] Q) =`<br>`ac2p P ∥[M] ac2p Q` | Both `A`, `A2` | [`ades_par_by_merge_ac2p`](../../angelic-designs/utp_ades_parallel_choice_lift.thy#L339) | [`ades_par_ac2p`](../../angelic-designs/utp_ades_parallel_operator.thy#L114) |

The last column takes `M = merge_des j`, since
`merge_ades j = H3m (H1m (ac'_lift_merge (merge_des j)))`
([`merge_ades_design_lift`](../../angelic-designs/utp_ades_parallel_lifted_merge.thy#L36)). For `H` operands, whose `d2ac` images are `A` and
`A2`, this gives:

| Equality | Operand premises | Lemma |
| --- | --- | --- |
| `d2ac D ∥AD[j] d2ac E =`<br>`d2ac (D ∥D[j] E)` | `D, E` both `H` | [`ades_par_d2ac`](../../angelic-designs/utp_ades_parallel_operator.thy#L122) |
| `D ∥D[j] E =`<br>`ac2p (d2ac D ∥AD[j] d2ac E)` | `D, E` both `H` | [`ades_par_ac2p_d2ac`](../../angelic-designs/utp_ades_parallel_operator.thy#L120) |

The A2 associativity laws in [Symmetry and associativity](#symmetry-and-associativity)
transfer [`des_par_assoc`](../../deps/UTP-Designs/utp_des_parallel_lift.thy#L215) and [`des_par_assoc_nd`](../../deps/UTP-Designs/utp_des_nd.thy#L100) through
[`ades_lift_par_assoc_transfer`](../../angelic-designs/utp_ades_parallel_algebra.thy#L248): for `A`, `A2` operands, AD associativity
follows from D associativity of their `ac2p` images.
