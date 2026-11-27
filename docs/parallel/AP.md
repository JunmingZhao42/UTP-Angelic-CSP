# Angelic process parallel

[Parallel by merge](README.md) · [Generic](Generic.md) · [AD](AD.md) · [RAD](RAD.md)

Source files, in import order:

- [`utp_ap_parallel_merge.thy`](../../angelic-processes/utp_ap_parallel_merge.thy)
- [`utp_ap_parallel_laws.thy`](../../angelic-processes/utp_ap_parallel_laws.thy)
- [`utp_ap_parallel_lifted_merge.thy`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy)
- [`utp_ap_parallel_operator.thy`](../../angelic-processes/utp_ap_parallel_operator.thy)
- [`utp_ap_parallel_algebra.thy`](../../angelic-processes/utp_ap_parallel_algebra.thy)

[Shared notation](README.md#shared-notation).

AP processes share the RAD alphabet. AP sequential composition is AD sequential
composition applied to AP processes, and the paper relates that composition to RAD through `RA1`
and `H1`. We define AP parallel the same way: a parallel by merge on AP processes,
related to RAD parallel by refinement, with equality for nondivergent operands.

- [Merge conditions](#merge-conditions)
- [The lifted merge](#the-lifted-merge)
- [Closure](#closure)
- [Monotonicity and choice](#monotonicity-and-choice)
- [Symmetry and associativity](#symmetry-and-associativity)
- [Zero laws](#zero-laws)
- [Relation to RAD](#relation-to-rad)
- [Angelic choice against a synchronising partner](#angelic-choice-against-a-synchronising-partner)
- [Not covered](#not-covered)
- [AP theories](#ap-theories)

## Merge conditions

AP reuses `H1m` and `H2m` from [D](D.md#merge-conditions),
`ADm` from [AD](AD.md#merge-conditions) and `RA2APm` from
[RAD](RAD.md#merge-conditions), and adds one condition for `RA3AP`:

```isabelle
RA3APm M ≡ II_AP ◁ wait ▷ M
```

- [`RA2APm`](../../reactive-angelic-designs/utp_rad_parallel_merge.thy#L41) normalises the trace, as `RA2` does for processes. RAD's `RA2m`
  also requires a trace extension in the output:
  `RA2m M = RA2APm M ∧ (∃v ∈ ac'. tr ≤ v.tr)`. AP drops that conjunct, since an AP
  process can diverge with no trace extension among its choices.
- [`RA3APm`](../../angelic-processes/utp_ap_parallel_merge.thy#L14) makes a waiting merge the AP skip, as `RA3AP P = II_AP ◁ wait ▷ P`.
- `RA3APm` is idempotent and monotone.

## The lifted merge

We complete the [RAD merge](RAD.md#the-lifted-merge) as the AD merge is
completed, and add the AP waiting condition:

```isabelle
merge_rad  ≡ ac'_lift_merge ∘ merge_rdes
merge_ap   ≡ RA3APm ∘ H3m ∘ H1m ∘ merge_rad
merge_ades ≡ H3m ∘ H1m ∘ ac'_lift_merge ∘ merge_des_raw

P ∥AP[j] Q ≡ P ∥[merge_ap j] Q
```

[`merge_ap_obs`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L22) unfolds `merge_ap j` at a started, non-waiting prior. Write
`obs(ok,s)` for an RD observation and `M` for `merge_rdes j`:

```isabelle
merge_ap j ((True,s),(okL,acL),(okR,acR),(ok',ac')) ↔
  acL ≠ {} ∧ acR ≠ {} ∧
  ((∀sL ∈ acL. ∀sR ∈ acR. ∃s' ∈ ac'. M(obs(True,s),obs(okL,sL),obs(okR,sR),obs(ok',s'))) ∨
   (∀sL ∈ acL. ∀sR ∈ acR. ∃s'. M(obs(True,s),obs(okL,sL),obs(okR,sR),obs(False,s'))))
```

- The second disjunct holds once a branch diverges and the branch states merge.
  Then any output is allowed, including `ac' = {}`, as in AD.
- With both branches terminating, the second disjunct is false and `merge_ap j` is
  the RAD lift ([`merge_ap_both_ok`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L40)).

## Closure

Each closure rule holds for any `M` that satisfies its merge premises. For every
`j`, `merge_ap j` satisfies each merge premise, which gives the closure law for
`∥AP[j]` with no A2 premise and no premise on `j`:

| `P ∥[M] Q` is | Operand premises | Merge premises | Lemma | `merge_ap j` | `P ∥AP[j] Q` |
| --- | --- | --- | --- | --- | --- |
| `RA2` | Both `RA2`, `PBMH_ades` | `RA2APm` | [`rad_par_by_merge_RA2`](../../reactive-angelic-designs/utp_rad_parallel_laws.thy#L53) | [`merge_ap_RA2APm`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L120) | - |
| `RA3AP` | Both `RA3AP` | `RA3APm` | [`ap_par_by_merge_RA3AP`](../../angelic-processes/utp_ap_parallel_laws.thy#L9) | [`merge_ap_RA3APm`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L157) | - |
| `AP` | Both `AP` | `H1m`, `H2m`, `ADm`, `RA2APm`, `RA3APm` | [`ap_par_by_merge_AP`](../../angelic-processes/utp_ap_parallel_laws.thy#L24) | [`merge_ap_H1m`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L70), [`merge_ap_H2m`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L86), [`merge_ap_ADm`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L100), [`merge_ap_RA2APm`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L120), [`merge_ap_RA3APm`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L157) | [`ap_par_AP`](../../angelic-processes/utp_ap_parallel_operator.thy#L21) |
| `A2` | Both `A2` | `A2m` | [`A2_par_by_merge`](../../angelic-designs/utp_ades_parallel_laws.thy#L81) | [`merge_ap_A2m`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L160) | [`ap_par_A2`](../../angelic-processes/utp_ap_parallel_operator.thy#L27) |

The `RA2` rule is RAD's. AP operands meet its `PBMH_ades` premise
([`AP_is_PBMH_ades`](../../angelic-processes/utp_ap_healthy.thy#L413)).

For `∥AP[j]`, parallel also preserves nondivergence:

| Result of `P ∥AP[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| `NDAP` | Both `AP`, `NDAP` | [`ap_par_NDAP`](../../angelic-processes/utp_ap_parallel_operator.thy#L32) |

RAD's `NDRAD` closure needs A2 operands; AP's `NDAP` closure does not.

## Monotonicity and choice

AP choices are disjunction and conjunction
([`AP_demonic_choice`](../../angelic-processes/utp_ap_ops.thy#L108),
[`AP_angelic_choice`](../../angelic-processes/utp_ap_ops.thy#L16)), so the generic `∨` and
`∧` [laws](Generic.md#parallel-operator) give the laws below for any `M`. The
last column gives each law for `∥AP[j]`. These `∥AP[j]` laws, and those of the
next two sections, are for AP operands.

| Property | Law for $P \parallel_M Q$ | Lemma | `P ∥AP[j] Q` |
| --- | --- | --- | --- |
| Monotonic | $P \sqsubseteq P' \land Q \sqsubseteq Q' \implies$<br>$P \parallel_M Q \sqsubseteq P' \parallel_M Q'$ | [`par_by_merge_mono`](../../deps/UTP/utp_concurrency.thy#L370) | [`ap_par_mono`](../../angelic-processes/utp_ap_parallel_algebra.thy#L9) |
| Distributes over `⊓AP` | $P \parallel_M (Q \sqcap_{AP} R) =$<br>$(P \parallel_M Q) \sqcap_{AP} (P \parallel_M R)$ | [`par_by_merge_disj_distl`](../../deps/UTP/utp_concurrency.thy#L332) | [`ap_par_demonic_distl`](../../angelic-processes/utp_ap_parallel_algebra.thy#L25) |
| Distributes over `⊓AP` | $(P \sqcap_{AP} Q) \parallel_M R =$<br>$(P \parallel_M R) \sqcap_{AP} (Q \parallel_M R)$ | [`par_by_merge_disj_distr`](../../deps/UTP/utp_concurrency.thy#L337) | [`ap_par_demonic_distr`](../../angelic-processes/utp_ap_parallel_algebra.thy#L30) |
| Subdistributes over `⊔AP` | $(P \parallel_M Q) \sqcup_{AP} (P \parallel_M R) \sqsubseteq$<br>$P \parallel_M (Q \sqcup_{AP} R)$ | [`par_by_merge_conj_subdistl`](../../deps/UTP/utp_concurrency.thy#L345) | [`ap_par_angelic_subdistl`](../../angelic-processes/utp_ap_parallel_algebra.thy#L35) |
| Subdistributes over `⊔AP` | $(P \parallel_M R) \sqcup_{AP} (Q \parallel_M R) \sqsubseteq$<br>$(P \sqcup_{AP} Q) \parallel_M R$ | [`par_by_merge_conj_subdistr`](../../deps/UTP/utp_concurrency.thy#L350) | [`ap_par_angelic_subdistr`](../../angelic-processes/utp_ap_parallel_algebra.thy#L40) |

For `∥AP[j]`, the right subdistribution becomes an equality for nondivergent
operands:

| Property | Law | Operand premises | Lemma |
| --- | --- | --- | --- |
| Distributes over `⊔AP` | $(P \parallel_{AP[j]} R) \sqcup_{AP} (Q \parallel_{AP[j]} R) =$<br>$(P \sqcup_{AP} Q) \parallel_{AP[j]} R$ | All `AP`, `NDAP`; `R` intersection-closed | [`ap_par_angelic_distr`](../../angelic-processes/utp_ap_parallel_algebra.thy#L48) |

Here `R` is intersection-closed as in the [RAD guide](RAD.md#monotonicity-and-choice).
The left-hand law follows from the right-hand one by commutativity when `j` is
`SymMerge`.

## Symmetry and associativity

For any `M`, the [generic laws](Generic.md#parallel-operator) give symmetry from
`SymMerge` ([`par_by_merge_comm`](../../deps/UTP/utp_concurrency.thy#L414)), and associativity from `SymMerge` and
`AssocMerge` ([`par_by_merge_assoc`](../../deps/UTP/utp_concurrency_assoc.thy#L30)) or, on nondivergent operands, from
`AssocMerge` of the guarded merge ([`par_by_merge_assoc_guard`](../../deps/UTP/utp_concurrency_assoc.thy#L75)). With premises
on `j`, the lifted merge has these properties:

| Property of `merge_ap j` | Premises on `j` | Lemma |
| --- | --- | --- |
| `SymMerge` | `SymMerge` | [`merge_ap_SymMerge`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L168) |
| `AssocMerge` | `Functional`, `mergeable`, `AssocMerge` | [`merge_ap_AssocMerge`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L191) |
| `AssocMerge` on nondivergent branches | `Functional`, `AssocMerge` | [`merge_ap_guard_AssocMerge`](../../angelic-processes/utp_ap_parallel_lifted_merge.thy#L345) |

So `∥AP[j]` is symmetric and associative:

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| $P \parallel_{AP[j]} Q = Q \parallel_{AP[j]} P$ | - | `SymMerge` | [`ap_par_comm`](../../angelic-processes/utp_ap_parallel_algebra.thy#L14) |
| $(P \parallel_{AP[j]} Q) \parallel_{AP[j]} R =$<br>$P \parallel_{AP[j]} (Q \parallel_{AP[j]} R)$ | - | `SymMerge`, `AssocMerge`, `mergeable`, `Functional` | [`ap_par_assoc_det`](../../angelic-processes/utp_ap_parallel_algebra.thy#L186) |
| $(P \parallel_{AP[j]} Q) \parallel_{AP[j]} R =$<br>$P \parallel_{AP[j]} (Q \parallel_{AP[j]} R)$ | All `NDAP` | `SymMerge`, `AssocMerge`, `Functional` | [`ap_par_assoc_det_nd`](../../angelic-processes/utp_ap_parallel_algebra.thy#L192) |

- Associativity for all operands matches AD's
  [`ades_par_assoc_det`](AD.md#symmetry-and-associativity).
- RAD has no such law: as in [RD](RD.md#symmetry-and-associativity), a divergent
  branch still constrains the output trace, and a deterministic total `j` is not
  enough.

## Zero laws

| Law | Operand premises | Premises on `j` | Lemma |
| --- | --- | --- | --- |
| $P \parallel_{AP[j]} \top_{AP} =$<br>$\top_{AP} \parallel_{AP[j]} P = \top_{AP}$ | `P is AP` | - | [`ap_par_miracle`](../../angelic-processes/utp_ap_parallel_algebra.thy#L97) |
| $P \parallel_{AP[j]} \mathit{Chaos}_{AP} =$<br>$\mathit{Chaos}_{AP} \parallel_{AP[j]} P = \mathit{Chaos}_{AP}$ | `P is AP`, with a singleton observation at the prior trace | merges empty traces | [`ap_par_chaos`](../../angelic-processes/utp_ap_parallel_algebra.thy#L117) |
| $P \parallel_{AP[j]} \mathit{ChaosCSP}_{AP} =$<br>$\mathit{ChaosCSP}_{AP} \parallel_{AP[j]} P = \mathit{Chaos}_{AP}$ | same | same | [`ap_par_chaos`](../../angelic-processes/utp_ap_parallel_algebra.thy#L117) |

- The Chaos premises correspond to those of RAD's `rad_par_chaos`, stated on AP
  observations: at every started, non-waiting prior `s`, `P` has an observation
  `P(True,s,c,{v})` with `v.tr = s.tr`, and `j` has a result, of any trace, for
  empty branch traces.
- The last row shows the cost of the AD completion. A divergent branch releases
  the output, so `ChaosCSP_AP`, which keeps its history in sequence, behaves like
  `Chaos_AP` in parallel.
- AP sequential composition does the same to a divergent first operand.

## Relation to RAD

As for sequential composition (paper Theorems 61 to 63), AP parallel is refined by
`H1` of RAD parallel on the `RA1` images, with equality for nondivergent operands:

| Law | Operand premises | Lemma |
| --- | --- | --- |
| `P ∥AP[j] Q ⊑ H1 (RA1 P ∥RAD[j] RA1 Q)` | Both `AP` | [`ap_par_rad_refine`](../../angelic-processes/utp_ap_parallel_operator.thy#L74) |
| `P ∥AP[j] Q = H1 (RA1 P ∥RAD[j] RA1 Q)` | Both `AP`, `NDAP` | [`ap_par_rad_NDAP`](../../angelic-processes/utp_ap_parallel_operator.thy#L117) |
| `RA1 (P ∥AP[j] Q) = RA1 P ∥RAD[j] RA1 Q` | Both `AP`, `NDAP` | [`ap_par_RA1`](../../angelic-processes/utp_ap_parallel_operator.thy#L184) |
| `ac2p (RA1 (P ∥AP[j] Q)) =`<br>`ac2p (RA1 P) ∥RD[j] ac2p (RA1 Q)` | Both `AP`, `NDAP`, `A2` | [`ap_par_ac2p`](../../angelic-processes/utp_ap_parallel_operator.thy#L191) |

- The right-hand side `H1 (RA1 P ∥RAD[j] RA1 Q)` was the previous AP parallel.
- That operator needed A2 operands for closure, and gave `Chaos_AP` and
  `ChaosCSP_AP` the same parallel results ([`Chaos_AP_same_RAD`](../../angelic-processes/utp_ap_ops.thy#L333)).
- On divergent operands only the refinement holds.

The round trips between AP and RD, through `F(P) = ac2p (RA1 P)` and
`G(D) = H1 (p2ac D)`:

| Operand premises | Round trip | Lemma |
| --- | --- | --- |
| `D is RD` | `F(G(D)) = D` | [`ap_RD_roundtrip`](../../angelic-processes/utp_ap_rad.thy#L285) |
| `P` is AP and A2 | `G(F(P)) = H1 (RA1 P)` | [`ap_RD_reverse_roundtrip`](../../angelic-processes/utp_ap_rad.thy#L294) |
| `P` is AP, A2 and NDAP | `G(F(P)) = P` | [`ap_RD_reverse_roundtrip_NDAP`](../../angelic-processes/utp_ap_nd.thy#L216) |

## Angelic choice against a synchronising partner

Prefixes and their choices are nondivergent, so on them AP parallel is `H1` of RAD
parallel on the `RA1` images, and `H1` leaves a started prior unchanged
([`ap_par_started`](../reviews/2026-11-20-ad-parallel-geometry/ap/AP_Probe.thy#L9)). So AP inherits the
[RAD behaviour](RAD.md#angelic-choice-against-a-synchronising-partner). With
`a ≠ b` ([`ap_sync_angelic_miracle`](../reviews/2026-11-20-ad-parallel-geometry/ap/AP_Probe.thy#L129)):

```isabelle
PrefixSkip_AP a ∥AP[jsync] (PrefixSkip_AP a ⊔AP PrefixSkip_AP b) = a →AP ⊤AP
```

The result differs from RAD's only at unstarted priors, where `H1` allows anything.

## Not covered

- Canonicity of `merge_ap` among AP merges, the counterpart of
  [`rad_par_canonical`](Canonicity.md#rad).
- The `p2ac` mapping law. By the `ChaosCSP_AP` row above, the law can hold only
  for nondivergent operands.
- Associativity for a partial `j` on divergent operands. AD fails there too
  ([AD guide](AD.md#symmetry-and-associativity)).

## AP theories

| File | Contents |
| --- | --- |
| [`utp_ap_healthy`](../../angelic-processes/utp_ap_healthy.thy) | AP healthiness, waiting laws, normal forms and component support. |
| [`utp_ap_rad`](../../angelic-processes/utp_ap_rad.thy) | H1/RA1 correspondence, closure and the Galois law. |
| [`utp_ap_ops`](../../angelic-processes/utp_ap_ops.thy) | Choice, Chaos, Stop and Skip, with transport laws. |
| [`utp_ap_seq`](../../angelic-processes/utp_ap_seq.thy) | Sequential composition calculations. |
| [`utp_ap_prefix`](../../angelic-processes/utp_ap_prefix.thy) | Prefixing calculations. |
| [`utp_ap_nd`](../../angelic-processes/utp_ap_nd.thy) | NDAP, non-divergent transport and closure. |
