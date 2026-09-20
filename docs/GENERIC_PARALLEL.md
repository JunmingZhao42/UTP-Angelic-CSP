# Generic parallel for AD, RAD, and AP

The generic operators on `research/generic-parallel-merges` follow the
reactive-design construction pattern: restrict the supplied merge, then
apply merge healthiness. They are research extensions to the paper development.

## Operator and alphabet

A supplied merge `M(x,p,q,o)` relates the initial observation `x`, both branch
observations `p` and `q`, and the final observation `o`. The initial observation
contains `ok` and state; each result contains `ok` and an angelic choice set.
For RAD/AP, choice-set members carry trace, refusal, and waiting observations.

[OkM](../angelic-designs/utp_ades_parallel_generic.thy#L445) restricts the seed:

\[
  M_0 = M \land (ok' = ok_{\mathrm{left}} \land ok_{\mathrm{right}}).
\]

The layer's merge healthiness operator then produces
\(M_{\mathrm{healthy}} = \mathcal H_M(M_0)\). Parallel uses that completed merge:

\[
  (P\parallel_M Q)(x,o)
  \iff \exists p,q.\ P(x,p)\land Q(x,q)\land M_{\mathrm{healthy}}(x,p,q,o).
\]

| Operator | Completed merge | Both operands → result |
| --- | --- | --- |
| [ades_par_full](../angelic-designs/utp_ades_parallel_generic.thy#L566) | [ADOKM](../angelic-designs/utp_ades_parallel_generic.thy#L498) = ADM ∘ OkM | [ades_par_full_A_closure](../angelic-designs/utp_ades_parallel_generic.thy#L634) (`H1 → A`) |
| [rad_par_full](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L677) | [RADOKM](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L634) = RADM_full ∘ OkM | [rad_par_full_RAD_closure](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L834) (`RAD → RAD`) |
| [ap_par_full](../angelic-processes/utp_ap_parallel_generic.thy#L373) | [APOKM](../angelic-processes/utp_ap_parallel_generic.thy#L296) = APM ∘ OkM | [ap_par_full_AP_closure](../angelic-processes/utp_ap_parallel_generic.thy#L533) (`AP → AP`) |

The supplied merge is arbitrary. It specifies the choice-set relation and may
contain further control dependencies. `OkM` imposes no equation on choice sets;
healthiness completion may transform the choices and control observations.

**The conjunction is a seed restriction.** It need not hold globally after
completion. The [ADOKM_obs](../angelic-designs/utp_ades_parallel_generic.thy#L501) formula shows that a permitted failure for an
unsuccessful branch pair permits either final `ok` value. The reactive
transformations additionally supply startup and waiting behaviour.

This follows the architecture of the library's
[N1](../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L123),
[NR](../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L126), and
[MR](../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L132).
An exact correspondence with reactive-design parallel, general CSP divergence,
and synchronisation laws have not been proved.

## Healthiness framework

| Completed transformation | Idempotence | Monotonicity |
| --- | --- | --- |
| `ADOKM` | [ADOKM_Idempotent](../angelic-designs/utp_ades_parallel_generic.thy#L537) | [ADOKM_Monotonic](../angelic-designs/utp_ades_parallel_generic.thy#L543) |
| `RADOKM` | [RADOKM_Idempotent](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L656) | [RADOKM_Monotonic](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L642) |
| `APOKM` | [APOKM_Idempotent](../angelic-processes/utp_ap_parallel_generic.thy#L352) | [APOKM_Monotonic](../angelic-processes/utp_ap_parallel_generic.thy#L304) |

Repeating completion at the operator interface changes nothing, by
[ades_par_full_normalise](../angelic-designs/utp_ades_parallel_generic.thy#L641), [rad_par_full_normalise](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L858), and [ap_par_full_normalise](../angelic-processes/utp_ap_parallel_generic.thy#L550).

The supporting merge transformations are:

| Layer | Transformation after `OkM` | Meaning |
| --- | --- | --- |
| AD | [ADM](../angelic-designs/utp_ades_parallel_generic.thy#L362) = merge_health A | Each fixed branch slice is an angelic design. |
| RAD | [RADM_full](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L409) = RA3M ∘ RA2M ∘ RA1M ∘ CSPA1M ∘ H2M ∘ PBMHM | Reactive trace, waiting, startup, and design healthiness. |
| AP | [APM](../angelic-processes/utp_ap_parallel_generic.thy#L152) = RA3APM ∘ RA2M ∘ ADM | Design healthiness, trace normalisation, and AP waiting behaviour. |

[RA2M](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L102) normalises the prior trace and all three result choice sets together.
[RA3M](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L149) supplies `II_Rac` when the prior is waiting; [RA3APM](../angelic-processes/utp_ap_parallel_generic.thy#L20) supplies `II_AP`.
On nonwaiting inputs, the merge can still depend on both branch observations.
Branch waiting-state composition is a policy of the supplied merge.

The stronger AD construction [ANOKM](../angelic-designs/utp_ades_parallel_normal.thy#L367) = A3M ∘ OkM is also monotone and
idempotent. [ades_par_full_ANOKM_closure](../angelic-designs/utp_ades_parallel_normal.thy#L461) proves A, A2, and A3 closure for the public operator with an `ANOKM` seed and H1-healthy operands. The public
RAD/AP closure theorems do not additionally assert A2 or A3.
These are sufficient constructions; no weakestness claim is made.

## Parallel laws

All three public operators are monotone in the operands and supplied merge.
A symmetric seed gives commutative parallel. Associativity requires
[MergeAssoc](../angelic-designs/utp_ades_parallel_generic.thy#L28) of the completed merge, not merely of the seed.

| Law | AD | RAD | AP |
| --- | --- | --- | --- |
| Monotonicity | [ades_par_full_mono](../angelic-designs/utp_ades_parallel_generic.thy#L645) | [rad_par_full_mono](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L862) | [ap_par_full_mono](../angelic-processes/utp_ap_parallel_generic.thy#L554) |
| Commutativity, assuming `MergeSym M` | [ades_par_full_comm](../angelic-designs/utp_ades_parallel_generic.thy#L651) | [rad_par_full_comm](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L868) | [ap_par_full_comm](../angelic-processes/utp_ap_parallel_generic.thy#L560) |
| Associativity, assuming `MergeAssoc` of the completed merge | [ades_par_full_assoc](../angelic-designs/utp_ades_parallel_generic.thy#L676) | [rad_par_full_assoc](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L893) | [ap_par_full_assoc](../angelic-processes/utp_ap_parallel_generic.thy#L585) |
| Distribution over disjunction in the left operand | [ades_par_full_disj_left](../angelic-designs/utp_ades_parallel_generic.thy#L719) | [rad_par_full_disj_left](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L936) | [ap_par_full_disj_left](../angelic-processes/utp_ap_parallel_generic.thy#L628) |
| Distribution over disjunction in the right operand | [ades_par_full_disj_right](../angelic-designs/utp_ades_parallel_generic.thy#L723) | [rad_par_full_disj_right](../reactive-angelic-designs/utp_rad_parallel_generic.thy#L940) | [ap_par_full_disj_right](../angelic-processes/utp_ap_parallel_generic.thy#L632) |

The `*_comm_iff` and `*_assoc_iff` companion lemmas characterise these laws
for arbitrary operands using the completed merge. No general preservation
of associativity by completion is established. Literal `false` operands
annihilate parallel; literal `false` need not belong to the healthy layer.

The completed AD operator can fail associativity even with a healthy symmetric
merge: [ADOKM_ades_nand_merge](../angelic-designs/utp_ades_parallel_normal.thy#L272) shows that completion retains the NAND merge,
and [ades_nand_parallel_not_assoc](../angelic-designs/utp_ades_parallel_normal.thy#L345) proves the operator counterexample.

## Trace-agreement example

[basic_merge_state](../reactive-angelic-designs/utp_rad_parallel_examples.thy#L26) requires the branch and final traces to agree and extend
the prior trace, and sets the final state's waiting flag to the disjunction
of the branch states' waiting flags. Refusals are unconstrained.

[basic_merge_seed](../reactive-angelic-designs/utp_rad_parallel_examples.thy#L36) requires successful branch and final observations, exact
singleton branch choice sets `{l}` and `{r}`, and a final choice set containing
some state permitted by `basic_merge_state`. It describes singleton
synchronisation, not arbitrary multistate angelic choice or general divergence.

Passing this seed to the public operators yields the completed basic merges,
by [RADOKM_basic_merge_seed](../reactive-angelic-designs/utp_rad_parallel_examples.thy#L126) and [APOKM_basic_merge_seed](../angelic-processes/utp_ap_parallel_examples.thy#L23).
At a started, nonwaiting input with empty trace, and a nonwaiting singleton
final state `z`, two event prefixes complete together exactly when
`ok' ∧ a = b ∧ z.tr = [a]`. These are proved for the public operators by
[rad_par_full_basic_prefixes_complete](../reactive-angelic-designs/utp_rad_parallel_examples.thy#L496) and [ap_par_full_basic_prefixes_complete](../angelic-processes/utp_ap_parallel_examples.thy#L208).
The completed examples also supply the respective startup and waiting cases.

## Sources

* [AD merge healthiness and parallel](../angelic-designs/utp_ades_parallel_generic.thy)
* [Stronger AD normalisation](../angelic-designs/utp_ades_parallel_normal.thy)
* [RAD merge healthiness and parallel](../reactive-angelic-designs/utp_rad_parallel_generic.thy)
* [AP merge healthiness and parallel](../angelic-processes/utp_ap_parallel_generic.thy)
* [RAD examples](../reactive-angelic-designs/utp_rad_parallel_examples.thy)
* [AP examples](../angelic-processes/utp_ap_parallel_examples.thy)
