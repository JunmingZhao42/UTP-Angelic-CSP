# Generic merge predicates for AD, RAD, and AP

This research extends the state-merge interface with a merge relation on
complete observations. The earlier interface and its theorems remain available.
The checkpoint before this extension is `6d88f02` on `research/parallel`;
the extension is developed on `research/generic-parallel-merges`.

## Operator and alphabet

All three layers use the same relational operator:

\[
  (P\parallel_M Q)(x,o)
  \iff \exists p,q.\ P(x,p)\land Q(x,q)\land M(x,p,q,o).
\]

Here `x` contains the initial `ok` and state; `p`, `q`, and `o` each contain
an `ok` flag and an angelic choice set. In RAD and AP, each member of a
choice set is a reactive state containing trace, refusal, and waiting
observations. Thus the merge can inspect both complete branch results and
choose the complete final result.

The operator adds no equation combining branch termination or waiting flags.
The old AD parallel is exactly the instance
`ades_par_full P (merge_ades_up j) Q`, proved by `ades_par_state_as_full`.
Applying a new healthiness operator to that lifted merge can change its
semantics; it is a construction of a healthy merge, not an equivalence claim.

## Merge healthiness and closure

For fixed branch results, define `merge_slice M p q` to be the predicate
`M(x,p,q,o)` on initial and final observations. Then

\[
  \operatorname{merge\_health}(H)(M)(x,p,q,o)
  = H(\operatorname{merge\_slice}(M,p,q))(x,o).
\]

The generic lifting preserves idempotence and monotonicity. Its fixed points
are exactly the merges whose every branch slice is `H`-healthy. That fact
alone does not imply parallel closure: closure must also account for the
existential branch witnesses in the operator.

| Layer / result | Merge condition | Operand assumptions | Main closure lemma |
| --- | --- | --- | --- |
| AD: `A0` | `M is A0M` | None | `ades_par_full_A0_closure` |
| AD: `PBMH_ades` | `M is PBMHM` | None | `ades_par_full_PBMH_closure` |
| AD: `H2` | `M is H2M` | None | `ades_par_full_H2_closure` |
| AD: `H1` | `M is H1M` | Both `H1`-healthy | `ades_par_full_H1_closure` |
| AD: combined `A` | `M is ADM` | Both `H1`-healthy; `A`-healthy operands also suffice | `ades_par_full_A_closure` |
| Any alphabet: `A2` | `M is A2M` | None | `ades_par_full_A2_closure` |
| AD: `A3`, also `A` and `A2` | `M is A3M` | Both `H1`-healthy | `ades_par_full_A3_closure` and companion lemmas |
| RAD: combined `RAD` | `M is RADM_full` | Both `RAD`-healthy | `rad_par_full_RAD_closure` |
| AP: combined `AP` | `M is APM` | Both `AP`-healthy | `ap_par_full_AP_closure` |

Every named merge operator in the table has `*_idem`, `*_Idempotent`,
`*_mono`, and `*_Monotonic` lemmas. Image closure lemmas allow an arbitrary
seed merge to be repaired before use. `A1M` and the individual reactive merge
operators also have these algebraic laws.

## Weakest conditions for closure

Weakest is relative to an operand class `C` and a target healthiness `H`.
The exact closure property is

\[
  W_{H,C}(M) \iff
  \forall P,Q\in C.\ H(P\parallel_M Q)=P\parallel_M Q.
\]

A merge healthiness operator `K` gives the weakest condition precisely when
`K(M) = M` is equivalent to the universal closure property above.
Idempotence and monotonicity alone do not establish this equivalence.
Nor does a component characterisation
such as `ADM_components_iff`: that describes the fixed points of `ADM`,
not every merge satisfying universal parallel closure.

| Merge condition | Target | Permitted operands | Weakest for this closure? |
| --- | --- | --- | --- |
| `A0M` | `A0` | Arbitrary | Yes, by the slice argument below. |
| `PBMHM` | `PBMH_ades` | Arbitrary | Yes, by the slice argument. |
| `H2M` / `CSPA2M` | `H2` / `CSPA2` | Arbitrary | Yes; `CSPA2M_H2M` identifies these operators. |
| `A2M` | `A2` | Arbitrary | Yes, by the slice argument. |
| `RA1M` | `RA1` | Arbitrary reactive predicates | Yes, by the slice argument. |
| `H1M` | `H1` | Both `H1`-healthy | No. |
| `ADM` | `A` | Both `H1`-healthy | No. |
| `A3M` | `A3`, or `A`, `A2`, and `A3` together | Both `H1`-healthy | No. |
| `RA3M` / `RA3APM` | `RA3` / `RA3AP` | Both healthy for the respective target | No, as conditions on the whole merge predicate. |
| `RADM_full` | `RAD` | Both `RAD`-healthy | No, as a condition on the whole merge predicate. |
| `APM` | `AP` | Both `AP`-healthy | No, as a condition on the whole merge predicate. |

For arbitrary operands, fix any branch results `p0`, `q0` and choose
`P(x,p) = (p = p0)` and `Q(x,q) = (q = q0)`. Their parallel is exactly
`merge_slice M p0 q0`. Universal closure therefore forces every slice to
be healthy, which is precisely the corresponding lifted merge condition.
Together with the existing closure theorem, this proves necessity and
sufficiency mathematically. These necessity arguments have not yet been
added as Isabelle lemmas.

For the three AD rows marked **No**, consider

\[
  M(x,p,q,o)=\neg ok(x)\land p=o\land q=o.
\]

For every pair of `H1`-healthy operands, this merge produces exactly
`¬ok(x)`, an `A`-, `A2`-, and `A3`-healthy predicate. It fails `H1M`,
and therefore also `ADM` and `A3M`: an unstarted input does not make every
branch slice true. At such an input, the parallel only needs suitable
existential branch witnesses. Thus the counterexample also applies if the
operands are further restricted to `A`-healthy designs.

For the reactive rows marked **No**, start with a merge satisfying the
stated condition and delete its entries where the prior is started and
waiting but the left branch has `ok = False`. Healthy operands cannot
produce that branch observation, so their parallel is unchanged. However,
`RA3M` and `RA3APM` require the waiting slice to equal `II_Rac` and `II_AP`
respectively even at these unreachable branch pairs. The changed merge
violates that requirement, and consequently also violates the relevant
combined condition. These non-necessity arguments are mathematical
explanations, not additional Isabelle counterexample lemmas.

Minimality of the sufficient component conditions `RA2M` and `CSPA1M` has
not been established here. No separate parallel closure or minimality
claim is made for `A1M`. Finding the exact weakest closure property and
representing it by a monotonic, idempotent operator are separate questions.

## Combined conditions

| Operator | Definition / fixed-point components | Meaning |
| --- | --- | --- |
| `ADM` | `merge_health A`; fixed points satisfy `H1M`, `H2M`, `PBMHM`, and `A0M` | Each branch slice is an angelic design. |
| `A3M` | `merge_health AN2` | Each slice has an output-independent failure predicate and singleton-generated successful behaviour. |
| `RADM_full` | `RA3M ∘ RA2M ∘ RA1M ∘ CSPA1M ∘ H2M ∘ PBMHM`; fixed points satisfy all six components | Reactive trace, waiting, design, and choice-set requirements act on the merge. |
| `APM` | `RA3APM ∘ RA2M ∘ ADM`; fixed points satisfy all three components | Angelic-design slices with reactive trace normalisation and AP waiting behaviour. |

`RA2M` normalises the prior trace and **all three output choice sets** using
the same prior trace. It is not a slice lifting of `RA2`: normalising only
the final choices would leave the branch witnesses inconsistent. The proof
uses trace prepending to recover witnesses from normalised choices.

`RA3M` supplies `II_Rac` when the prior is waiting; `RA3APM` supplies `II_AP`
there. These clauses disregard the branch results on that waiting input.
On nonwaiting inputs, healthy merges can still depend on both branches.
Neither clause imposes a universal disjunction of the branch waiting flags.

`RADM_full` absorbs the reactive startup requirement into the merge, so
generic RAD parallel needs no outer `CSPA1` wrapper or separate state-merge
totality premise `A0j`. This differs from the older `rad_par` construction.

## A0, A2, and A3 qualifications

* `A0M` repairs the complete predicate's empty-choice/control-flag behaviour.
  It is not state-merge totality `A0j`, nor the earlier skip-adding `H0`.
  Consequently the obstruction to representing exactly all total state
  merges by a monotone retraction does not apply to this construction.
* `A2M` imposes the existing singleton-choice healthiness operator on each
  output slice. It does not require a functional state-level merge. Its
  alphabet-polymorphic closure theorem also applies to RAD/AP merges when
  they additionally satisfy `A2M`; `RADM_full` and `APM` alone do not promise
  `A2` closure.
* `A3M` is deliberately stronger than merely lifting `A3`. For a slice `R`,
  `AN2` reads failure from `R(True,s,False,{})` and success from
  `R(True,s,True,{z})`, producing
  `¬ok ∨ F(s) ∨ (ok' ∧ (∃z∈ac'. G(s,z)))`.
  This form is stable under the branch existential quantifiers. It gives
  `A`, `A2`, and `A3` together, but does not represent all `A3`-healthy slices
  and can change the failure semantics of the seed merge.
* Global AD `A3` implies design startup healthiness `H1`, which admits an
  unstarted observation with an empty final choice set. RAD's `RA1` rejects
  every empty final choice set. Thus global `A3` and `RAD` cannot both hold;
  this is independent of the parallel construction. It does not rule out
  `A3j` on a state merge or qualified properties of design components.

## Algebraic laws

AD, RAD, and AP use the same full parallel operator, so its algebraic laws
are proved once and given layer-specific names. These equalities do not
require healthy operands. The closure theorems supply layer membership
when the operand and merge healthiness assumptions also hold.

| Law | Merge assumption | AD / RAD / AP |
| --- | --- | --- |
| Monotonicity in both operands and the merge | None | `*_par_full_mono` |
| Commutativity | `MergeSym M` | `*_par_full_comm` |
| Associativity | `MergeAssoc M` | `*_par_full_assoc` |
| Distribution over disjunction (demonic choice), in either operand | None | `*_par_full_disj_left`, `*_par_full_disj_right` |
| `false` annihilates parallel in either operand | None | `*_par_full_false_left`, `*_par_full_false_right` |

Here `*` is `ades`, `rad`, or `ap`. The generic AD laws additionally cover
disjunction of merges and a `false` merge. The annihilator is the literal
`false` predicate, which need not belong to the chosen healthy layer.

`MergeSym` means

\[
  M(x,p,q,o) \iff M(x,q,p,o).
\]

It is equivalent to the existing swap equation `swap_m ;; M = M`.
`ADM`, `RADM_full`, and `APM` preserve symmetry: repairing a symmetric seed
therefore gives a healthy merge for a commutative parallel operator.

`MergeAssoc` means relational associativity at each fixed prior observation:

\[
  (\exists y.\ M(x,p,q,y)\land M(x,y,r,o))
  \iff
  (\exists y.\ M(x,q,r,y)\land M(x,p,y,o)).
\]

The same prior `x` is used throughout. This direct reassociation condition
works with the different input and output alphabets of angelic designs;
it does not require symmetry. It differs from the library's homogeneous,
rotation-based `AssocMerge`, used by the older state-merge interface.
`ades_par_full_comm_iff` and `ades_par_full_assoc_iff` prove that these
conditions are also **necessary** for their respective laws to hold for
all arbitrary operands. They do not assert necessity when operands are
restricted to a healthy layer.

**Associativity is not generic, even with a healthy symmetric AD merge.**
`ades_nand_merge` satisfies `A3M`, `ADM`, `A2M`, and `MergeSym`. Its healthy
Boolean operands satisfy
`ades_bool_choice a parallel ades_bool_choice b = ades_bool_choice (a NAND b)`.
Yet `(True NAND True) NAND False = True`, while
`True NAND (True NAND False) = False`. The explicit parallel inequality is
proved by `ades_nand_parallel_not_assoc`.

The generic RAD/AP associativity lemmas retain the `MergeAssoc` premise.
No general preservation law is claimed for the combined `RADM_full` and
`APM` repairs. The basic examples below prove preservation through `RA2M`,
`RA3M`, and `RA3APM`, then handle their particular startup clauses separately.
The concrete healthy-operand counterexample above is for AD.

## Basic trace-agreement examples

The library example is `BasicMerge` in
`deps/UTP-Reactive-Designs/utp_rdes_parallel.thy`. It equates the two branch
trace extensions with the final extension and preserves an ordinary state
component. Our `rad_state` alphabet has trace, refusal, and waiting fields,
but no separate ordinary state component. The examples therefore use its
state-free trace-agreement policy; they leave refusals unconstrained.

`basic_merge_state s l r z` requires that all three result traces agree and
extend `s.tr`, and chooses `z.wait = (l.wait ∨ r.wait)`. The wait equation is
an explicit policy of this example. For branch traces extending the prior
trace, equality of the full traces is equivalent to equality of their
extensions, as used by the library example.

`basic_merge_seed` lifts that rule to complete observations. Both branch
`ok` flags and the final `ok` flag must be true; the branch choice sets must
be exactly `{l}` and `{r}`, and the final choice set must contain a permitted
`z`. Waiting is still represented separately by each state's `wait` field.

This seed changes the choice-set lifting as well as the flag policy. For
fixed singleton branch results, let `S = {z. basic_merge_state s l r z}` be
the set of permitted merged states, and let `Z = ac'` be the proposed final
choice set:

| Requirement | Old `merge_ades_up` lifting | New `basic_merge_seed` |
| --- | --- | --- |
| Branch and final flags | `ok' = (ok_L \u2227 ok_R)` | `ok_L \u2227 ok_R \u2227 ok'` |
| Branch choice sets | Arbitrary sets, lifted pointwise | Exactly `{l}` and `{r}` |
| Final choices for these singleton branches | `S \u2286 Z` | `S \u2229 Z \u2260 {}` |

If `S = {a,b}` with distinct states, the old lifting requires both states
in `Z`; the seed accepts either singleton. If `S` is empty, the old lifting
accepts every `Z` when the flag equation holds, while the seed rejects the
branch pair. These are different merge semantics. The generic operator
does not impose either policy; using the unchanged old lifting reproduces
the old parallel exactly, with its original limitations.

This is a **singleton lifting**, not a proposed treatment of every multi-state
angelic choice. Exact singleton branch sets matter: checking only membership
would let upward-closed operands pad their branch sets with arbitrary matching
states. The raw seed also supplies no `ok = False` branch behaviour.
This example does not define general divergence propagation.

| Merge | Healthiness and closure | Trace-agreement behaviour |
| --- | --- | --- |
| `basic_merge_seed` | Satisfies `PBMHM`, `H2M`, `A0M`, `A2M`, and `RA1M`; fails the combined conditions. | Direct singleton synchronisation rule. |
| `BasicMerge_RAD = RADM_full basic_merge_seed` | `RADM_full`-healthy; preserves `RAD` for `RAD` operands. | Retains the seed rule at started, nonwaiting inputs with zero prior trace. |
| `BasicMerge_AP = APM basic_merge_seed` | `APM`-healthy; preserves `AP` for `AP` operands. | Retains the same rule at started, nonwaiting inputs with zero prior trace. |

The seed's `A2M` property is proved separately. No explicit `A2M` or A2
closure lemmas for the repaired `BasicMerge_RAD` and `BasicMerge_AP` examples
are included here; their combined RAD/AP closure theorems do not establish
that additional property by themselves.

Both repaired merges are symmetric and associative, so their parallel
operators commute and associate. These are proofs for this particular
singleton lifting; the general healthiness conditions do not imply either law.
Their ordinary execution equations and singleton examples explicitly check
trace agreement, rejection of unequal traces, and acceptance of nonempty
trace extensions. The healthiness repairs also supply their respective
startup and waiting observations; the repaired predicates are therefore
different from the raw seed.

The worked `PrefixSkip` calculations use healthy operands. At a started,
nonwaiting input with empty trace, and for a final choice set exactly `{z}`
with `z.wait = False`,
two event prefixes can complete together exactly when their events agree:
`ok' ∧ a = b ∧ z.tr = [a]`. Distinct events therefore have no joint completed
result; this does not rule out waiting observations. See
`BasicMerge_RAD_prefixes_complete` and `BasicMerge_AP_prefixes_complete`.

## Sources and examples

* [AD generic merge lifting and closure](../angelic-designs/utp_ades_parallel_generic.thy)
* [Stronger AD A3 construction and examples](../angelic-designs/utp_ades_parallel_normal.thy)
* [RAD generic merge healthiness](../reactive-angelic-designs/utp_rad_parallel_generic.thy)
* [AP generic merge healthiness](../angelic-processes/utp_ap_parallel_generic.thy)
* [RAD basic merge examples](../reactive-angelic-designs/utp_rad_parallel_examples.thy)
* [AP basic merge examples](../angelic-processes/utp_ap_parallel_examples.thy)

The AD examples use the existing right-state merge to exhibit a non-skip
result, dependence on the right branch, and a final termination flag that
the old conjunction rule would reject. `APM_right_merge_wait_example` also
exhibits a healthy AP merge accepting a non-skip result with `wait = False`
when the left branch's state has `wait = True`. Healthiness closure establishes
membership of the target theory; it does not by itself establish a particular
CSP synchronisation policy or associativity for arbitrary seed merges.

## Validation

On 2026-09-10, Isabelle2025-2 checked the generic theories and both focused
example theories, including the algebraic laws, basic trace-agreement examples,
and the healthy NAND counterexample above,
then completed all three sessions in the full working-tree build:

```bash
env ISABELLE_IDENTIFIER=utp-2025-2 \
  PROJECT_DIR=/Users/ming/AI-summer/repos/UTP-Angelic-CSP \
  /Applications/Isabelle2025-2.app/bin/isabelle build \
  -b -o system_heaps=false -o threads=2 UTP-Angelic-CSP
```

The interactive checking console was closed before the build. No MCP server
was started. The new theories contain no admitted proofs or added axioms.
`scripts/check-paper-baseline.py --prepare-only` also succeeded, and the
exported paper snapshot excludes all nine parallel research theories and
their registrations. This snapshot check did not run a separate paper build.
