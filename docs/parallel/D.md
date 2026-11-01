# Ordinary design parallel by merge

[Overview](README.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md) · [AP](AP.md)

[utp_des_parallel.thy](../../deps/UTP-Designs/utp_des_parallel.thy)
defines the ordinary-design operator `des_par`, written `P ∥D[j] Q`.
The state merge constrains the output only when both branch observations
terminate; after divergence, a merged state must still exist.
This guide describes the implementation on `research/parallel2`.

## Common notations

| Role | Flag | State |
| --- | --- | --- |
| Initial | `ok0` | `s0` |
| Left branch | `okL` | `sL` |
| Right branch | `okR` | `sR` |
| Merged output | `okOut` | `sOut` |

| Notation | Meaning |
| --- | --- |
| `P`, `Q`, `R :: 's des_hrel` | Relations over ordinary design observations |
| `P(ok0,s0,okOut,sOut)` | `P` accepts this initial/final observation pair |
| `j :: 's merge`; `j(s0,sL,sR,sOut)` | State merge; the latter abbreviates `merge_eval j s0 sL sR sOut` |
| `M :: 's des_merge` | Merge over design observations, including their flags |
| `P ∥[M] Q` | Generic parallel by merge |
| `P ∥D[j] Q` | Ordinary-design parallel using `merge_des j` |
| `P is H` | `P` is H1- and H2-healthy |
| `Chaos`, `Miracle` | `⊥D = true`, `⊤D = ¬ok0`, respectively |

An accepted observation with `okOut=False` admits nontermination. It does not
mean that the predicate `P` is false. The formulas below use readable observation
notation rather than literal Isabelle record syntax.

## Lifting state merge

[`merge_des_raw`](../../deps/UTP-Designs/utp_des_parallel.thy#L273)
`:: 's merge ⇒ 's des_merge` lifts the state merge and sets the output flag:

```text
merge_des_raw(j)((ok0,s0), (okL,sL), (okR,sR), (okOut,sOut))
  = (okOut = (okL ∧ okR)) ∧ j(s0,sL,sR,sOut)
```

The raw lift always applies `j`. Its result is an intermediate observation:
the final merge below releases it when either branch flag is false.

### Design merge healthiness

[`H1m`](../../deps/UTP-Designs/utp_des_parallel.thy#L20),
[`H2m`](../../deps/UTP-Designs/utp_des_parallel.thy#L25),
[`H3m`](../../deps/UTP-Designs/utp_des_parallel.thy#L30), and
[`HDM`](../../deps/UTP-Designs/utp_des_parallel.thy#L35)
each have type `'s des_merge ⇒ 's des_merge`:

```text
H1m M = M ∨ ¬ok0
H2m M = M ;; J
H3m M ≡ M ;; II_D
HDM M = H1m (H2m M)
```

`H1m` removes constraints before start. `H2m` composes with the design relation
`J`, allowing a false output flag to become true while preserving the output
state. `H3m` expresses right-skip closure on the merge alphabet and is
monotone and idempotent. H3 itself is typed for design relations, whose
input is a single design observation rather than a merge-input triple.
`HDM` still combines only H1m and H2m.

[`merge_des`](../../deps/UTP-Designs/utp_des_parallel.thy#L286)
follows the reactive-design merge `M_R(M) = N_R(M) ;; II_R`: the healthy raw
lift is followed by the design skip `II_D = (true ⊢r II)`:

```text
merge_des j = HDM (merge_des_raw j) ;; II_D
```

`II_D` accepts any output after a nonterminating intermediate observation and
copies a terminating one. Since `J ;; II_D = II_D`, the skip absorbs the `H2m`
part of `HDM`.
[`merge_des_alt_def`](../../deps/UTP-Designs/utp_des_parallel.thy#L291) proves:

```text
merge_des j = H1m (merge_des_raw j) ;; II_D
```

Composing with `H1m` before or after `;; II_D` gives the same merge.

[`merge_des_expand`](../../deps/UTP-Designs/utp_des_parallel.thy#L324)
unfolds the merge:

```text
merge_des(j)((ok0,s0), (okL,sL), (okR,sR), (okOut,sOut))
  = ¬ok0 ∨ (((okL ∧ okR) ⇒ (okOut ∧ j(s0,sL,sR,sOut)))
            ∧ (∃y. j(s0,sL,sR,y)))
```

| Merge input | Constraint on the merged output | Lemma |
| --- | --- | --- |
| `ok0=False` | None | [`merge_des_expand`](../../deps/UTP-Designs/utp_des_parallel.thy#L324) |
| `ok0=True`, both branch flags true | `okOut=True` and `j(s0,sL,sR,sOut)` | [`merge_des_expand_terminate`](../../deps/UTP-Designs/utp_des_parallel.thy#L336) |
| `ok0=True`, at least one branch flag false | Output unconstrained; some `y` with `j(s0,sL,sR,y)` must exist | [`merge_des_expand_diverge`](../../deps/UTP-Designs/utp_des_parallel.thy#L346) |

The divergent row matches the reactive merge, which retains only the existence
of a merged trace that the final trace extends.

[`merge_des_is_HDM`](../../deps/UTP-Designs/utp_des_parallel.thy#L295)
proves that `merge_des j is HDM` for every `j`, using `HDM_seq` and the
existing facts that `II_D` is normal
([`skip_d_is_H1_H3`](../../deps/UTP-Designs/utp_des_healths.thy#L772)) and
that normal designs are H
([`N_implies_H`](../../deps/UTP-Designs/utp_des_healths.thy#L735)).
No mergeability premise is required.

## Ordinary design parallel by merge

[`des_par`](../../deps/UTP-Designs/utp_des_parallel.thy#L355) is an
abbreviation, as reactive-design parallel `P ∥R[M] Q ≡ P ∥[M_R(M)] Q` is:

```text
P ∥D[j] Q ≡ P ∥[M_D(j)] Q        where M_D = merge_des
```

Generic parallel-by-merge lemmas therefore apply to it without unfolding.

Both branches share the initial observation. The outer existential quantifiers
select one accepted observation from each branch; the merge then relates these
to the output. By
[`des_par_expand`](../../deps/UTP-Designs/utp_des_parallel.thy#L364):

```text
(P ∥D[j] Q)(ok0,s0,okOut,sOut)
  iff ∃okL sL okR sR.
       P(ok0,s0,okL,sL)
     ∧ Q(ok0,s0,okR,sR)
     ∧ (¬ok0 ∨ (((okL ∧ okR) ⇒ (okOut ∧ j(s0,sL,sR,sOut)))
                ∧ (∃y. j(s0,sL,sR,y))))
```

Releasing the output constraint does not remove the requirement that both
branches supply an observation, nor that their states have some merged state.
This is why Miracle remains absorbing.

### Healthiness closure

At the generic concurrency level,
[`par_by_merge_seq_add`](../../deps/UTP/utp_concurrency.thy#L291) gives
`(P ∥[M] Q) ;; K = P ∥[M ;; K] Q`. Substituting `M ;; K = M`
immediately gives `(P ∥[M] Q) ;; K = P ∥[M] Q`, without any design-specific
premises. No separate completion lemma is needed.

At the design level, take `K = II_D` and use `H3 X ≡ X ;; II_D`.
The following rules apply to an arbitrary design merge `M`:

| Healthiness | Premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| H1 | `P`, `Q` both H1; `M is H1m` | `(P ∥[M] Q) is H1` | [`H1_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel.thy#L238) |
| H2 | `M is H2m`; no operand premises | `(P ∥[M] Q) is H2` | [`H2_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel.thy#L244) |
| H | `P`, `Q` both H1; `M is HDM` | `(P ∥[M] Q) is H` | [`H_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel.thy#L258) |
| H3 | `M is H3m`; no operand premises | `(P ∥[M] Q) is H3` | [`H3_par_by_merge`](../../deps/UTP-Designs/utp_des_parallel.thy#L251) |

The constructed merge satisfies both `merge_des j is HDM` and
[`merge_des_is_H3m`](../../deps/UTP-Designs/utp_des_parallel.thy#L299):
`merge_des j is H3m`, equivalently `merge_des j ;; II_D = merge_des j`. Hence:

| Healthiness | Premises | Conclusion | Lemma |
| --- | --- | --- | --- |
| H | `P`, `Q` both H1; arbitrary `j` | `(P ∥D[j] Q) is H` | [`des_par_H_closure`](../../deps/UTP-Designs/utp_des_parallel.thy#L379) |
| H3 | No operand premises; arbitrary `j` | `(P ∥D[j] Q) is H3` | [`des_par_H3_closure`](../../deps/UTP-Designs/utp_des_parallel.thy#L384) |
| N | `P`, `Q` both H1; arbitrary `j` | `(P ∥D[j] Q) is N` | [`des_par_N_closure`](../../deps/UTP-Designs/utp_des_parallel.thy#L388) |

Here `N X ≡ H1 (H3 X)`. None of these closure laws requires mergeability;
normality alone does not establish associativity.

## Nontermination, Chaos, and Miracle

At a fixed started initial state `s0`, a nonterminating observation from either
branch makes the composition accept every output, provided the other branch
has at least one observation and the two branch states have some merged state.
This is locally Chaos; it need not hold at other initial states.

| Premises at `s0` | Conclusion for every `okOut`, `sOut` | Lemma |
| --- | --- | --- |
| `P(True,s0,okL,sL)`, `Q(True,s0,okR,sR)`, `¬(okL ∧ okR)`, `j(s0,sL,sR,y)` | `(P ∥D[j] Q)(True,s0,okOut,sOut)` | [`des_par_diverge`](../../deps/UTP-Designs/utp_des_parallel.thy#L402) |

This law requires no healthiness premises. Even if the same branch also admits
termination, its nonterminating observation suffices.

Chaos supplies a divergent observation at every state. By
[`des_par_expand`](../../deps/UTP-Designs/utp_des_parallel.thy#L364), composing
with Chaos therefore accepts every output wherever the other operand has an
observation whose state `j` can merge with some state. An infeasible operand has
no such observation. Hence Chaos with Chaos is Chaos whenever `j` has a merged
state at every initial state, and Chaos is a zero for feasible (H4) operands
when `j` is [`mergeable`](../../deps/UTP/utp_concurrency.thy#L62), that is, `∀s0 sL sR. ∃y. j(s0,sL,sR,y)`. Miracle is a zero for H1 operands under any merge.

| Property | Premises | Equality | Lemma |
| --- | --- | --- | --- |
| Chaos with Chaos | `∀s0. ∃sL sR y. j(s0,sL,sR,y)` | `Chaos ∥D[j] Chaos = Chaos` | [`des_par_chaos_chaos`](../../deps/UTP-Designs/utp_des_parallel.thy#L409) |
| Chaos zero | `P is H4`; `mergeable j` | `P ∥D[j] Chaos = Chaos ∥D[j] P = Chaos` | [`des_par_chaos`](../../deps/UTP-Designs/utp_des_parallel.thy#L416) |
| Miracle zero | `P is H1`; arbitrary `j` | `P ∥D[j] Miracle = Miracle ∥D[j] P = Miracle` | [`des_par_miracle`](../../deps/UTP-Designs/utp_des_parallel.thy#L432) |

Neither Chaos-zero premise can simply be dropped. Miracle is H1 but not H4, and
`Chaos ∥D[j] Miracle = Miracle`: Miracle supplies no started observation, so
the existential branch selection fails. Without a merge premise, if `P` always
terminates in a state that `j` merges with no state, `P ∥D[j] Chaos` has no
started observation. The merge premise can be weakened, though: pairing Chaos's
divergent observation with the other operand's own state needs only
self-mergeability, `∀s0 s. ∃y. j(s0,s,s,y)`. This is a hand argument;
`des_par_chaos` assumes and uses `mergeable j`, and no self-mergeability
variant is proved.

The Chaos-with-Chaos premise is exact: if some `s0` has no merged state for any
pair, `Chaos ∥D[j] Chaos` rejects every started observation at `s0`.

## Commutativity

[`des_par_comm`](../../deps/UTP-Designs/utp_des_parallel.thy#L446) proves
`P ∥D[j] Q = Q ∥D[j] P` when `j is SymMerge`, with no operand premises. It
applies the generic `par_by_merge_comm` to the lifted merge, which is symmetric
by [`merge_des_SymMerge`](../../deps/UTP-Designs/utp_des_parallel.thy#L304):
swapping the branches only exchanges `okL ∧ okR` and the arguments of `j`,
`HDM` preserves `SymMerge`, and `II_D` runs after the merge.

## Associativity

[`des_par_assoc_state`](../../deps/UTP-Designs/utp_des_parallel.thy#L453)
proves:

```text
(P ∥D[j] Q) ∥D[j] R = P ∥D[j] (Q ∥D[j] R)
```

It requires three premises on the state merge:

| Premise | Formula |
| --- | --- |
| Symmetry | `j is SymMerge`: `j(s0,a,b,z) ↔ j(s0,b,a,z)` |
| Rotation invariance | `AssocMerge j`: `(∃v. j(s0,a,b,v) ∧ j(s0,v,c,z)) ↔ (∃v. j(s0,b,c,v) ∧ j(s0,v,a,z))` |
| Mergeability | `mergeable j`: `∀s0 a b. ∃z. j(s0,a,b,z)` |

`AssocMerge j` says that rotating the three inputs of the left-nested merge
leaves it unchanged. With symmetry it gives the relational associativity the
proof uses, `(∃v. j(s0,a,b,v) ∧ j(s0,v,c,z)) ↔ (∃v. j(s0,b,c,v) ∧ j(s0,a,v,z))`.
Associative merges that are not symmetric, such as "left wins", are not covered.

The initial state `s0` stays fixed throughout both nested merges. The theorem
requires no operand healthiness. Mergeability permits
multiple results: it requires at least one result for each pair of branch
states, not every possible output state.

Mergeability prevents an intermediate terminating pair from becoming infeasible
before it meets a divergent branch. Relational associativity alone does not
prevent that loss of branch observations. For example, take states `{s,t}` and
let `j(s0,s,s,t)` be the only merge. Then `j` satisfies `SymMerge` and `AssocMerge`, but
if `P`, `Q` terminate at `s` and `R` diverges, `(P ∥D[j] Q) ∥D[j] R` needs a
merge of `t` with `s`, whereas `P ∥D[j] (Q ∥D[j] R)` may choose a divergent
intermediate `s`. Under mergeability, the existence clause of `merge_des` is always
true. These are the theorem's sufficient premises; the file does not prove that
mergeability is necessary for every merge.

## Merge-healthiness algebra and source navigation

The earlier sections of the theory develop general design-merge healthiness,
independently of `merge_des_raw`.

| Topic | Result and premises | Source |
| --- | --- | --- |
| Idempotence and monotonicity | `H1m`, `H2m`, and `HDM` are idempotent and monotone; H1m and H2m commute | [Idempotence and monotonicity](../../deps/UTP-Designs/utp_des_parallel.thy#L38) |
| Fixed points | `M is HDM ↔ (M is H1m ∧ M is H2m)` | [`HDM_fixed_iff`](../../deps/UTP-Designs/utp_des_parallel.thy#L94) |
| Disjunction | All three healthiness functions distribute over disjunction | [Disjunction and conjunction](../../deps/UTP-Designs/utp_des_parallel.thy#L109) |
| Conjunction | H1m distributes unconditionally; H2m and HDM distribution is proved for H2m-healthy operands and fails in general | [`H2m_conj`](../../deps/UTP-Designs/utp_des_parallel.thy#L127), [`HDM_conj`](../../deps/UTP-Designs/utp_des_parallel.thy#L137), [counterexamples](../../deps/UTP-Designs/utp_des_parallel.thy#L142) |
| Healthy combinations | For each of H1m, H2m, and HDM, disjunction and conjunction of healthy merges remain healthy | [Closure lemmas](../../deps/UTP-Designs/utp_des_parallel.thy#L160) |
| Symmetry | Each healthiness function preserves `SymMerge` | [Symmetry](../../deps/UTP-Designs/utp_des_parallel.thy#L190) |
| Sequential closure | H1m needs `M is H1m` and an H1 continuation; H2m needs only an H2 continuation; HDM needs only `M is H1m` and an H continuation | [Sequential composition](../../deps/UTP-Designs/utp_des_parallel.thy#L207) |

The file contains no parallel identity theorem. The symmetry lemmas feed
[`merge_des_SymMerge`](../../deps/UTP-Designs/utp_des_parallel.thy#L304), which gives `des_par_comm`.

## AD correspondence

The [AD guide](AD.md) describes the matching AD lifting, which requires a merged
state for every pair of branch states and coverage only when both branches
terminate. The four public `ac2p`/`d2ac` parallel mapping laws hold for
arbitrary `j`, with A/A2 premises on angelic operands and H premises on ordinary
operands. Lifted AD parallel is already A3-healthy for H1-healthy operands, so
its mapping laws need no excluded-output premise. The mappings and the paper's
refinement lemma are unchanged. RAD/AP retain their separate reactive merge
semantics.
