# Historical parallel-by-merge notes

> These notes retain the earlier UTP walkthrough and pointwise angelic
> construction. That angelic implementation has been removed from this
> branch. Use [Parallel by merge](docs/PARALLEL.md) for the current
> conjunction-based operators and their assumptions.

This note explains the main mathematical ideas in
[`utp_concurrency.thy`](deps/UTP/utp_concurrency.thy), gives a quick-reference
walkthrough of the merge healthiness conditions and closure rules in
[`utp_rea_parallel.thy`](deps/UTP-Reactive/utp_rea_parallel.thy), and records
how [`utp_rdes_parallel.thy`](deps/UTP-Reactive-Designs/utp_rdes_parallel.thy)
and the angelic theories build on the generic construction.

The extension using merge predicates on complete AD, RAD, and AP observations
is described in [Generic merge predicates](docs/PARALLEL.md), including
its monotone, idempotent merge operators and parallel-closure conditions.
The state-level lifting described below is historical and is no longer implemented.

The central idea is:

> Run both relations from the same initial observation, retain their two final
> observations separately, and then use a merge relation to construct the
> combined final observation.

Thus, UTP does not prescribe one universal meaning of parallel composition.
The merge relation supplies the particular concurrency semantics.

## Bottom-up reading guide

The construction has four levels. The lower levels provide the relational
wiring and the merge parameter; the higher levels lift that parameter to
choice sets and add the healthiness conditions required by reactive angelic
designs and angelic processes.

### Level 0: generic relational kernel

This level is implemented in
[`utp_concurrency.thy`](deps/UTP/utp_concurrency.thy).

1. The `mrg` alphabet stores three observations: the shared prior observation,
   the left branch result, and the right branch result.

2. A merge predicate $M$ reads that `mrg` observation and produces one
   combined result. The choice of $M$ supplies the actual concurrency
   semantics.

3. `U0` and `U1` rename the two branch outputs into the separate left and
   right fields of `mrg`. This avoids accidentally equating identically named
   after-variables from the two branches.

4. `par_sep` runs $P$ and $Q$ from the same initial observation and retains
   their results separately:

   $$
   P\parallel_s Q
   = (P;U_0)\land(Q;U_1)\land(m_{<}=\sigma).
   $$

5. `par_by_merge` sequentially passes the separated results to $M$:

   $$
   P\parallel_M Q=(P\parallel_s Q);M.
   $$

The generic theory proves the `false` laws, the post-processing law
`par_by_merge_seq_add`, the feasible `skip_m` law, and commutativity when
`swap_m ;; M = M`. It also defines `ThreeWayMerge` and `AssocMerge`, but does
not yet prove a generic parallel associativity theorem.

### Reference branch: standard reactive theories

The existing reactive theories provide the model for the angelic conditions
introduced later:

- [`utp_rea_parallel.thy`](deps/UTP-Reactive/utp_rea_parallel.thy) works at
  the reactive-relation layer. It defines the merge conditions `R1m`,
  `R1m'`, `R2m`, `R2m'`, `R2cm`, and `R3m`, then proves the corresponding
  `R1`, `R2`, and `R3` parallel-closure rules. Section 11 gives the complete
  read-through. These conditions do not combine the two branch `ok` values;
  `R3m` only copies the whole prior observation in its waiting branch.

- [`utp_rdes_parallel.thy`](deps/UTP-Reactive-Designs/utp_rdes_parallel.thy)
  adds the reactive-design protocol. Its `nmerge_rd` normalisation includes
  the equations $ok'=ok_0\land ok_1$ and
  $wait'=wait_0\lor wait_1$, and `RDM` supplies the healthiness condition on
  the underlying merge.

These theories guide the new construction, but the angelic development cannot
reuse their merge types directly because an angelic result contains a set of
possible states.

### Level 1: angelic-design choice-set lifting

This level is implemented in
[`utp_ades_parallel.thy`](angelic-designs/utp_ades_parallel.thy).

1. Start with a homogeneous state-level merge $J$.

2. `merge_ades(J)` lifts $J$ to angelic choice sets. Its output choice set is
   exactly the image obtained by applying $J$ to every pair consisting of one
   left choice and one right choice.

3. Applying `PBMH_ades` replaces exact equality of that image by inclusion.
   The resulting `merge_ades_up(J)` is the public, upward-closed merge.

4. Angelic-design parallel instantiates generic parallel-by-merge with this
   lifted predicate:

   $$
   P\parallel^{AD}_{J}Q
   =P\parallel_{M_{AD}^{\uparrow}(J)}Q.
   $$

The lifted operator is unconditionally `PBMH_ades`-healthy. It preserves the
design healthiness conditions under the stated operand assumptions, preserves
`A` when $J$ is total, and is monotonic in both operands. It distributes
exactly through demonic choice; for angelic choice the generally valid laws
are one-way refinements, since the two branches of the outer choice can use
different parallel witnesses.

Symmetry of $J$ gives commutativity. If $J$ is also `AssocMerge`-healthy, the
choice-set image is associative and so is AD parallel:

$$
(P\parallel^{AD}_{J}Q)\parallel^{AD}_{J}R
=P\parallel^{AD}_{J}(Q\parallel^{AD}_{J}R).
$$

There is no unconditional `A2` or `A3` closure law for a relational $J$;
the required merge conditions follow the `R1m` naming pattern. For H- and
`A2`-healthy operands, `A2` closure holds for a functional merge (`A2j`).
For H-healthy operands, `A3` closure holds for a merge excluding
some exact singleton image at every prior state (`A3j`) or, for an arbitrary
merge, for normal operands, whose preconditions cannot inspect the output
choice set. The
counterexamples `ades_par_rel_A3_rel_counterexample` and
`ades_par_rel_A2_rel_counterexample` show that the named weaker premise
packages are insufficient: totality alone does not guarantee `A2` closure,
and totality plus functionality does not guarantee `A3` closure. Separately,
`ades_par_A3_closure_iff_A3j` proves that, under `A0j`, `A3j` is necessary and
sufficient for A3 of every parallel of H-healthy operands. This does not
claim necessity for partial merges or narrower operand classes; no analogous
necessity result is established for `A2j`.

### Level 2: reactive angelic designs

This level is implemented in
[`utp_rad_parallel.thy`](reactive-angelic-designs/utp_rad_parallel.thy).

1. `RA1m` requires the merged trace to extend the prior trace. `RA2m` removes
   dependence on the common trace history. Their primed variants additionally
   require both branch traces to extend the prior trace. At present only their
   idempotence laws are developed; the current closure proofs use the unprimed
   `RA1m` and `RA2m` conditions.

2. `RA3m` restores the prior state when the prior observation is waiting.
   The combined merge condition is

   $$
   RADM=RA2m\circ RA3m.
   $$

3. Raw AD parallel is `RA1`-closed for `RA1`-healthy operands and a total,
   `RA1m`-healthy merge. It is `RA2`-closed for `RA2`-healthy operands and an
   `RA2m`-healthy merge. It is not `RA3`-closed: at an unstarted waiting
   observation it forces the prior state into the combined choice set, while
   `II_Rac` only requires some trace-extending choice.

4. Reactive angelic parallel therefore wraps raw AD parallel in `CSPA1`:

   $$
   P\parallel^{RAD}_{J}Q
   =CSPA1(P\parallel^{AD}_{J}Q).
   $$

The wrapper supplies the missing unstarted behaviour. With RAD-healthy
operands and a total, `RADM`-healthy merge, the result is RAD-healthy. Symmetry
of $J$ again yields commutativity.

### Level 3: angelic processes

This level is implemented in
[`utp_ap_parallel.thy`](angelic-processes/utp_ap_parallel.thy).

1. `merge_AP(J)` is an abbreviation for the existing upward-closed AD lift:

   $$
   M_{AP}(J)=M_{AD}^{\uparrow}(J).
   $$

2. AP parallel currently reuses the AD operator directly:

   $$
   P\parallel^{AP}_{J}Q=P\parallel^{AD}_{J}Q.
   $$

3. The current theory provides the pointwise evaluation law, commutativity,
   left and right Miracle-zero laws, and qualified Chaos-zero laws. The Chaos
   results require `AP_feasible` because the other branch must supply a
   successful result at a started, non-waiting observation.

4. The remaining work is to prove feasibility for the principal constructors,
   AP closure, the RAD/AP correspondence, possible `NDAP` closure, and laws for
   a concrete synchronising merge, including conditional associativity.

The main properties move upward through the construction as follows:

| Property | Low-level source | How it lifts | Current high-level result |
|---|---|---|---|
| PBMH healthiness | `PBMH_ades` | Exact image equality becomes image inclusion in `merge_ades_up`. | AD, RAD, and AP all reuse the upward-closed choice-set merge. |
| Commutativity | `swap_m ;; J = J` | `merge_ades_up_swap` preserves symmetry; the generic `par_by_merge_comm` calculation can then be reused. | `ades_par_comm`, `rad_par_comm`, and `ap_par_comm`. |
| Choice-set non-emptiness | `A0j J` | A pair of non-empty branch choice sets has at least one merged result. | Required for AD `A` closure and for the current RAD closure theorem. |
| Trace and waiting behaviour | `RADM = RA2m ∘ RA3m` | Raw AD parallel supplies the `RA1`/`RA2` part; `CSPA1` supplies the missing unstarted `RA3` behaviour. | `rad_par_RAD_closure`. |
| Miracle zero | AP healthiness plus an `RA3m`-healthy merge | The pointwise AP evaluation splits started and waiting observations. | Left and right `top_AP` zero laws. |
| Chaos zero | `AP_feasible P` plus AP and `RA3m` healthiness | Feasibility supplies a successful result from the non-Chaos branch at a started, non-waiting observation. | Qualified left and right `Chaos_AP` zero laws. |
| Associativity | Symmetry `swap_m ;; J = J` together with `AssocMerge J` | `ades_merge_image_assoc` lifts the state law to choice sets; monotonicity transports it through upward closure. | `ades_par_assoc` proves AD associativity. Preservation by the RAD healthiness wrapper remains a higher-layer task. |

The source path corresponding to these levels is
[`utp_concurrency.thy`](deps/UTP/utp_concurrency.thy) →
[`utp_ades_parallel.thy`](angelic-designs/utp_ades_parallel.thy) →
[`utp_rad_parallel.thy`](reactive-angelic-designs/utp_rad_parallel.thy), with
[`utp_ap_parallel.thy`](angelic-processes/utp_ap_parallel.thy) specialising the AD lift and
using the RAD waiting-case support.

## Critical review notes

The following points record current limitations, qualified results, and
organization work exposed by a critical review of the mechanisation.

- **Necessity has a precise scope.** The AD counterexamples only establish
  that particular weaker premise packages fail. The separate theorem
  `ades_par_A3_closure_iff_A3j` characterises A3 of every parallel of H-healthy
  operands under a total merge (`A0j`). It does not assert necessity for
  partial merges or narrower operand classes. `A2j` remains a sufficient
  condition without a corresponding necessity theorem.

- **Strict growth is incompatible with the present waiting discipline.** An
  `RA3m`-healthy merge must return the prior state when the prior observation
  is waiting, so its output trace then equals the prior trace. An
  `RA1sm`-healthy merge requires the output trace to be strictly greater than
  the prior trace. Consequently no merge can be both `RA1sm`-healthy and
  `RADM`-healthy, because `RADM` healthiness entails `RA3m` healthiness. The
  theorem `RA1sm_A3j` is valid, but `RA1sm` is currently a separate sufficient
  route to `A3j`, not an additional condition usable in the RAD closure
  theorem. A productive RAD condition would need to exempt waiting priors or
  otherwise reconcile strict growth with the `RA3m` identity branch.

- **The primed merge conditions are provisional.** `RA1m'` and `RA2m'` mirror
  the stronger standard reactive conditions, but currently have only
  idempotence results and are not used by the closure proofs. Either their
  monotonicity, fixed-point, evaluation, and closure interface should be
  completed, or they should remain explicitly marked as future support.

- **Some foundational RAD facts are stored too high in the import graph.** The
  `H2` commutation laws, the projections from `RA` healthiness to
  `RA1`/`RA2`/`RA3`, `RAD_is_CSPA2`, and the general `CSPA1` component and
  preservation laws do not depend essentially on parallel. They should
  eventually move to `utp_rad_healthy.thy` or `utp_rad_designs.thy`, leaving
  `utp_rad_parallel.thy` focused on the operator and its closure results.

- **Duplicate RAD declarations remain.** AD now provides `skip_merge_eval`
  and `skip_merge_A0j`, beside `skip_merge_A2j` and `skip_merge_A3j`.
  RAD still declares its own `skip_merge_eval` and `A0j_skip_merge`; these
  WIP declarations are retained for a later cleanup.

- **The repository snapshot must be committed as one coherent extension.**
  The RAD/AP theory files, their `ROOT` and aggregate imports, and this
  documentation describe one development. A commit containing only the AD
  theory and documentation would leave documented files and results absent
  from the repository.

## 1. Relations and observations

Regard a UTP relation

$$
P \subseteq \alpha \times \beta
$$

as a predicate $P(\sigma,p)$, where $\sigma\in\alpha$ is an initial
observation and $p\in\beta$ is a possible final observation. Similarly, let

$$
Q \subseteq \alpha \times \gamma.
$$

Both relations start from the same initial observation, but their final
observation types may differ.

If we simply conjoined $P$ and $Q$, their after-variables would collide.
For example, both branches might write $x'$, and conjunction would
accidentally require the two values of $x'$ to be equal. Parallel-by-merge
therefore renames and stores the two branch results separately before they are
combined.

## 2. The merge observation

The alphabet `mrg` contains three observations:

$$
m = (m_{<},m_0,m_1),
$$

where

- $m_{<}\in\alpha$ is the prior, shared observation;
- $m_0\in\beta$ is the final observation produced by the left branch;
- $m_1\in\gamma$ is the final observation produced by the right branch.

The corresponding Isabelle fields are `mrg_prior`, `mrg_left`, and
`mrg_right`. In expressions, their variable prefixes are `<`, `0`, and `1`.

A general merge relation has type

$$
M \subseteq (\alpha\times\beta\times\gamma)\times\delta.
$$

It observes the shared prior state and both branch results, and produces a
combined result in $\delta$. In Isabelle, this is the middle argument of
`par_by_merge`:

$$
P : \alpha\leftrightarrow\beta,
\qquad
M : (\alpha,\beta,\gamma)\,\textit{mrg}\leftrightarrow\delta,
\qquad
Q : \alpha\leftrightarrow\gamma.
$$

The type synonym `merge` is a homogeneous special case:

$$
\alpha\,\textit{merge}
=
(\alpha,\alpha,\alpha)\,\textit{mrg}\leftrightarrow\alpha.
$$

Its Isabelle spelling is:

```isabelle
type_synonym 'α merge = "(('α, 'α, 'α) mrg, 'α) urel"
```

The three occurrences of `'α` inside `mrg` are the prior, left, and right
parts of the merge input. The final `'α`, after the comma, is the output type
of the relation: it is the single merged result, not a fourth input part.

The underlying `par_by_merge` operator is more general than this synonym: its
initial, left-final, right-final, and merged-final observation types can all be
different.

## 3. Separating the branch results

The relations `U0` and `U1` are generic wiring relations, not designs or
destructive assignments. In the context
$P:\alpha\leftrightarrow\beta$ and $Q:\alpha\leftrightarrow\gamma$, they
are instantiated as

$$
U_0:\beta\leftrightarrow(\alpha,\beta,\gamma)\,\textit{mrg},
\qquad
U_1:\gamma\leftrightarrow(\alpha,\beta,\gamma)\,\textit{mrg}.
$$

They constrain the left or right field of the output merge record to equal
their input. Thus `P ;; U0` and `Q ;; U1` both have output type
$(\alpha,\beta,\gamma)\,\textit{mrg}$, and sequential composition gives

$$
(P;U_0)(\sigma,m) \iff P(\sigma,m_0),
$$

and

$$
(Q;U_1)(\sigma,m) \iff Q(\sigma,m_1).
$$

The intermediate branch result is hidden by `;;`; the prior and other branch
field remain unconstrained until the three conjuncts of `par_sep` are combined.

The separator `par_sep` is

$$
P\parallel_s Q
=
(P;U_0)\land(Q;U_1)\land(m_{<}=\sigma).
$$

Consequently,

$$
(P\parallel_s Q)(\sigma,m)
\iff
P(\sigma,m_0)\land Q(\sigma,m_1)\land m_{<}=\sigma.
$$

The last conjunct copies the common initial observation into the prior part of
the merge record. Neither branch is responsible for combining its result with
the other branch.

The same construction can be written using alphabet extrusion:

$$
P\parallel_s Q
=
\lceil P\rceil_0
\land
\lceil Q\rceil_1
\land
(m_{<}=\sigma).
$$

Here $\lceil P\rceil_0$ renames the after-variables of $P$ into the left
component, and $\lceil Q\rceil_1$ renames those of $Q$ into the right
component. The equivalences are established by `U0_as_alpha` and
`U1_as_alpha`.

Most of the lemmas between `U0_as_alpha` and `varr_sub_merge_right` are
bookkeeping laws for these renamings: lens well-behavedness, independence,
substitution, and sequential composition.

## 4. Parallel by merge

The generic operator is defined by

$$
P\parallel_M Q
=
(P\parallel_s Q);M.
$$

This is `par_by_merge_def`. Expanding the relational compositions gives the
most useful semantic reading:

$$
(P\parallel_M Q)(\sigma,z)
\iff
\exists p\in\beta,\,q\in\gamma\bullet
P(\sigma,p)
\land
Q(\sigma,q)
\land
M((\sigma,p,q),z).
$$

There are therefore two distinct stages:

1. $P$ and $Q$ independently produce $p$ and $q$ from the same
   initial observation $\sigma$.
2. $M$ decides which combined results $z$ are permitted.

Both the branches and the merge may be nondeterministic. The result contains
every combination of branch results accepted by $M$.

The alternative form is recorded by `par_by_merge_alt_def`:

$$
P\parallel_M Q
=
\bigl(\lceil P\rceil_0
\land\lceil Q\rceil_1
\land(m_{<}=\sigma)\bigr);M.
$$

This form is often convenient when proving predicate-calculus laws.

## 5. The merge determines the concurrency model

The operator $\parallel_M$ is only a framework. Different choices of $M$
can express different models, for example:

- disjoint-state parallelism, where the two state partitions are recombined;
- shared-state interference, where both branch results constrain the result;
- trace synchronisation or interleaving;
- refusal-set combination;
- a merge that rejects incompatible branch results;
- a nondeterministic merge that permits several combined outcomes.

This separation is useful because algebraic properties of the parallel
operator can be reduced to algebraic properties of $M$.

## 6. The prior-state merge

The merge `skip_m` ignores both branch results and restores the prior
observation:

$$
\mathit{skip}_m((\sigma,p,q),z)
\iff
z=\sigma.
$$

The Isabelle definition says exactly this:

```isabelle
skip\<^sub>m = ($\<^bold>v\<^sup>> = $<:\<^bold>v\<^sup><)\<^sub>e
```

Here `$\<^bold>v\<^sup>>` is the whole merged output,
`$<:\<^bold>v\<^sup><` is the prior part of the merge input, and
`(...)\<^sub>e` lifts the equality to a UTP predicate. Thus `skip_m` is the
merge relation itself, not a test applied to some other merge.

Suppose both branches are feasible from every initial observation:

$$
P;\mathit{true}=\mathit{true},
\qquad
Q;\mathit{true}=\mathit{true}.
$$

Then the branches can produce some outputs, `skip_m` discards those outputs,
and the original observation is restored:

$$
P\parallel_{\mathit{skip}_m}Q=II.
$$

This is `par_by_merge_skip`. The feasibility premises are necessary: if a
branch has no possible result for an input, parallel composition cannot reach
the merge stage for that input.

## 7. Symmetry and commutativity

The relation `swap_m` exchanges the two branch-result components while leaving
the prior component unchanged:

$$
\mathit{swap}_m(\sigma,p,q)=(\sigma,q,p).
$$

Its Isabelle spelling is a simultaneous assignment:

```isabelle
swap\<^sub>m = (0:\<^bold>v, 1:\<^bold>v) := ($1:\<^bold>v, $0:\<^bold>v)
```

The left side names the components to update; the right side reads their old
values. Hence the new left component is the old right component and the new
right component is the old left component. The unmentioned prior component is
unchanged. The two branch components have the same type `'β`, which is why the
type is `(('α, 'β, 'β) mrg) hrel`.

A merge is symmetric when swapping its two branch inputs has no effect:

$$
\mathit{swap}_m;M=M.
$$

Equivalently,

$$
M((\sigma,p,q),z)
\iff
M((\sigma,q,p),z).
$$

The existing abbreviation `SymMerge` represents the healthiness function

$$
\mathit{SymMerge}(M)=\mathit{swap}_m;M.
$$

Thus, `M is SymMerge` means precisely
$\mathit{swap}_m;M=M$.

The structural fact behind commutativity is `par_sep_swap`:

$$
(P\parallel_s Q);\mathit{swap}_m
=
Q\parallel_s P.
$$

For a symmetric merge,

$$
\begin{aligned}
P\parallel_M Q
  &= (P\parallel_s Q);M \\
  &= (P\parallel_s Q);\mathit{swap}_m;M \\
  &= (Q\parallel_s P);M \\
  &= Q\parallel_M P.
\end{aligned}
$$

The generic theory records this calculation as `par_by_merge_comm`.  Its
premise is the direct symmetry equation `swap_m ;; M = M`, so the result also
applies to heterogeneous merges whose prior and final types differ.

### Symmetry with different initial and result types

`SymMerge` and `swap_m` allow different initial and result types. The symmetry
equation

$$
\mathit{swap}_m;M=M,
$$

make sense whenever the left and right result types agree, even if the prior
and final types are different. This distinction matters for angelic designs:
their initial observation contains an `astate`, while their final observation
contains an `achoices` set.

The library declarations have been generalised in place, so angelic designs
can use `M is SymMerge` directly. `ThreeWayMerge` and `AssocMerge` also allow
the initial type to differ from the branch-result type. Their branch and
final result types must agree so that one merge result can feed into another.

## 8. Three-way merging and associativity

To discuss associativity, `ThreeWayMerge` wires two copies of a binary merge
relation together. Ignoring the record plumbing, its meaning is

$$
M_3(\sigma;x,y,z;w)
\iff
\exists u\bullet
M((\sigma,x,y),u)
\land
M((\sigma,u,z),w).
$$

Thus, it first merges $x$ with $y$, and then merges that intermediate
result with $z$, always retaining the same prior observation $\sigma$.

The renaming `rotate_m` cyclically rotates the three branch inputs:

$$
(x,y,z)\longmapsto(y,z,x).
$$

The definition `AssocMerge` requires the constructed three-way merge to be
invariant under this rotation:

$$
\mathit{rotate}_m;M_3(M)=M_3(M).
$$

Equivalently,

$$
M_3(\sigma;y,z,x;w)
\iff
M_3(\sigma;x,y,z;w).
$$

This cyclic-invariance equation is the library's relational encoding of an
associative merge. When the merge is also symmetric, it has the familiar
algebraic interpretation

$$
(x\mathbin{M}y)\mathbin{M}z
=
x\mathbin{M}(y\mathbin{M}z),
$$

with existentially quantified intermediate observations when $M$ is
nondeterministic.

`utp_concurrency.thy` defines `ThreeWayMerge`, `rotate_m`, and `AssocMerge`,
but it does not yet prove a generic associativity theorem for
parallel-by-merge.

## 9. Existing generic laws

The main laws currently available are:

| Isabelle lemma | Mathematical content |
|---|---|
| `par_by_merge_false` | $P\parallel_{\mathit{false}}Q=\mathit{false}$. |
| `par_by_merge_left_false` | $\mathit{false}\parallel_M Q=\mathit{false}$. |
| `par_by_merge_right_false` | $P\parallel_M\mathit{false}=\mathit{false}$. |
| `par_by_merge_seq_add` | $(P\parallel_M Q);R=P\parallel_{M;R}Q$. |
| `par_by_merge_skip` | Feasible $P,Q$ satisfy $P\parallel_{\mathit{skip}_m}Q=II$. |
| `skip_merge_swap` | $\mathit{swap}_m;\mathit{skip}_m=\mathit{skip}_m$. |
| `par_sep_swap` | $(P\parallel_s Q);\mathit{swap}_m=Q\parallel_s P$. |
| `par_by_merge_comm` | A merge satisfying $\mathit{swap}_m;M=M$ induces a commutative parallel operator. |

The first three laws follow directly from the semantic reading: a result needs
simultaneous witnesses for $P$, $Q$, and $M$, so `false` in any position removes
every possible result.

The law `par_by_merge_seq_add` says that post-processing the combined result is
equivalent to incorporating that post-processing into the merge:

$$
(P\parallel_M Q);R
=
P\parallel_{M;R}Q.
$$

This is a useful modularity law: the branches are unaffected by any operation
that occurs strictly after their results have been merged.

## 10. Unrestriction and substitution

The unrestriction laws describe variable dependence.

For an input variable $x$, `unrest_in_par_by_merge` says that
$P\parallel_M Q$ does not read $x$ when:

- neither $P$ nor $Q$ reads $x$; and
- the prior component of $M$ does not read $x$.

For an output variable $x'$, `unrest_out_par_by_merge` says that the whole
parallel composition does not constrain $x'$ when $M$ does not constrain
it. This reflects the two-stage semantics: only the merge relation creates the
final combined output.

The substitution law `lit_pbm_subst` has the corresponding structure:

- substitution into an initial variable must be pushed into both branches and
  the prior component of the merge;
- substitution into a final variable affects only the merge.

The current law supports literal substitution. The source notes that a more
general substitution theorem would require additional alphabet coercions.

## 11. How the reactive theories extend the construction

### Reactive relations: a quick walkthrough of `utp_rea_parallel.thy`

#### Scope and notation

This theory does not define another parallel operator. It takes
$P\parallel_M Q$ from `utp_concurrency.thy` and asks which conditions on $M$
make the result satisfy `R1`, `R2`, or `R3`.

A reactive merge has type

```isabelle
('t::trace, '\<alpha>) rp merge
```

The `rp` carrier contains `ok`, `wait`, `tr`, and an extension state, but
having that carrier does not make a predicate a reactive design. The merge
receives three reactive observations and produces a fourth:

- $tr_{<}$ is the trace in the shared prior observation;
- $tr_0$ is the final trace produced by the left branch;
- $tr_1$ is the final trace produced by the right branch;
- $tr'$ is the final merged trace produced by $M$.

The suffix `m` means that a condition acts on a merge predicate rather than an
ordinary reactive relation. An apostrophe in `R1m'` or `R2m'` names a
strengthened auxiliary condition; it is not an after-variable marker.

#### `R1m` and `R1m'`: trace growth

`R1m` requires only the merged result to extend the common history:

$$
\boxed{R1_m(M)=M\land tr_{<}\leq tr'.}
$$

`R1m'` also exposes the corresponding well-formedness conditions for the two
branch results:

$$
\boxed{
R1'_m(M)=
M\land tr_{<}\leq tr'
 \land tr_{<}\leq tr_0
 \land tr_{<}\leq tr_1.
}
$$

Thus `R1m'` is stronger than `R1m`. The extra conditions are not needed merely
to show that the final merged trace grows, but they are useful when all three
trace extensions must be extracted in the `R2` calculation.

The rules established around these definitions are:

- `R1m_idem` and `R1m'_idem`: both operators are idempotent.
- `R1m_mono` and `R1m'_mono`: both are monotonic.
- `R1m_seq`: if $M$ is `R1m`-healthy and $S$ is `R1`-healthy, then
  $M;S$ is `R1m`-healthy.
- `R1_par_by_merge`:

  $$
  \boxed{M\text{ is }R1m\Longrightarrow
         P\parallel_M Q\text{ is }R1.}
  $$

  No `R1` premises on $P$ and $Q$ are required: the final trace of the
  composition is created by $M$, and `R1m` constrains it directly.
- `R1m_skip_merge`, `R1m_disj`, and `R1m_conj`: `skip_m` is healthy and
  `R1m` distributes through disjunction and conjunction.

#### `R2m` and `R2m'`: history independence

A merge can inspect four absolute traces, so ordinary `R2` normalisation must
be applied to all four. Write

$$
\begin{aligned}
\mathcal N_h(M)=M[
  0,\;&tr'-tr_{<},\;tr_0-tr_{<},\;tr_1-tr_{<}\\
  &/tr_{<},\;tr',\;tr_0,\;tr_1].
\end{aligned}
$$

Then the two merge conditions are:

$$
\boxed{R2_m(M)=R1_m(\mathcal N_h(M))}
\qquad
\boxed{R2'_m(M)=R1'_m(\mathcal N_h(M)).}
$$

Both make $M$ see only the merged, left, and right trace extensions over a
zero prior history. The primed version additionally records that all three
actual traces extend the common prior trace.

The lemma `R2m'_form` gives the most readable form of the primed condition:

$$
\boxed{
\begin{aligned}
R2'_m(M)=\exists tt,tt_0,tt_1.\;&
 M[0,tt,tt_0,tt_1/tr_{<},tr',tr_0,tr_1]\\
&\land tr'=tr_{<}+tt\\
&\land tr_0=tr_{<}+tt_0\\
&\land tr_1=tr_{<}+tt_1.
\end{aligned}
}
$$

This says that the common history can be factored out and $M$ evaluated only
on the three extensions.

The prime is important in the proof of closure. The fundamental calculation,
`R2_R2m'_pbm`, is:

$$
\boxed{
R2(P\parallel_M Q)
=
R2(P)\parallel_{R2'_m(M)}R2(Q).
}
$$

The public theorem nevertheless accepts an `R2m`-healthy merge. Since an
`R2`-healthy branch is also `R1`-healthy, its trace already extends the common
history. Consequently the extra branch guards in `R2m'` do not change this
parallel composition. This is `R2m_R2m'_pbm`:

$$
\boxed{
R2(P)\parallel_{R2_m(M)}R2(Q)
=
R2(P)\parallel_{R2'_m(M)}R2(Q).
}
$$

Together these bridge rules yield both closure forms:

$$
\boxed{
\begin{aligned}
P\text{ is }R2\land Q\text{ is }R2\land M\text{ is }R2m
&\Longrightarrow P\parallel_M Q\text{ is }R2,\\
P\text{ is }R2\land Q\text{ is }R2\land M\text{ is }R2m'
&\Longrightarrow P\parallel_M Q\text{ is }R2.
\end{aligned}
}
$$

These are `R2_par_by_merge` and `R2_par_by_merge'`. The other `R2`-level rules
are:

- `R2m_idem` and `R2m'_idem`: idempotence.
- `R2m_mono` and `R2m'_mono`: monotonicity.
- `R2m'_seq`: an `R2m'`-healthy merge followed by an `R2`-healthy relation
  remains `R2m'`-healthy.
- `R2m_skip_merge`, `R2m_disj`, and `R2m_conj`: `skip_m` healthiness and
  distribution through disjunction and conjunction.

#### `R2cm`: conditional history independence

The file also defines the merge counterpart of ordinary `R2c`:

$$
\boxed{
R2c_m(M)=
\mathcal N_h(M)
\mathbin{\triangleleft}tr_{<}\leq tr'\mathbin{\triangleright}
M.
}
$$

It normalises the histories when the merged trace extends the prior trace and
otherwise leaves $M$ unchanged. This allows history independence to be stated
without assuming `R1` globally. The file proves `R2cm_idem` and `R2cm_mono`,
but its parallel-closure theorem is formulated using `R2m` and `R2m'`.

#### `R3` and `R3m`: no activity while waiting

For comparison, ordinary `R3` acts on a reactive relation:

$$
\boxed{
R3(P)=II\mathbin{\triangleleft}wait
            \mathbin{\triangleright}P
     =(wait\land II)\lor(\neg wait\land P).
}
$$

If the predecessor is waiting, the relation behaves as identity. Otherwise it
uses $P$.

The merge counterpart tests the waiting flag in the shared prior observation:

$$
\boxed{
R3_m(M)=
skip_m\mathbin{\triangleleft}wait_{<}
      \mathbin{\triangleright}M.
}
$$

Since

$$
skip_m\equiv(\mathbf v'=\mathbf v_{<}),
$$

this can be read as

$$
\boxed{
R3_m(M)=
\bigl(wait_{<}\land\mathbf v'=\mathbf v_{<}\bigr)
\lor
\bigl(\neg wait_{<}\land M\bigr).
}
$$

When the prior observation is waiting, `skip_m` ignores both branch results
and copies the whole prior observation to the merged output. This includes
copying the prior `ok` value, but it is not a rule combining the left and
right `ok` values.

The corresponding rules are:

- `R3m_idem` and `R3m_mono`: idempotence and monotonicity.
- `R3_par_by_merge`:

  $$
  \boxed{
  P\text{ is }R3\land Q\text{ is }R3\land M\text{ is }R3m
  \Longrightarrow P\parallel_M Q\text{ is }R3.
  }
  $$

#### What the file gives you

For a quick application-oriented reading:

1. To obtain an `R1`-healthy parallel result, require only `M is R1m`.
2. To obtain an `R2`-healthy result, require `P is R2`, `Q is R2`, and
   `M is R2m`. The primed conditions are the strengthened forms used to expose
   and manipulate the three trace extensions in the proof.
3. To obtain an `R3`-healthy result, require `P is R3`, `Q is R3`, and
   `M is R3m`.
4. `R1m` and `R2m` additionally have `skip_m` and binary
   conjunction/disjunction laws; all the merge-healthiness operators in this
   file are idempotent and monotonic.
5. `SymMerge_R1_true` is the final small compatibility rule: postcomposing a
   symmetric merge with `R1(true)` preserves symmetry.

The theory deliberately proves the three reactive closure properties
separately. It does not define one composite reactive-design merge condition,
and it does not impose $ok'=ok_0\land ok_1$ or
$wait'=wait_0\lor wait_1$. Those protocol equations enter at the next layer.

### Reactive designs

`utp_rdes_parallel.thy` is where the design-control protocol is added. Its
`nmerge_rd0` construction abstracts the `ok` and `wait` observations from the
underlying merge, enforces trace growth, and sets the merged waiting flag.
`nmerge_rd1` then sets the merged termination flag:

$$
wait'=wait_0\lor wait_1,
\qquad
ok'=ok_0\land ok_1,
$$

`nmerge_rd` adds the appropriate behaviour when the prior observation is
waiting or has not started, and `merge_rd` composes the result with reactive
identity. The merge healthiness condition `RDM` applies `R2m` after hiding all
`ok` and `wait` observations of the underlying merge. Consequently the
user-supplied merge describes the substantive state-and-trace combination,
while the reactive-design normalisation owns the `ok`/`wait` protocol.

The resulting operator is still an instance of generic parallel-by-merge:

$$
P\parallel^{R}_{M}Q
=
P\parallel_{M_R(M)}Q.
$$

The lemma `SymMerge_merge_rd` shows that reactive-design merge normalisation
preserves symmetry. This is exactly the architecture useful for a future
angelic-process operator:

1. define a raw merge;
2. impose or construct the required healthiness conditions;
3. prove that normalisation preserves symmetry;
4. obtain commutativity from the generic swap argument;
5. prove closure of the process theory.

The later `rea_design_par` operator in `utp_rdes_parallel.thy` is different
from the parameterised parallel-by-merge operator. It is defined directly by
conjoining the reactive-design preconditions and commitments:

$$
P\parallel_R Q
=
RHS\bigl((pre_R(P)\land pre_R(Q))
\mathbin{\vdash}
(cmt_R(P)\land cmt_R(Q))\bigr).
$$

It should not be confused with the earlier operator
$P\parallel^R_M Q$.

## 12. Starting point for angelic processes

For an angelic process, a branch's final observation includes a set of possible
reactive states rather than one reactive state. Therefore, the important new
mathematical choice is how to lift a state-level merge $J$ to two choice
sets.

The raw AD-level definition `merge_ades`, written $M_{AD}(J)$, uses the lift

$$
z\in ac'
\iff
\exists p\in ac_0,\,q\in ac_1\bullet
J(\sigma,p,q,z).
$$

Thus the combined choice set contains every state obtainable by merging one
left choice with one right choice.  The outer design observations are combined
by

$$
ok' = ok_0 \land ok_1,
$$

so the combined computation terminates exactly when both branches terminate.

Applying `PBMH_ades` to the exact-image parallel replaces equality by image
inclusion. The public AD merge therefore uses

$$
\{z\mid \exists p\in ac_0,q\in ac_1\bullet J(\sigma,p,q,z)\}
\subseteq ac'.
$$

This is `merge_ades_up`, written $M_{AD}^{\uparrow}(J)$. The theorem
`PBMH_ades_par_raw` proves that it is exactly the `PBMH_ades` normal
form of the raw semantics. AP parallel reuses this healthy definition through
the abbreviation `merge_AP`, written $M_{AP}(J)$.

Commutativity can be developed before AP closure. If the lifted merge satisfies

$$
\mathit{swap}_m;M_{AP}=M_{AP},
$$

then the generic separator calculation immediately gives

$$
P\parallel_{M_{AP}}Q
=
Q\parallel_{M_{AP}}P.
$$

No premises saying that $P$ and $Q$ are `AP`-healthy are needed for this
structural equality. Such premises become relevant later, when proving that
the parallel result is itself `AP`-healthy.

### Layered mechanisation roadmap

#### AD foundation

- [x] Heterogeneous `par_by_merge_comm` in `utp_concurrency.thy`, with the
  direct symmetry premise `swap\<^sub>m ;; M = M`.
- [x] `merge_ades` in `angelic-designs/utp_ades_parallel.thy`: lifts a
  state-level merge $J$ to choice sets by exact image and conjoins the
  branch termination flags.
- [x] `merge_ades_up`: the public upward-closed merge (image inclusion);
  `PBMH_ades_par_raw` identifies it as the `PBMH_ades` normal form
  of raw parallel.
- [x] The notation $P\parallel^{AD}_{J}Q$ and commutativity for symmetric
  merges (`merge_ades_up_swap`, `ades_par_comm`).
- [x] Closure: unconditional `PBMH_ades` closure, and `A` closure for
  `A`-healthy operands and a total merge (`ades_par_A_closure`).
- [x] `A2` closure at the choice-set level: `ades_par_rel_A2_rel_closure`
  proves `A2_rel` closure of `ades_par_rel` (the composition shape shared by
  the postcondition and negated precondition of AD parallel) for
  `A2_rel`-healthy operands and a functional merge
  (`A2j`); no totality is needed.
- [x] Design-level assembly: `ades_par_rdesign` gives the relational
  design normal form of AD parallel for H-healthy operands (commitments
  compose; a failure pairs one branch failure with an arbitrary observation
  of the other). From it, `ades_par_A2_closure` (H- and `A2`-healthy operands,
  functional `A2j` merge) and
  `ades_par_A3_closure` (H-healthy operands, `A3j` merge — no
  operand conditions beyond H) follow by design calculus.
- [x] `A3` at the choice-set level: totality and functionality are not
  enough (`ades_par_rel_A3_rel_counterexample`: under the total, functional,
  surjective right-projection merge `ades_right_merge`, one branch failure
  floods every singleton and `A3_rel` is lost). The merge condition that works
  is `A3j` — some singleton is not an exact merge image at every prior state.
  `ades_par_rel_conj_A3_rel_closure` establishes `A3_rel` for the conjunction
  of the two negated failure compositions. The excluded singleton's element
  may occur in larger images, so surjectivity alone does not rule out `A3j`. An alternative is
  `ac'`-independent (normal) preconditions, which make `A3_rel` trivial.
- [x] A3 characterisation: under `A0j`, `ades_par_A3_closure_iff_A3j` makes `A3j`
  necessary and sufficient for A3 of every parallel of H-healthy operands.
- [x] Conditional associativity (`ades_par_assoc`), assuming
  `swap_m ;; j = j` and `AssocMerge j`.
- [x] Merge-condition kit: totality survives enlargement (`A0j_enlarge`)
  and functionality survives restriction (`A2j_restrict`). `A3j` need not
  survive restriction, because a larger image can become a singleton.
  `skip_m` is functional and satisfies `A3j` on state spaces with two or
  more elements
  (`skip_merge_A2j`, `skip_merge_A3j`). The counterexamples delimit weaker
  premise packages: `ades_right_merge_not_A3j` shows that totality and
  functionality do not imply singleton-image exclusion, while
  `ades_par_rel_A2_rel_counterexample` shows that the total two-valued
  `ades_univ_merge` breaks `A2_rel` closure. These counterexamples are separate
  from the qualified A3 necessity theorem above.
- [x] `A2` bridging: `A2_components_iff` characterises `A2` healthiness
  of H-healthy designs by `A2_rel` healthiness of the negated precondition
  and postcondition. The premises of `ades_par_A2_closure` are H and A2
  healthiness of both operands and functionality `A2j j` of the merge.
- [x] Normal operands: `ades_par_normal_A3_closure` gives `A3`
  closure for `N`-healthy operands under an arbitrary merge (the
  precondition's choice-set independence transfers through the
  composition), and the composition is itself normal
  (`ades_par_normal_H3_closure`, `ades_par_N_closure`).

#### RAD layer

- [x] Add `utp_rad_parallel.thy`, reusing $M_{AD}^{\uparrow}$ rather than
  defining a second choice-set lift.
- [x] Define the merge-healthiness conditions needed for RAD closure, using
  `R1m`, `R2m`, `R3m`, and `RDM` as structural guides rather than copying
  their standard reactive-design types directly.  The conditions `RA1m`,
  `RA1m'`, `RA2m`, `RA2m'`, and `RA3m` constrain the state-level merge
  $J$ on `rad_state`, where the angelic lift keeps all reactive content;
  the composite is `RADM = RA2m ∘ RA3m`, with `RA1m` absorbed by `RA2m`.
  Unlike `RDM`, no `ok`/`wait` quantification is needed: the lift combines
  `ok` itself, and the waiting flag is genuine `rad_state` state whose
  waiting-prior case `RA3m` sends to `skip_m`.  Each condition preserves
  the symmetry equation `swap_m ;; J = J` (`RA1m_swap` … `RADM_swap`), and
  `RA3m` preserves `A0j` (`RA3m_A0j`); totality of `RA1m`-
  and `RA2m`-healthy merges must be established per concrete merge.
- [x] Prove RAD closure.  The raw operator $P\parallel^{AD}_{J}Q$ is
  `RA1`-closed (`RA1m`-healthy total merge, `RA1`-healthy operands) and
  `RA2`-closed (`RA2m`-healthy merge, `RA2`-healthy operands), but **not**
  `RA3`-closed: at an unstarted waiting observation the composition forces
  the prior state into the combined choice set, whereas `II_Rac` only
  requires some trace-extending choice
  (`ades_par_RA3_counterexample`, with `II_Rac` operands and the
  `skip_m` merge).  The RAD operator therefore wraps the composition in
  `CSPA1`, mirroring the divergence disjunct of `nmerge_rd`:

  $$P\parallel^{RAD}_{J}Q = CSPA1(P\parallel^{AD}_{J}Q).$$

  Started observations are unaffected.  The wrapped operator is
  commutative for symmetric merges and closed under `RA1`, `RA2`, `RA3`,
  `CSPA1`, `CSPA2`, `PBMH_ades`, and `RAD` itself
  (`rad_par_RAD_closure`: `RAD`-healthy operands, `RADM`-healthy
  total merge).  Supporting facts: `H2` commutes with `RA1`/`RA2`/`RA3`/
  `CSPA1`, RAD-healthy predicates are `CSPA2`-healthy (`RAD_is_CSPA2`),
  and `RA`-healthy predicates project to `RA1`/`RA2`/`RA3`
  (`RA_is_RA1` … `RA_is_RA3`).
- [x] Merge-condition preservation: `RA3m` preserves `A2j` and `A3j`
  (`RA3m_A2j`, `RA3m_A3j` — the waiting branch is `skip_m` and a waiting
  prior's flag can be flipped), and `RA2m` preserves `A0j`, `A2j`, and
  `A3j` (`RA2m_A0j`, `RA2m_A2j`, `RA2m_A3j` — prepending the prior trace
  inverts trace differencing).
- [x] Strict trace growth `RA1sm` (a Productive-style conjunctive
  healthiness condition, idempotent and monotonic, absorbed by `RA1m`)
  gives `A3j` outright (`RA1sm_A3j`): the prior state is always a blind
  spot. This is a separate sufficient route to `A3j`, not a strengthening
  available to `RADM`: `RA3m` restores the prior state on waiting inputs, so
  `RA1sm` and `RADM` cannot have a common fixed point.
- [x] `A2`/`A3` closure of the wrapped operator: `CSPA1` adds an
  A2-healthy divergence disjunct and preserves the design components, giving
  commutation with `A2` and `A3` (`A2_CSPA1_commute`, `A3_CSPA1_commute`),
  and the AD closure theorems lift (`rad_par_A2_closure`,
  `rad_par_A3_closure`, `rad_par_normal_A3_closure`).
  The premises are H- or N-healthiness of the operands; restating them
  for RAD-healthy (non-H1) operands remains open.
- [ ] Prove a correspondence with standard reactive-design
  parallel-by-merge.

#### AP layer

- [x] `merge_AP` and $P\parallel^{AP}_{J}Q$ are abbreviations of the AD-level
  semantics, specialised to reactive states.
- [x] `merge_AP_swap` and `ap_par_comm`, proving
  $\mathit{swap}_m;M_{AP}(J)=M_{AP}(J)$ whenever
  $\mathit{swap}_m;J=J$.
- [x] Add `ap_par_eval`, a thin AP-specialised form of
  `ades_par_eval`, so the first AP algebraic laws can use the public
  notation without reopening the AD choice-set lifting.
- [x] Prove an explicit `top_AP_design` normal form for
  $\top_{AP}=AP(false)$, together with any small waiting-case
  simplification needed to combine an AP-healthy operand with an
  `RA3m`-healthy merge.
- [x] Prove the left and right Miracle-zero laws directly from the evaluation
  theorem.  Neither direction needs merge symmetry, and this short route does
  not depend on the RAD closure theorem, AP closure, or the RAD/AP parallel
  correspondence (`top_AP_parallel_left_zero` and
  `top_AP_parallel_right_zero`).
- [x] Introduce `AP_feasible`, requiring every started, non-waiting input to
  admit an `ok'` branch result, and use it with `Chaos_AP_design` to prove the
  qualified left and right Chaos-zero laws
  (`Chaos_AP_parallel_left_zero` and `Chaos_AP_parallel_right_zero`).  The
  qualification is essential: an unconditional Chaos-zero law would conflict
  with the Miracle-zero law when the other operand is Miracle.  The distinct
  name also avoids confusion with reactive `Productive`, which requires
  strict trace growth.
- [ ] Prove `AP_feasible` for the principal process constructors and closure
  under the AP operators for which it is preserved.
- [ ] Prove that AP-healthy operands yield an AP-healthy parallel result.
- [ ] Prove the RAD/AP correspondence for parallel and investigate `NDAP`
  closure.
- [ ] Add a concrete synchronising merge and its conditional associativity
  theorem.

## 13. Compact mental model

The entire construction can be remembered as

$$
\boxed{
(P\parallel_M Q)(\sigma,z)
\iff
\exists p,q\bullet
P(\sigma,p)\land Q(\sigma,q)\land M(\sigma,p,q,z)
}
$$

with the following division of responsibility:

$$
\underbrace{P,Q}_{\text{produce branch results}}
\quad+
\underbrace{\parallel_s}_{\text{keep the results separate}}
\quad+
\underbrace{M}_{\text{define the concurrency semantics}}.
$$

Symmetry, associativity, trace behaviour, waiting behaviour, and state
combination are therefore primarily properties of the merge relation.
