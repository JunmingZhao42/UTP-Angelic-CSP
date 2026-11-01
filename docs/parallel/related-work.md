# Related work and semantic limits

[Parallel by merge](README.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md)

This note merges three research notes from 15–16 October 2026: the literature
assessment, the RD divergence investigation and the survey of non-UTP Miracle
semantics. It was updated on 1 November 2026 for the current merges. *Our
deduction* marks hand derivations; they are not Isabelle lemmas. Lemmas are
cited by name, with links to their theory files rather than to line numbers.

## Summary

- D and AD parallel compose independent computations, merge their final states,
  and treat nontermination catastrophically, as total-correctness designs and
  CSP failures–divergences semantics do. The reading is strongest when `j` is mergeable.
- They do not model CCS bisimulation or communicating CSP parallel. A
  communication needed to reach divergence cannot be skipped because a branch
  diverges when run alone.
- After a branch diverges the final observation is unrestricted, but the branch
  states must still have some merged state. RD has the same clause plus a
  trace-prefix condition.
- `Chaos ∥ Miracle = Miracle` is proved for D and RD; for AD it was checked in
  scratch against the 16 October merge and needs rechecking. At active starts,
  generic parallel-by-merge forces this: Miracle has no active observation, so
  no merge can supply one.
- The papers below support the semantic policy. They do not establish this
  repository's AD lifting or its laws, which come from the proofs here.

## Divergence across D, AD and RD

At an active start (`ok(s0)`, and also `¬wait(s0)` for RD), select a branch pair
in which at least one branch diverges:

| Operator | Requirement on the divergent pair | `Chaos ∥ Miracle` |
| --- | --- | --- |
| D | `∃y. j(s0,sL,sR,y)`; final observation unrestricted | Miracle, for every `j` |
| AD | Both branch choice sets nonempty and every pair of branch states has a merged state; final flag and choice set unrestricted | Miracle (scratch check; recheck pending) |
| RD with `M is RDM` | `∃u. M(s0,sL,sR,u) ∧ tr(u) ≤ tr(s)` | Miracle |

Sources: [`merge_des_expand`](../../deps/UTP-Designs/utp_des_parallel.thy),
[`merge_ades_obs`](../../angelic-designs/utp_ades_parallel.thy) and
[`merge_rd_eval`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel_laws.thy).
The installed Miracle laws are `des_par_miracle` for D, and
`Miracle_parallel_Chaos` and `Chaos_parallel_Miracle` for RD. The AD instances
were checked in scratch on 16 October 2026, before the 28 October AD merge
change; they need rechecking before installation (PLAN Stage 1).

The RD clause keeps merge feasibility and a trace-prefix requirement; it does not
impose `M(s0,sL,sR,s)` on the final observation. A PIDE scratch (16 October 2026,
not installed) checked three consequences of `merge_rd_eval`:

1. If the wrapper admits `s` for a divergent pair, it admits every `s'` with
   `tr(s) ≤ tr(s')`, whatever the other fields of `s'`.
2. `M = false` is RDM-healthy, and its wrapper rejects every active merge
   observation. RDM alone therefore gives no universal Chaos law.
3. A sufficient condition for Chaos absorption on feasible operands is an
   initial-trace divergence witness: at each active `s0`, accepted branch
   observations, at least one with `ok = False`, and a merged witness `u` with
   `tr(u) = tr(s0)`. The exact criterion is now `rdes_parallel_Chaos_iff`.

Upstream defines `M_R(M) = N_R(M) ;; II_R` in
[`utp_rdes_parallel.thy`](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy);
the appended Skip supplies the divergence continuation above. This project's
local `RADm` merge differs: it keeps a final refusal constraint after divergence
(see the [RAD guide](RAD.md)).

### Why changing the merge cannot make Chaos absorb Miracle

Every layer uses generic parallel by merge, [`par_by_merge`](../../deps/UTP/utp_concurrency.thy),
unfolded by `des_par_by_merge_unfold` and `ades_par_by_merge_eval`:

```text
(P ∥[N] Q)(s0,s) = ∃sL sR. P(s0,sL) ∧ Q(s0,sR) ∧ N(s0,sL,sR,s)
```

If `Q` has no observation at `s0`, this is false for every `N`, including a
merge that drops all constraints after divergence. Miracle has no active
observation, so no merge gives `Chaos ∥ Miracle = Chaos`. Two distinct elements
also cannot both be universal zeros, since their composition would equal both.
Universal Chaos absorption therefore needs a restricted Miracle law and a
different way of combining operands, not just a different merge.

## UTP sources

| Primary source | Published result and premises | Relevance |
| --- | --- | --- |
| Ye, Foster, Woodcock, *Automated Reasoning for Probabilistic Sequential Programs with Theorem Proving* (RAMiCS 2021), [§6.2, pp. 8–9](https://pure.york.ac.uk/portal/files/72526604/RAMICS2021_rev20210818.pdf#page=9) | Ordinary-design parallel with a distribution merge `prob' = 0.prob +r 1.prob`. For normal operands `p ⊢ P` and `q ⊢ Q`, the calculated precondition is `(p ∨ (q ∧ ¬Pre(Q))) ∧ (q ∨ (p ∧ ¬Pre(P)))`; `Pre` is relational domain. | Supports the feasibility-sensitive treatment of divergence: a failed assumption propagates when the other operand has behaviour. Their merge is total, so this is evidence for the resulting law, not for our lifting with partial merges. |
| Foster et al., *Unifying Theories of Reactive Design Contracts*, [Definition 6.21 and Theorem 6.25, pp. 33–34](https://arxiv.org/pdf/1712.10233#page=33) | Builds an outer merge from `okOut = (okL ∧ okR)`, a disjunction of branch waiting flags, and an inner merge, then applies reactive healthiness, including `RD3`. Closure requires SRD operands and an RDM inner merge: history independence and independence from `ok`, `wait` and their decorations. | Supports separating control flags from the semantic merge and completing it by healthiness; the D merge mirrors this with `;; II_D`. |
| Foster et al., *Automated Verification of Reactive and Concurrent Programs by Calculation* (2021), [Theorem 7.9, Example 7.36, Theorem 7.41, PDF pp. 25, 33–34](https://arxiv.org/pdf/2007.13529#page=25) | Miracle absorbs reactive-design parallel. Chaos absorption needs more premises; Theorem 7.41 assumes independent state name sets and an NCSP- and CACC-healthy other operand. CACC supplies an empty-trace quiescent observation. | Our Miracle exception matches published UTP semantics. Ordinary feasibility and reactive CACC are different conditions; neither theorem lets its premises be dropped. |
| Oliveira, Cavalcanti, Woodcock, *A UTP Semantics for Circus*, [§3.1.6, pp. 10–11](https://www.cs.york.ac.uk/circus/publications/papers/07-ocw.pdf#page=10) | A branch contributes divergence only along a trace compatible with the other branch's synchronisations. States merge in the terminating case; intermediate observations record waiting and refusals. | Supports dropping final-state obligations after divergence while keeping the compatibility needed to reach it. A guard around every reactive observation would lose this distinction. |

### Pinned Circus result

The pinned `utp-main` Circus theory builds its parallel from the RD merge:

| Source | Role |
| --- | --- |
| [`CSPInnerMerge_RDM`, lines 49–50](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L49) | The inner Circus merge `N_C ns1 cs ns2` is RDM-healthy. |
| [`CSPMerge`, lines 130–131](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L130) | `M_C ns1 cs ns2 = M_R(N_C ns1 cs ns2) ;; Skip`. |
| [Parallel syntax translation, lines 841–844](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L841) | Circus parallel is generic parallel-by-merge using `M_C`. |
| [`parallel_miracle`, lines 1471–1473](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L1471) | For `P is NCSP`, Miracle absorbs Circus parallel, via `Miracle_parallel_left_zero`. |
| [`Chaos_par_zero`, lines 1547–1549](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L1547) | Chaos absorbs when `P is NCSP`, `P is CACC`, and `ns1 ⋈ ns2`. |

`CACC(P) = P ∨ Accept`, and healthiness requires `CACC(P) = P`. `Accept` supplies
a quiescent observation with empty trace contribution and all events enabled
([`Accept` and `CACC`, lines 1482–1489](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L1482)).
The 2021 paper observes that Miracle, Skip and assignments are not CACC, so its
Chaos-zero Theorem 7.41 excludes Miracle and does not conflict with the
Miracle-zero Theorem 7.9 ([pp. 33–34](https://arxiv.org/pdf/2007.13529#page=33)).
CACC is sufficient, not necessary: its failure for Skip does not refute the zero
law for Skip.

### Ordinary-design precondition (our deduction)

Write normal operands `D = p ⊢ R` and `E = q ⊢ S`, where `p, q` depend only on
the initial state and `R, S` contain no control flags. Let
`dom(R)(s0) = ∃x. R(s0,x)`, and similarly for `S`. A divergent pair accepts every
output when its branch states have a merged state (`des_par_diverge`). For
mergeable `j`, that is `∀s0 x y. ∃z. j(s0,x,y,z)`, such a pair exists at a
started state exactly when

```text
bad = (¬p ∧ (¬q ∨ dom(S))) ∨ (¬q ∧ (¬p ∨ dom(R)))
```

Negating `bad` gives

```text
pre = (p ∨ (q ∧ ¬dom(S))) ∧ (q ∨ (p ∧ ¬dom(R)))
post(s0,z) = ∃x y. R(s0,x) ∧ S(s0,y) ∧ j(s0,x,y,z)
D ∥D[j] E = pre ⊢ post
```

This recovers the Ye–Foster–Woodcock precondition, with `R, S` as their
postconditions. If both postconditions have a result at every initial state,
`pre` reduces to `p ∧ q`; an infeasible operand breaks that simplification,
hence the Miracle exception. For partial `j`, each disjunct of `bad` also needs
a merge witness for the chosen branch states. The first becomes
`¬p ∧ ∃y. (¬q ∨ S(s0,y)) ∧ (∃x z. j(s0,x,y,z))`.

### Partial merges and associativity (our deduction)

`des_par_assoc_state` assumes `j is SymMerge`, `AssocMerge j` and `mergeable j`.
These premises are sufficient, not a proved minimal set. Mergeability stops an
intermediate join from turning feasible operands into Miracle. Take the
equality merge `j(x,y,z) ≡ x = y ∧ z = x` on distinct states `0, 1`, and let
`C0, C1` terminate in those states:

```text
(Chaos ∥j C0) ∥j C1 = Chaos
Chaos ∥j (C0 ∥j C1) = Chaos ∥j Miracle = Miracle
```

The equality merge is relationally associative but not mergeable. This explains
the extra premise. It does not mean CSP synchronisation must accept every pair
of complete traces: CSP records blocked interaction through prefixes and
refusals, which the ordinary final-state layer lacks.

## CSP

Van Glabbeek's *A Branching Time Model of CSP*, §3 and Table 2 (pp. 3–6),
presents failures–divergences semantics with flooding after divergence and
states, for a fixed synchronisation set `A`:

```text
P ||A div = div
P ||A (Q ||A R) = (P ||A Q) ||A R
```

Here `div` performs an infinite internal computation; the paper also studies a
finer model that preserves behaviour around divergence
([primary source](https://cgi.cse.unsw.edu.au/~rvg/pub/Roscoe.pdf#page=3)).
The carrier requires `(ε, ∅) ∈ F` (N1, p. 3), so it has no empty behaviour set
representing infeasibility. Our inference: the law does not determine
`div ∥ Miracle`, which needs an extended carrier and a definition of parallel on
the added element.

Roscoe's *The Theory and Practice of Concurrency*, §8.3.2 (printed p. 207),
builds a parallel divergence from **compatible component traces**, one of which
reaches divergence, then allows arbitrary continuation
([primary source](https://www.cs.ox.ac.uk/ucs/tpc2010.pdf#page=223)). His
`Chaos(A)` is divergence-free (p. 85, footnote 4); `div` is the counterpart of
design Chaos. Likewise FDR's `DIV` diverges immediately, whereas `CHAOS(A)` can
perform events in `A` or deadlock
([built-in processes](https://cocotec.io/fdr/manual/cspm/prelude.html#processes),
[failures–divergences refinement](https://www.cs.ox.ac.uk/projects/concurrency-tools/fdr-2.94-html-manual/fdr2manual_5.html)).
The UTP Chaos zero law concerns catastrophic divergence, not FDR `CHAOS(A)`.

Our deduction from van Glabbeek's Table 1 transition rules:

```text
div ||{a} STOP =FD div
(a → div) ||{a} STOP =FD STOP
```

In the second line the required `a` cannot synchronise, so the divergence is
unreachable. Releasing final-state guarantees suits the D/AD layer. A reactive
lifting for RAD/AP must keep divergence, waiting and deadlock distinct and keep
the communication history leading to divergence compatible.

## CCS

Tian and Sangiorgi, *Unique Solutions of Contractions, CCS, and their HOL
Formalisation* (EXPRESS/SOS 2018), §2, Figure 1 and Definition 2.1
(pp. 123–124), give independent component transitions, synchronisation on
complementary actions, and weak bisimulation
([primary source](https://arxiv.org/pdf/1808.08652#page=3)). These rules keep
transition structure; they do not replace a divergent composition by an
unrestricted process.

Our deduction: with `Ω = τ.Ω`, the process `Ω | a.0` has transitions
`--τ--> Ω | a.0` and `--a--> Ω | 0`, but no `b` transition even after internal
steps. It is therefore not weakly bisimilar to a process allowing arbitrary
visible actions; weak bisimulation can even identify `Ω` with `0`. CCS supports
propagating internal activity, not catastrophic divergence. Walker studies
divergence-sensitive bisimulation with convergence predicates in *Bisimulation
Equivalence and Divergence in CCS* (1987; journal version 1990;
[report](https://www.lfcs.inf.ed.ac.uk/reports/87/ECS-LFCS-87-29/)). Any
comparison of divergence laws must name its equivalence.

## Semantics outside UTP with Magic or Miracle

These sources admit miraculous specifications. Their constants and composition
operators need separate interpretation; the name `Magic` alone does not
establish correspondence with UTP Miracle or CSP failures–divergences semantics.

| Framework and source | Treatment | Scope |
| --- | --- | --- |
| Ian J. Hayes, Larissa A. Meinicke and Naso Evangelou-Oost, *Restructuring a Concurrent Refinement Algebra* (2024), [§§2–2.2](https://arxiv.org/pdf/2405.05690#page=2) | `⊥` is the everywhere infeasible command, called magic/miracle; `⊤` is irrecoverable abort, allowing every behaviour. The paper states `⊤ ∥ c = ⊤` for every command, including `c = ⊥` (Equation 10). | A direct example of abort dominating miracle in parallel. Its separately named `chaos` is the unit of weak conjunction and must not be substituted for abort. |
| Ralph-Johan Back and Joakim von Wright, *Interpreting Nondeterminism in the Refinement Calculus* (1996), [§§1.1–1.2, 2.6](https://doi.org/10.14236/ewic/RW1996.1) | Predicate transformers include `magic(q) = true` and `abort(q) = false`, the refinement top and bottom. Guards satisfy `[false] = magic`. | Their user–system reading describes magic as waiting/deadlock (§2.6). Evidence of an explicit miraculous construct, not identification with CSP `STOP`. |
| Yifeng Chen, *Cumulative Computing* (2003), [§§3–4](https://doi.org/10.1016/S1571-0661(03)50002-0) | Commands are sets of cumulations: `magic = ∅`, `chaos = X`. Generic parallel is intersection. Section 4 develops a CSP/Timed CSP case study in which alphabet restriction can yield magic. | For generic intersection `magic ∩ chaos = magic` is immediate. This does not establish the corresponding law for the specialised CSP parallel operator. |
| Viorel Preoteasa and Stavros Tripakis, *Refinement Calculus of Reactive Systems*, [§3.3](https://arxiv.org/pdf/1406.6035#page=6) and [§4.2, Definition 16 and Theorem 17](https://arxiv.org/pdf/1406.6035#page=11) | Monotonic property transformers include `Magic(q) = ⊤` and `Fail(q) = ⊥`. Magic is unimplementable. Guarded systems exclude miraculous behaviour; Fail remains guarded. | These transformers map properties of output traces to properties of input traces. Including Magic in the semantic universe differs from admitting it in the guarded subclass. |

The later paper by Preoteasa, Dragomir and Tripakis, *The Refinement Calculus of
Reactive Systems*, states non-miraculousness as `S(⊥) = ⊥` and defines guarded
transformers as `{in(r)} ◦ [r]`; Magic is in the general relational class but
fails that condition ([§4.2.2, Definition 19](https://arxiv.org/pdf/1710.03979#page=20)).

The 2024 algebra requires distribution over **nonempty** nondeterministic
choice only: the empty choice would force miracle absorption and conflict with
abort absorption. Colvin, Hayes and Meinicke's earlier *Designing a Semantic
Model for a Wide-Spectrum Language with Concurrency* (2016,
[§4.4](https://arxiv.org/pdf/1609.00195#page=10)) instead lets infeasibility
dominate abort in parallel. Giving abort priority over Miracle is therefore a
coherent choice with precedent, not a proved correspondence with the RD alphabet
or CSP.

### RCRS parallel product (our deduction)

For monotonic property transformers, the later RCRS paper defines the product of
parallel input/output components, with `Fail(q) = ∅`
([Definition 9](https://arxiv.org/pdf/1710.03979#page=15),
[Definition 13](https://arxiv.org/pdf/1710.03979#page=17)):

```text
(S ⊗ T)(q) = {(x,u) | ∃p,p'. p × p' ⊆ q ∧ x ∈ S(p) ∧ u ∈ T(p')}
```

From these definitions:

```text
S ⊗ Fail = Fail = Fail ⊗ S
Magic ⊗ Fail = Fail
(Magic ⊗ S)(q) = X^ω × S(⊤)
```

The first two hold because no witness belongs to `Fail(p')`. For the last,
monotonicity gives the forward inclusion and `p = ∅`, `p' = ⊤` the reverse;
`X` is Magic's input alphabet. So `Magic ⊗ S = Magic` when `S(⊤) = ⊤`, the
paper's input-receptiveness condition ([§4.1](https://arxiv.org/pdf/1710.03979#page=15)).
Failure absorbs unconditionally and Magic conditionally. No correspondence
between this Fail and CSP catastrophic divergence is established.

## Two targets for a different operator

1. **Standard CSP correspondence on a suitable process class.** Keep compatible
   histories and divergence flooding, and prove that immediate divergence has an
   initial-trace witness against every process in the class. The Circus theorem
   gives one sufficient set of premises. Miracle lies outside the standard
   failures–divergences carrier, so this target need not override it.
2. **Universal Chaos absorption on a carrier containing Miracle.** Change how
   parallel combines operand behaviours, or their representation, so that
   divergence can contribute without a complete observation from an infeasible
   counterpart; guarding the merge cannot do this. Specify the interaction with
   Miracle, for example Miracle absorption only for suitable operands, then prove
   healthiness, symmetry, associativity and correspondence. Divergence must still
   keep the history before it reachable: treating every independently divergent
   branch trace as globally reachable is unsound for synchronising parallel.

## Evidence boundary

The cited PDFs, the FDR documentation and the pinned Circus theory were read
directly on 15–16 October 2026; that Circus revision was not rebuilt. The
Back–von Wright and Chen statements were checked in indexed copies
([Back–von Wright](https://www.researchgate.net/publication/2483621_Interpreting_Nondeterminism_in_the_Refinement_Calculus),
[Chen](https://www.researchgate.net/publication/242284720_Cumulative_Computing));
direct publisher access was unavailable. No Isabelle proof of correspondence with
CSP, CCS or the published operators was attempted. Scratch checks are labelled
where cited and are not installed.
