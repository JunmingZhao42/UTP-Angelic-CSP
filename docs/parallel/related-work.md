# Related work and semantic limits

[Parallel by merge](README.md) · [D](D.md) · [AD](AD.md) · [RAD](RAD.md)

These sources compare semantic choices. They do not establish correspondence
between the published operators and this repository's lifting.

## Divergence and infeasibility

[D](D.md#state-merge-lifting) and [AD](AD.md#lifting-a-state-merge) release
the final observation after divergence but retain branch and merge feasibility.
Completed RD parallel additionally requires a merged witness whose trace is
a prefix of the final trace, through the completed
[merge_rd](../../deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L132).
The pinned [rdes_parallel_Chaos_iff](../../deps/UTP-Reactive-Designs/utp_srdes_parallel_laws.thy#L495)
gives the exact Chaos criterion for SRD operands and an RDM input merge.

Every generic parallel selects an observation from both operands. If one
operand has no started observation, changing the merge cannot supply it.
Thus Miracle absorbs Chaos in the installed [des_par_miracle](../../deps/UTP-Designs/utp_des_parallel.thy#L494) and
[ades_par_miracle](../../angelic-designs/utp_ades_parallel.thy#L700) laws. Universal Chaos absorption on a carrier containing
Miracle would require a different operand-combination rule.

The [RAD choice-set lift](RAD.md#reactive-merge-lifting) applies the supplied
ordinary merge directly. Reactive skip completion belongs to the selected
ordinary merge construction; see [RD lifting](RD.md#lifted-merge-and-laws).

## UTP sources

- Ye, Foster and Woodcock,
  [*Automated Reasoning for Probabilistic Sequential Programs with Theorem Proving*,
  §6.2](https://pure.york.ac.uk/portal/files/72526604/RAMICS2021_rev20210818.pdf#page=9)
  calculates ordinary-design parallel with a total distribution merge.
  Its precondition accounts for whether the other operand has behaviour;
  it does not justify dropping feasibility for partial merges.
- Foster et al.,
  [*Unifying Theories of Reactive Design Contracts*, Definition 6.21 and
  Theorem 6.25](https://arxiv.org/pdf/1712.10233#page=33)
  separates control flags from an inner merge and applies reactive healthiness.
  Closure uses SRD operands and an RDM inner merge.
- Foster et al.,
  [*Automated Verification of Reactive and Concurrent Programs by Calculation*,
  Theorems 7.9 and 7.41](https://arxiv.org/pdf/2007.13529#page=25)
  gives Miracle absorption and a conditional Chaos-zero law.
  The latter requires NCSP, CACC and independent state name sets;
  CACC supplies an empty-trace quiescent observation.
- Oliveira, Cavalcanti and Woodcock,
  [*A UTP Semantics for Circus*, §3.1.6](https://www.cs.york.ac.uk/circus/publications/papers/07-ocw.pdf#page=10)
  requires traces compatible with synchronisation before divergence.
  Releasing final-state guarantees does not remove that history requirement.

The pinned Circus implementation agrees:
[`Chaos_par_zero`](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L1547)
requires NCSP, CACC and independent names;
[`parallel_miracle`](https://github.com/isabelle-utp/utp-main/blob/07cb0c256a90bc347289b5f5d202781b536fc640/theories/circus/utp_circus_parallel.thy#L1471)
requires NCSP. These are different premise sets: CACC excludes Miracle.

### Calculations, not installed correspondence theorems

For normal designs `p ⊢ R`, `q ⊢ S` and mergeable `j`, a hand calculation gives

```text
pre = (p ∨ (q ∧ ¬dom(S))) ∧ (q ∨ (p ∧ ¬dom(R)))
post(s,s') = ∃sL sR. R(s,sL) ∧ S(s,sR) ∧ j(s,sL,sR,s')
```

This recovers the feasibility-sensitive precondition above. If both
postconditions are total, it reduces to `p ∧ q`; partial merges need
additional merge witnesses.

Partial merges also explain the mergeability premise in D associativity.
For the equality merge `j(s,sL,sR,s') ≡ sL = sR ∧ s' = sL`, let C0 and C1
terminate at distinct states. Then the hand calculation is

```text
(Chaos ∥D[j] C0) ∥D[j] C1 = Chaos
Chaos ∥D[j] (C0 ∥D[j] C1) = Miracle.
```

The merge is symmetric and relationally associative but not mergeable.
This is not a claim that every partial merge fails associativity.

## CSP and CCS

Van Glabbeek's [*A Branching Time Model of CSP*, §3 and Table 2](https://cgi.cse.unsw.edu.au/~rvg/pub/Roscoe.pdf#page=3)
has divergence flooding and associative parallel. Its failures carrier
requires an initial failure observation, so it does not settle how parallel
should treat an added infeasible Miracle.

Roscoe's [*The Theory and Practice of Concurrency*, §8.3.2](https://www.cs.ox.ac.uk/ucs/tpc2010.pdf#page=223)
constructs divergence from compatible component traces.
Immediate divergence can propagate against STOP, while a divergence reachable
only after an event blocked by STOP cannot.
FDR's [`DIV` and `CHAOS(A)`](https://cocotec.io/fdr/manual/cspm/prelude.html#processes)
are distinct: the former matches catastrophic divergence; the latter allows
events or deadlock.

CCS keeps transition structure and uses bisimulation
([Tian and Sangiorgi, §2](https://arxiv.org/pdf/1808.08652#page=3)).
An internally divergent component does not grant arbitrary visible actions.
A comparison therefore has to specify its equivalence; see also
[Walker on divergence-sensitive CCS bisimulation](https://www.lfcs.inf.ed.ac.uk/reports/87/ECS-LFCS-87-29/).

## Semantics outside UTP with Miracle

- Hayes, Meinicke and Evangelou-Oost,
  [*Restructuring a Concurrent Refinement Algebra*, Equation 10](https://arxiv.org/pdf/2405.05690#page=2),
  makes abort absorb every parallel operand, including magic.
  Its `chaos` is instead the unit of weak conjunction. Distribution is over
  nonempty nondeterministic choice; including empty choice would force magic absorption.
- Back and von Wright,
  [*Interpreting Nondeterminism in the Refinement Calculus*, §§1.1–1.2, 2.6](https://doi.org/10.14236/ewic/RW1996.1),
  has `magic(q) = true` and `abort(q) = false`. Its interpretation of magic
  does not establish a correspondence with CSP STOP.
- Chen's [*Cumulative Computing*, §§3–4](https://doi.org/10.1016/S1571-0661(03)50002-0)
  uses `magic = ∅`, `chaos = X` and intersection as generic parallel.
  Magic absorption follows for that operator, not automatically for the
  specialised CSP operator.
- Preoteasa, Dragomir and Tripakis,
  [*The Refinement Calculus of Reactive Systems*, Definitions 9, 13 and 19](https://arxiv.org/pdf/1710.03979#page=15),
  distinguishes Magic from guarded, non-miraculous transformers.
  From its parallel-product definition, Fail absorbs unconditionally and
  Magic absorbs an input-receptive partner. This is a hand deduction, not
  a proved identification of Fail with CSP divergence.

Abort taking priority over Miracle is therefore a possible semantic choice.
It is not obtained by changing only the merge in the current operator.

## Evidence boundary

The literature and pinned Circus revision were inspected on 15–16 October 2026;
the revision was not rebuilt. Back–von Wright and Chen were checked through
indexed copies because publisher access was unavailable. No correspondence
with these published operators has been mechanised. The calculations above
remain informal; current installed laws are cited in the layer guides.
