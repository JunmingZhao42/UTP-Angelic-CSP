# Parallel by merge

[Documentation](../README.md) · [Paper guides](../paper/README.md)

On `research/parallel2`, ordinary and angelic design parallel constrain the final
state by the state merge only when both branches terminate. After a divergence the
branch states must still have some merged state, as in the RD merge. The
[D guide](D.md) and [AD guide](AD.md) describe the matching liftings and their
proved correspondence. RAD/AP retain their separate reactive merge semantics.

[Related work](related-work.md) compares this lifting with published
ordinary-design, Circus, CSP, CCS and refinement-calculus semantics, and explains
why parallel by merge cannot make Chaos absorb Miracle.

This branch has one parallel operator by lifted merge per layer. Each guide lists
closure, algebra and ordinary-layer correspondence laws with their premises.

Read D for ordinary merge lifting and its laws, then AD → RAD → AP for the
angelic layers. AD introduces choice sets; RAD adds reactive observations, and
AP transports the RAD operator.

| Layer | Guide | Operator |
| --- | --- | --- |
| Ordinary designs (D) | [D parallel](D.md) | `P ∥D[j] Q`: raw state merge followed by design Skip, as in the RD merge. |
| Angelic designs (AD) | [AD parallel](AD.md) | `P ∥AD[j] Q`: state merge lifting; the A3 wrapper is redundant for H1-healthy operands. |
| Reactive angelic designs (RAD) | [RAD parallel](RAD.md) | `P ∥RAD[M] Q`: parallel using a lifted reactive observation merge. |
| Angelic processes (AP) | [AP parallel](AP.md) | `P ∥AP[M] Q`: RAD parallel transported through RA1 and H1. |

AD maps to ordinary-design parallel. RAD/AP map to flat reactive-design
parallel. RAD/AP closure requires healthy operands and a RADm-healthy merge.
AP transport identifies some distinct divergent
processes; it does not preserve every distinction of direct AP semantics.
