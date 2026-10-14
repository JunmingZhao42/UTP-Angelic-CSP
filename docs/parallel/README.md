# Parallel by merge

[Documentation](../README.md) · [Paper guides](../paper/README.md)

This branch has one parallel operator by lifted merge per layer. Each guide lists
closure, algebra and ordinary-layer correspondence laws with their premises.

Read AD → RAD → AP: AD introduces the shared merge and choice-set conventions;
RAD adds reactive observations, and AP transports the RAD operator.

| Layer | Guide | Operator |
| --- | --- | --- |
| Angelic designs (AD) | [AD parallel](AD.md) | `P ∥AD[j] Q`: state merge lifting followed by A3. |
| Reactive angelic designs (RAD) | [RAD parallel](RAD.md) | `P ∥RAD[M] Q`: reactive observation merge lifting followed by RAD. |
| Angelic processes (AP) | [AP parallel](AP.md) | `P ∥AP[M] Q`: RAD parallel transported through RA1 and H1. |

AD maps to ordinary-design parallel. RAD/AP map to flat reactive-design
parallel with RD completion. AP transport identifies some distinct divergent
processes; it does not preserve every distinction of direct AP semantics.
