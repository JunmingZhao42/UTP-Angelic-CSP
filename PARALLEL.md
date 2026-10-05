# Parallel by merge

This branch has one parallel operator by lifted merge per layer. Each guide lists
closure, algebra and ordinary-layer correspondence laws with their premises.

| Layer | Guide | Operator |
| --- | --- | --- |
| Angelic designs (AD) | [AD parallel](docs/AD_PARALLEL.md) | `ades_par`: state merge lifting followed by A3. |
| Reactive angelic designs (RAD) | [RAD parallel](docs/RAD_PARALLEL.md) | `rad_par`: reactive observation merge lifting followed by RAD. |
| Angelic processes (AP) | [AP parallel](docs/AP_PARALLEL.md) | `ap_par`: RAD parallel transported through RA1 and H1. |

AD maps to ordinary-design parallel. RAD/AP map to flat reactive-design
parallel with RD completion. AP transport identifies some distinct divergent
processes; it does not preserve every distinction of direct AP semantics.
