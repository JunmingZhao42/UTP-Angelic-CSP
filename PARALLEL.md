# Parallel by merge

| Layer | Guide | Operators and scope |
| --- | --- | --- |
| Angelic designs (AD) | [AD parallel](docs/AD_PARALLEL.md) | Generic `ades_par`; state merge lifting with A3 completion and `ac2p`/`d2ac` laws. |
| Reactive angelic designs (RAD) | [RAD parallel](docs/RAD_PARALLEL.md) | Generic `rad_par`; ordinary reactive merge lifting with RAD completion and `rad_ac2p`/`rad_p2ac` laws. |
| Angelic processes (AP) | [AP parallel](docs/AP_PARALLEL.md) | Generic `ap_par`; direct lifting checks and a separate comparison through RAD. |

Each guide lists theorem premises and links to the Isabelle source.
RAD/AP lifting remains research work: sufficient ordinary merge conditions
for raw RAD closure, and global mapping/A2 laws for direct AP lifting, remain open.
The AP construction through RAD has proved mapping laws but is not established
to equal direct AP parallel.
