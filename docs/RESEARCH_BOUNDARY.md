# Research scope

The paper development is indexed in [paper coverage](PAPER_COVERAGE.md),
with qualifications explained in [semantic notes](SEMANTIC_NOTES.md).
The normal build also includes parallel research; the
[paper-only checker](BASELINE.md) excludes the project parallel theories.

The parallel development provides one public operator per layer:

| Layer | Operator and scope | Guide |
| --- | --- | --- |
| AD | `ades_par` applies A3 to parallel using `merge_ades j`. | [AD parallel](AD_PARALLEL.md) |
| RAD | `rad_par` applies RAD to parallel using `rad_lift_merge M`. Its closure law before completion assumes RAD/A2 operands and RD closure of their ordinary parallel. | [RAD parallel](RAD_PARALLEL.md) |
| AP | `ap_par` transports RAD parallel through RA1 and H1, identifying some distinct divergent AP processes. | [AP parallel](AP_PARALLEL.md) |

The guides state the healthiness, algebra and mapping premises. A successful
build checks those propositions; it does not establish that the proposed
parallel semantics are suitable for every intended application.

Sequential right identity and reverse mappings retain their normality/A3
qualifications. General sequential associativity is false; reassociation
requires additional conditions.

See the [README](../README.md#build) for setup and
[baseline checks](BASELINE.md) for build commands.
