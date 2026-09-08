# Main and research branches

`main` contains the paper mechanisation, supporting algebra and the reviewed
AD parallel extension. RAD/AP parallel remain work in progress on
`research/parallel`. This page describes the split as of **8 September 2026**.

## Included in main

| Layer | Development |
| --- | --- |
| AD | Paper results; sequential closure and qualified `Skip_AD` identities; mapping and Galois laws; reviewed parallel extension. |
| RAD | Paper results; sequential and prefix A2 closure; CSP correspondences; non-divergent sequential closure; general prefix forms. |
| AP | Paper results; AP/RAD correspondence support; sequential laws and general prefix forms. |
| Audit | Sequential associativity counterexamples and conditional laws, in a separate session. |

The directories are `angelic-designs/`, `reactive-angelic-designs/` and
`angelic-processes/`. `Angelic_CSP.thy` is the entry point.
See [paper coverage](PAPER_COVERAGE.md) for exact theorem assumptions and
[baseline checks](BASELINE.md) for build instructions and validation.

## Parallel status

The AD parallel theory is loaded by the AD session. It includes exact and
upward merge lifting, A2/A3 results, normal-operand laws, conditional
associativity and examples. The [AD review](AD_PARALLEL_REVIEW.md) records
the assumptions, naming changes and validation.

`research/parallel` preserves the combined research. Its RAD/AP parallel
theories, their session registrations and aggregate imports are absent from
`main`. The mixed parallel guide and provisional research documents also
remain separate.

The following support is excluded from `main`:

| Research file | Pending additions or relocation |
| --- | --- |
| `angelic-processes/utp_ap_healthy.thy` | `II_AP_eval`, `RA3AP_eval`, `RA3AP_healthy_wait_eval`, `AP_RA3AP_healthy`, `AP_is_RA3AP`, `AP_healthy_not_ok_eval`, `AP_feasible`, `AP_feasibleI`, `AP_feasibleD`, `top_AP_design` |

The AD support is included: `arel_not_applied` is in `utp_ades_core`;
`A0_healthy_non_empty`, `arel_indep_A3_rel`, `H_A3_intro` and `N_preD_indep`
are in `utp_ades_healthy`. The A0 helper moved from the parallel theory;
its statement is unchanged.

RAD/AP parallel and AP support still need their own review. Merging the
research branch wholesale would bring all of that pending work into `main`.

## Mathematical boundaries

AD sequential right identity requires normality. The reverse mapping needs
its A3 qualification. Sequential composition is not associative on the full
A/RAD/AP carriers; the [audit](../audits/seq-associativity/README.md) gives
counterexamples and sufficient conditions. Its results are not production
imports. Keeping research separate does not assert that its pending results
are false or ready for use.
