# Research branch contents

`research/generic-parallel-merges` extends the `research/parallel` checkpoint
at `6d88f02`. Its additional AD, RAD, and AP theories implement merge predicates
on complete observations, with monotone, idempotent healthiness operators and
parallel-closure proofs. See [Generic merge predicates](GENERIC_PARALLEL.md)
for the precise assumptions and the stronger A3 construction. The state-merge
interface remains available. The account below records the preceding branch
split and its inherited research boundary.

`research/parallel` builds on reviewed `main` at `2c39a6e`. It includes the
RAD/AP parallel work as an explicitly provisional extension. The paper
mechanisation and reviewed AD theory come from `main`.

## Added to main

| Area | Research content |
| --- | --- |
| RAD | `reactive-angelic-designs/utp_rad_parallel.thy`, with its session registration and aggregate import. |
| AP | `angelic-processes/utp_ap_parallel.thy`, with its session registration and aggregate import. |
| AP support | The evaluation, RA3AP, feasibility and top-design facts listed below. |
| Documents | The mixed parallel guide, semantic notes, historical dependency handoff and PR drafts. |
| Local material | The existing `slides/` ignore rule and `CLAUDE.md` guidance. |

The AP support in `utp_ap_healthy` comprises `II_AP_eval`, `RA3AP_eval`,
`RA3AP_healthy_wait_eval`, `AP_RA3AP_healthy`, `AP_is_RA3AP`,
`AP_healthy_not_ok_eval`, `AP_feasible`, `AP_feasibleI`, `AP_feasibleD`
and `top_AP_design`. These remain WIP alongside the AP parallel theory.

The RAD proof now uses `ades_par_is_PBMH_ades`, the reviewed AD fact name.
All other RAD/AP WIP source bytes are preserved. No definitions, assumptions
or proof steps have been weakened. Duplicate RAD helper declarations remain
for later cleanup.

## What the rebuild preserves

AD theories, dependency pins, paper coverage and the standalone audit come
from `main`. The audit's `lemma` keywords replace the older `theorem`
keywords; its statements and proofs are identical. The current paper checker
keeps its executable permission.

The original research tip `8f8b5d9` remains on
`backup/research-before-main-rebase-2026-09-08`. The
[rebuild record](RESEARCH_REBASE.md) explains the content checks and build.
The [parallel guide](../PARALLEL_BY_MERGE.md) retains the research discussion;
the [dependency handoff](RESEARCH_HANDOFF.md) and [PR drafts](pr-drafts/README.md)
are dated records whose remote status must be refreshed before submission.

## Continue development

Use the [README](../README.md#build) to set up this branch and
[baseline checks](BASELINE.md) to build it. Keep RAD/AP changes on this branch
until their semantics are reviewed. AD's accepted guarantees are in the
[AD review](AD_PARALLEL_REVIEW.md); a successful research build checks the
stated proofs, not the completeness or suitability of the proposed operators.

Sequential right identity and reverse mappings keep their documented
normality/A3 qualifications. General sequential associativity remains false;
see the [separate audit](../audits/seq-associativity/README.md).
