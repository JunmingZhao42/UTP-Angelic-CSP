# Paper and parallel development

The cleanup branch keeps the paper mechanisation and its supporting algebra,
plus the AD parallel implementation already committed at `dead464`.
The complete provisional development is preserved on `research/parallel`
at checkpoint `25f8201`. Selected nonparallel definitions, theorem statements,
and proofs are copied unchanged from that checkpoint. The AD parallel file
instead retains the earlier committed version described below.

## Retained in the cleanup branch

- AD sequential closure, `Skip_AD` and its qualified identity laws, and the
  mapping-carrier and Galois laws. `arel_indep_out_unrest` stays because the
  right-identity characterisation uses it. The PBMH lifting and commutation
  facts support these results and the AP/RAD correspondence.
- RAD sequential and prefix A2 closure, CSP operator correspondences,
  non-divergent sequential closure, and general prefix normal forms.
  `utp_rad_ops_csp` is registered in `ROOT` and imported by `utp_rad`.
- AP/RAD mapping support, sequential proof simplifications, and the general
  AP prefix normal form. `AP_neg_design` stays because `H1_RAD_AP_design`
  uses it; the remaining pending additions to `utp_ap_healthy` stay in research.
- Shared prefix observations and continuations move from the example theories
  into `utp_rad_seq`. The input-`ok` unrest rule moves to `utp_rad_healthy`.
  Their existing definitions and proofs are preserved.

The right identity for AD sequential composition retains its normality
qualification and counterexample. The A3 qualification on the reverse mapping
also remains. Sequential associativity on the full A/RAD/AP carriers must not
be assumed; the [standalone audit](../audits/seq-associativity/README.md)
is checked separately from the production sessions.

## AD parallel boundary

`angelic-designs/utp_ades_parallel.thy` is byte-for-byte identical to `dead464`
and remains in the AD session and aggregate. The pending changes to merge
lifting, A2/A3 closure, normal operands, associativity, and examples are not
included. Retaining the earlier implementation is a version boundary, not
an endorsement of the provisional extensions.

`utp_rad_parallel.thy` and `utp_ap_parallel.thy` are absent from this branch,
including its session registrations and aggregate imports. The three-session
hierarchy and existing AP file locations are unchanged.

## Support kept on the research branch

These additions and relocations were checked by their declaration content and
callers, rather than by filename alone. Their current uses are confined to the parallel
development, or to other support in the same excluded group. They remain in
their original files on `research/parallel`; no research content was discarded.

| Research file | Excluded declarations |
| --- | --- |
| `angelic-designs/utp_ades_core.thy` | `arel_not_applied` |
| `angelic-designs/utp_ades_healthy.thy` | `A0_healthy_non_empty`, `arel_indep_A3_rel`, `H_A3_intro`, `N_preD_indep` |
| `utp_ap_healthy.thy` | `II_AP_eval`, `RA3AP_eval`, `RA3AP_healthy_wait_eval`, `AP_RA3AP_healthy`, `AP_is_RA3AP`, `AP_healthy_not_ok_eval`, `AP_feasible`, `AP_feasibleI`, `AP_feasibleD`, `top_AP_design` |

`A0_healthy_non_empty` already exists in the retained AD parallel theory.
Its pending relocation into `utp_ades_healthy` is not taken, so the cleanup
keeps the existing declaration in its original parallel file without duplication.

This placement does not assert that these generic lemmas are false or can
never belong in the core. They can be promoted separately when a reviewed
development needs them. Before integrating the research branch, review both
the parallel theories and this support group; merging the checkpoint wholesale
would bring all of them back.

## Preserved work awaiting later cleanup

The standalone associativity audit is retained in its own session. Paper
coverage and the snapshot checker are documented in [BASELINE.md](BASELINE.md).
PR drafts, the parallel guide, and provisional source support remain on the
research branch. Historical commit rewriting is a separate later step.
`main`, existing backups, and dependency gitlinks are unchanged.

## Validation

Checked on 8 September 2026 with Isabelle2025-2 on arm64 macOS, using the
separate `utp-cleanup-2026-09-08` profile:

| Source checkpoint | Check | Result |
| --- | --- | --- |
| `6b80c2d` — AD support | Full `UTP-Angelic-CSP` build from a fresh profile | Exit 0; 6m20s. |
| `d811859` — RAD/AP support | Full `UTP-Angelic-CSP` build | Exit 0; 42s. Rebuilt RAD and AP; reused the validated AD and dependency heaps. |
| `d811859` | No-build freshness check | Exit 0. |

The first build rebuilt HOL-Eisbach, Optics, Shallow_Expressions,
Shallow_Expressions_Z, UTP2, UTP-Designs, UTP-Reactive,
UTP-Reactive-Designs, and all three project sessions. Distribution HOL heaps
were reused. Both builds used the unchanged dependency gitlinks from `dead464`.

Run from the cleanup repository root, with `ISABELLE` pointing to the
Isabelle2025-2 executable:

```bash
env ISABELLE_IDENTIFIER=utp-cleanup-2026-09-08 PROJECT_DIR="$PWD" \
  "$ISABELLE" build -v -b -d deps -d . \
  -o system_heaps=false -o threads=4 UTP-Angelic-CSP
```

Replace `-b` with `-n` for the freshness check. These checks include the
retained AD parallel implementation; they are not a paper-only snapshot build
or a new validation of the research checkpoint or associativity audit.

Source checks confirmed the retained AD parallel file matches `dead464`,
the selected RAD/AP source imports no provisional parallel theory, and
the research support listed above is absent from the core files. The existing
AD-local `A0_healthy_non_empty` remains in place. Source hashes were checked
before committing, and `git diff --check` passed.

Local logs are retained as `utp-cleanup-ad-build.log`,
`utp-cleanup-rad-ap-build.log`, and `utp-cleanup-freshness.log` under
`/Users/ming/AI-summer/backups/UTP-Angelic-CSP/20260908T054338Z/separation-validation/`.
