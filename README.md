# UTP-Angelic-CSP

An Isabelle/UTP mechanisation of Ribeiro and Cavalcanti's
[Angelic processes for CSP via the UTP](https://doi.org/10.1016/j.tcs.2018.10.008)
(*Theoretical Computer Science* 756, 2019, pp. 19–63).

The three sessions build on each other:

| Layer | Directory | Session |
| --- | --- | --- |
| Angelic designs (AD) | `angelic-designs/` | `UTP-Angelic-Designs` |
| Reactive angelic designs (RAD) | `reactive-angelic-designs/` | `UTP-Reactive-Angelic-Designs` |
| Angelic processes (AP) | `angelic-processes/` | `UTP-Angelic-CSP` |

`Angelic_CSP.thy` is the entry point. This is `research/generic-parallel-merges`,
extending the `research/parallel` checkpoint at `6d88f02` with full-observation
merge predicates for AD, RAD, and AP. Its normal build also loads
**generic merge and RAD/AP parallel research**; a passing build does not make
that research final.
Use `main` for the reviewed development.

| Read this | For |
| --- | --- |
| [Paper coverage](docs/PAPER_COVERAGE.md) | Definitions, theorem names and exact assumptions |
| [AD parallel](docs/AD_PARALLEL_REVIEW.md) | Merge semantics, naming and qualified parallel laws |
| [Parallel research](PARALLEL_BY_MERGE.md) | The AD/RAD/AP research guide and open issues |
| [Generic merges](docs/GENERIC_PARALLEL.md) | Full-observation merge healthiness and closure proofs |
| [Semantic notes](docs/SEMANTIC_NOTES.md) | Observation alphabets, operators and source qualifications |
| [Baseline checks](docs/BASELINE.md) | Paper-only builds and validation records |
| [Research boundary](docs/RESEARCH_BOUNDARY.md) | What this research branch adds to `main` |
| [Sequential associativity audit](audits/seq-associativity/README.md) | Counterexamples and conditions for reassociation |

## Merge healthiness at a glance

For full-observation parallel [P parallel_M Q](angelic-designs/utp_ades_parallel_generic.thy#L14), these are sufficient conditions;
operand requirements apply to both `P` and `Q`. `M is K` means `K M = M`.

| Merge condition | Operands | Result healthiness |
| --- | --- | --- |
| [A0M](angelic-designs/utp_ades_parallel_generic.thy#L346) / [PBMHM](angelic-designs/utp_ades_parallel_generic.thy#L255) / [H2M](angelic-designs/utp_ades_parallel_generic.thy#L316) | Arbitrary | [A0](angelic-designs/utp_ades_parallel_generic.thy#L535) / [PBMH_ades](angelic-designs/utp_ades_parallel_generic.thy#L520) / [H2](angelic-designs/utp_ades_parallel_generic.thy#L525), respectively |
| [H1M](angelic-designs/utp_ades_parallel_generic.thy#L287) | `H1` | [H1](angelic-designs/utp_ades_parallel_generic.thy#L555) |
| [ADM](angelic-designs/utp_ades_parallel_generic.thy#L438) | `H1` (in particular, `A`) | [AD: A](angelic-designs/utp_ades_parallel_generic.thy#L573) |
| [A2M](angelic-designs/utp_ades_parallel_generic.thy#L406) | Arbitrary, including RAD/AP predicates | [A2](angelic-designs/utp_ades_parallel_generic.thy#L530) |
| [A3M](angelic-designs/utp_ades_parallel_normal.thy#L115) | `H1` | AD: [A](angelic-designs/utp_ades_parallel_normal.thy#L205), [A2](angelic-designs/utp_ades_parallel_normal.thy#L214), and [A3](angelic-designs/utp_ades_parallel_normal.thy#L196) |
| [RADM_full](reactive-angelic-designs/utp_rad_parallel_generic.thy#L514) | `RAD` | [RAD: RAD](reactive-angelic-designs/utp_rad_parallel_generic.thy#L702) |
| [APM](angelic-processes/utp_ap_parallel_generic.thy#L277) | `AP` | [AP: AP](angelic-processes/utp_ap_parallel_generic.thy#L380) |

Merge conditions denote fixed-point healthiness. `RADM_full` and `APM` alone
do not ensure `A2`; see [Generic merges](docs/GENERIC_PARALLEL.md#merge-healthiness-and-closure)
for component conditions and closure lemmas.

## Build

Use **Isabelle2025-2** and the dependency commits pinned in `deps/`.
The submodules use GitHub SSH URLs. Most come from `isabelle-utp`;
`Optics` and `Z_Toolkit` use compatibility forks recorded in `.gitmodules`.

To obtain this generic-merge investigation, clone
`research/generic-parallel-merges`, then set the path to your Isabelle
executable. The preceding research baseline remains on `research/parallel`.

```bash
git clone --branch research/generic-parallel-merges --recurse-submodules git@github.com:JunmingZhao42/UTP-Angelic-CSP.git
cd UTP-Angelic-CSP

export PROJECT_DIR="$PWD"
export ISABELLE="/path/to/Isabelle2025-2/bin/isabelle"
export UTP_PROFILE="utp-2025-2"
```

For an existing clone, run `git submodule sync --recursive`, then
`git submodule update --init --recursive`.
Install the profile templates and build all three sessions:

```bash
mkdir -p "$HOME/.isabelle/$UTP_PROFILE/etc"
cp isabelle-profile/ROOTS "$HOME/.isabelle/$UTP_PROFILE/ROOTS"
cp isabelle-profile/settings "$HOME/.isabelle/$UTP_PROFILE/etc/settings"

ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" build \
  -b -o system_heaps=false UTP-Angelic-CSP
```

Keep `PROJECT_DIR` exported when using this profile. Replace `-b` with `-n`
for a freshness check without rebuilding.

## Edit

Open jEdit:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" jedit \
  -n -u -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
  "$PROJECT_DIR/Angelic_CSP.thy"
```

Or start the VS Code language server:

```bash
ISABELLE_IDENTIFIER="$UTP_PROFILE" "$ISABELLE" vscode_server \
  -n -A UTP-Angelic-Designs -R UTP-Angelic-CSP \
  -d "$PROJECT_DIR/deps" -d "$PROJECT_DIR" \
  -o system_heaps=false
```

Both reuse the AD heap while keeping RAD/AP editable. To edit AD theories
too, use `-A UTP-Reactive-Designs` instead.

## Background

For the underlying UTP concepts, see Cavalcanti and Woodcock's *A Tutorial
Introduction to CSP in Unifying Theories of Programming* and Hoare and He's
*Unifying Theories of Programming*.
