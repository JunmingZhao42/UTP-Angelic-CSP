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

[Angelic_CSP.thy](Angelic_CSP.thy) is the entry point. The
`research/generic-parallel-merges` branch adds parallel operators with merge
predicates over the full AD, RAD, and AP observations. This parallel work is
experimental and is included in the build. The reviewed development is on `main`.

| Documentation | Contents |
| --- | --- |
| [Paper coverage](docs/PAPER_COVERAGE.md) | Definitions, theorem names and exact assumptions |
| [AD parallel](docs/AD_PARALLEL_REVIEW.md) | Merge semantics and assumptions for the parallel laws |
| [Parallel research](PARALLEL_BY_MERGE.md) | The AD/RAD/AP research guide and open issues |
| [Generic merges](docs/GENERIC_PARALLEL.md) | Full-observation merge healthiness and closure proofs |
| [Semantic notes](docs/SEMANTIC_NOTES.md) | Observation alphabets, operators and differences from the sources |
| [Baseline checks](docs/BASELINE.md) | Paper-only builds and validation records |
| [Research boundary](docs/RESEARCH_BOUNDARY.md) | What this research branch adds to `main` |
| [Sequential associativity audit](audits/seq-associativity/README.md) | Counterexamples and conditions for reassociation |

## Merge healthiness

Each parallel operator uses
[OkM](angelic-designs/utp_ades_parallel_generic.thy#L445) to add
`ok' = ok_left ∧ ok_right` to the supplied merge, then applies merge healthiness
for its layer. The supplied merge determines how to combine the choice sets;
healthiness may modify that relation.

| Operator | Completed merge | Operand → result healthiness |
| --- | --- | --- |
| [ades_par_full](angelic-designs/utp_ades_parallel_generic.thy#L566) | [ADOKM](angelic-designs/utp_ades_parallel_generic.thy#L498) = ADM ∘ OkM | [H1 → A](angelic-designs/utp_ades_parallel_generic.thy#L634) |
| [rad_par_full](reactive-angelic-designs/utp_rad_parallel_generic.thy#L677) | [RADOKM](reactive-angelic-designs/utp_rad_parallel_generic.thy#L634) = RADM_full ∘ OkM | [RAD → RAD](reactive-angelic-designs/utp_rad_parallel_generic.thy#L834) |
| [ap_par_full](angelic-processes/utp_ap_parallel_generic.thy#L373) | [APOKM](angelic-processes/utp_ap_parallel_generic.thy#L296) = APM ∘ OkM | [AP → AP](angelic-processes/utp_ap_parallel_generic.thy#L533) |

The table assumes both operands satisfy the condition on the left of the arrow.
There is no healthiness requirement on the supplied merge. The three merge
transformations are monotone and idempotent.

The `ok'` equation is imposed before normalisation and need not hold afterwards;
see the [AD formula](angelic-designs/utp_ades_parallel_generic.thy#L501).
This is the same two-step construction used by
[reactive-design parallel](deps/UTP-Reactive-Designs/utp_rdes_parallel.thy#L123).
An exact correspondence between the operators, and general synchronisation
laws, have not been proved. The [generic parallel guide](docs/GENERIC_PARALLEL.md)
gives the definitions, proofs and examples.

## Build

Use **Isabelle2025-2** and the dependency commits pinned in `deps/`.
The submodules use GitHub SSH URLs. Most come from `isabelle-utp`;
`Optics` and `Z_Toolkit` use compatibility forks recorded in `.gitmodules`.

Clone this branch and set the path to your Isabelle executable:

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
