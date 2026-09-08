# Submodule PR drafts

Updated on 7 September 2026. These are PR titles and descriptions for review.
Each draft contains only a title and a short description to copy into a PR.
Build evidence, submission preparation, and Git history notes are kept here,
outside the PR messages.

UTP has been submitted as [PR #10](https://github.com/isabelle-utp/UTP/pull/10).
UTP-Designs is the next draft to review.

The audit covers the checked-out revision of every submodule, plus the
`UTP-Designs` branch `research/design-parallel`. Upstream `main` revisions
were checked through GitHub. Comparisons use the common ancestor, as a PR
does, so upstream-only commits are not described as proposed deletions.

## Drafts and proposed destinations

| Draft | Target repository and base | Source | Ahead / behind upstream | Changed files |
| --- | --- | --- | --- | --- |
| [UTP](01-utp.md) | `isabelle-utp/UTP:main` | `JunmingZhao42/UTP:main` | 2 / 0 | 1 |
| [UTP-Designs](02-utp-designs.md) | `isabelle-utp/UTP-Designs:main` | `JunmingZhao42/UTP-Designs:main` | 4 / 0 | 4 |
| [UTP-Reactive](03-utp-reactive.md) | `isabelle-utp/UTP-Reactive:main` | Local detached commit `2054af5`; source branch to be prepared | 1 / 0 | 1 |
| [UTP-Reactive-Designs](04-utp-reactive-designs.md) | `isabelle-utp/UTP-Reactive-Designs:main` | `JunmingZhao42/UTP-Reactive-Designs:main` | 1 / 0 | 1 |
| [Optics](05-optics.md) | `isabelle-utp/Optics:main` | Local branch `optics-2025-2` | 2 / 0 | 5 |
| [Z_Toolkit](06-z-toolkit.md) | `isabelle-utp/Z_Toolkit:main` | Local branch `z-2025-2` | 2 / 0 | 5 |
| [Design parallel research](07-utp-designs-parallel.md) | `isabelle-utp/UTP-Designs:main`, after the support PR | Local branch `research/design-parallel` | See the separate history note below | 2 additional files relative to current local `main` |

The design-parallel draft is deferred research. The UTP-Designs main-branch
draft contains the support laws and binder updates; it does not include
`utp_des_parallel.thy` or its aggregate import.

## Revisions inspected

| Submodule | Upstream `main` | Checked-out commit | Local commits to contribute |
| --- | --- | --- | --- |
| UTP | `62b3cbc55ed6ee72006e564e6f1e21dd0a2bd098` | `dfd71aef53a117844903a8bbb3b0bfd471891536` | `ac77c5f`, `dfd71ae` |
| UTP-Designs | `147de0ec3e4109eaaf11b49cd2f79a4b947604a0` | `0f6ff1147ba2d083f8f989d8302996f80a538b29` | `3914141`, `700a4fe`, `6fb241a`, `0f6ff11` |
| UTP-Reactive | `bf63f0fab3439f2b9c38ceef9e7da90171106493` | `2054af57da7a43fd374700d5ec97599631229f0d` | `2054af5` |
| UTP-Reactive-Designs | `6acb9dcd8e8cdfa2e7d8354af713082b7de12c54` | `143d4a572c7de372240406dc0b3c28bafed19d50` | `143d4a5` |
| Optics | `28593fbdf9289d42ca8c1922a728b7529d74d316` | `e3a5f441f1d64f6e348901b5e25e185121d4af19` | `4d17e56`, `e3a5f44` |
| Z_Toolkit | `6a268ade7c49b7fc628372ad736efbf4f8e762b8` | `5deade1f6ce71d5cab24af9f817c1c4a0ca629e8` | `1a2dbdd`, `5deade1` |

The other three submodules exactly match their upstream `main` revisions,
so there is no contribution to draft for them:

| Submodule | Matching revision |
| --- | --- |
| Abstract_Prog_Syntax | `44f64866919533975745da914b337572066733cb` |
| Circus_Toolkit | `8542d78a64088d18fc9402c111aafd433a8371ff` |
| Shallow-Expressions | `c8ca17a0b85335435d2bc40b13b8a4a1c38dde57` |

Circus_Toolkit's changed parent gitlink is an update to an upstream commit,
not an outstanding change to contribute to Circus_Toolkit itself.

## Preparation before submission

- **UTP and UTP-Designs:** the proposed `main` heads are present on the forks.
  Their drafts cover every commit ahead of upstream, including the earlier
  commutativity and design-support commits. The design binder change follows
  syntax already present in upstream UTP.
- **UTP-Reactive:** preserve `2054af5` on a named contribution branch before
  publishing it. This checkout is detached and its only configured remote is
  `isabelle-utp/UTP-Reactive`; a fork/source destination has not been selected.
- **UTP-Reactive-Designs:** the sole outstanding change is the existing
  `Miracle`/`Chaos` counterexample and its explanation. Its draft is separate
  from the general support-law contributions.
- **Optics:** rebased onto upstream `28593fb` and validated. The channel-generator
  conflict was resolved by retaining upstream's type-parameter and sort handling
  alongside the local compatibility changes. The current fork branch listing
  does not contain
  `optics-2025-2`, although the branch and both commits exist locally.
  Review the overlap with the open upstream PR
  [Tidy up Scenes and Scene_Spaces and improve automation](https://github.com/isabelle-utp/Optics/pull/2),
  which also changes `Scenes.thy`, `Scene_Spaces.thy`, and the
  `equiv_coregion` proof.
- **Z_Toolkit:** rebased onto upstream `6a268ad` and validated. Both local commits
  replayed without conflicts. The current fork branch listing does not contain
  `z-2025-2`,
  although the branch and both commits exist locally.
- **Design parallel research:** keep this separate from the current main
  development. It requires UTP's `merge_eval` and the design healthiness
  helpers. The branch ends at `6129b14676a97af381e30abfc880190b3ab89d8f`.
  Its prerequisite commit `ebaa55f` is patch-equivalent to main's `0f6ff11`;
  it is not the same ancestor. After the support changes land, create the
  eventual contribution branch from the updated main and carry over only
  `6129b14`. A direct three-dot comparison of the present branches also lists
  the duplicate helper patch, even though their healthiness files are identical.

The initial audit found no existing PRs from the proposed source branches;
UTP PR #10 has since been opened. Refresh the comparisons before submitting
the remaining drafts. Each rebased submodule retains its original tip on
`backup/pre-upstream-rebase-2026-09-07`. Both still have two local commits,
and each combined local patch has the same stable patch ID as before the
rebase. Parent staging and all other source work were preserved.

## Validation evidence and limits

The full downstream build after rebasing on 7 September 2026 passed with
Isabelle2025-2, profile `utp-2025-2`, in 6m20s. It rebuilt Optics,
Shallow_Expressions, Shallow_Expressions_Z (including the Z_Toolkit theories),
UTP2, UTP-Designs, UTP-Reactive, UTP-Reactive-Designs, UTP-Angelic-Designs,
UTP-Reactive-Angelic-Designs and UTP-Angelic-CSP. The dependency revisions are
the checked-out revisions above. The working project includes the existing
AD/RAD/AP parallel theories and excludes `utp_des_parallel`.

The project build used the following invocation, shown with `ISABELLE`
standing for the Isabelle2025-2 executable and run from the project root:

```bash
env ISABELLE_IDENTIFIER=utp-2025-2 \
  PROJECT_DIR="$PWD" \
  "$ISABELLE" build -v -b \
  -o system_heaps=false -o threads=4 UTP-Angelic-CSP
```

The corresponding log is
`/tmp/utp-upstream-rebase-yoocll7v/build.log`.
An earlier full build containing the exact saved design-parallel theory
passed in 5m05s; its log is `/tmp/utp-merge-eval-rebuild.log`.
The UTP-Designs freshness/build check before saving that branch also passed,
with log `/tmp/utp-design-parallel-split-nu2zcgfa/side-branch-build.log`.

`UTP-Angelic-CSP` is this project's session. The command and logs above
record the checks performed in this checkout. The PR messages omit validation
sections and build commands.

The successful rebase build establishes the tested dependency combination,
including the current upstream commits in Optics and Z_Toolkit. It does not
establish a build of each proposed PR independently of the other local
dependency contributions. The design-parallel branch will need validation
after its eventual preparation on the updated main.

Each contribution changes its own repository's sources. Updating the
UTP-Angelic-CSP parent gitlinks is a separate commit after selecting and
publishing the intended submodule revisions.
