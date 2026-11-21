# Documentation conventions

Keep the reader's docs small. Working records go where they cannot pile up.

## Where things go

| Content | Location |
| --- | --- |
| Reader guides | `docs/paper/` and `docs/parallel/`; update them in place. |
| Open tasks and undecided questions | `PLAN.md` for the parallel plan; GitHub issues for other work. |
| Finished work | The commit message. Do not add a log entry; remove finished items from `PLAN.md`. |
| Evidence an open `PLAN.md` item depends on: write-up, scratch theories, scripts | `docs/reviews/<YYYY-MM-DD>-<topic>/`, listed in `docs/reviews/README.md`. When the item is settled, install the result or state it in the owning guide, then delete the folder. |
| Raw evidence: PIDE and batch output, logs, hashes, patches, `.before` copies | Outside the repository. Never commit it. |
| Session handoffs | Not in `docs/`. Move open items into `PLAN.md` or an issue. |
| Superseded notes | Fold anything still true into the guide that owns it, then delete the note. |

## Rules

- Cite Isabelle results by name, linking to their declaration with a `#Lnnn`
  anchor in the owning theory. Update affected anchors when the theory changes
  and check them against the current source.
- Link named lemma and definition references to their declaration lines. Summarise
  lifted-merge healthiness and parallel closure in compact tables with premises.
- State each fact once, in the guide or plan section that owns it; elsewhere,
  link to it.
- Keep `docs/parallel/` as concise references to definitions, laws, premises and
  open questions. Put shared notation in its README; use tables only for useful
  comparisons. Add theory walkthroughs and proof explanations only when requested.
- A scratch proof that `PLAN.md` relies on must build: save it as a theory in
  its `docs/reviews/` folder with a `ROOT` session, or install it.
- Before finishing a documentation change, run `./scripts/check-doc-links.py`
  and fix what it reports.
