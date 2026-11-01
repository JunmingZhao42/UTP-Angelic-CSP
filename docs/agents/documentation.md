# Documentation conventions

Keep the reader's docs small. Working records go where they cannot pile up.

## Where things go

| Content | Location |
| --- | --- |
| Reader guides | `docs/paper/` and `docs/parallel/`; update them in place. |
| Open tasks and undecided questions | `PLAN.md` for the parallel plan; GitHub issues for other work. |
| Finished stage | One short entry in `docs/reviews/README.md`: what changed and how it was checked. |
| Full stage write-up and raw evidence: PIDE and batch output, logs, hashes, patches, `.before` copies | `audits/reviews/<YYYY-MM-DD>-<stage>/`, which is gitignored. |
| Write-up of unfinished work that `PLAN.md` depends on | `docs/reviews/<YYYY-MM-DD>-<topic>/README.md` until that item closes; then reduce it to a log entry. |
| Session handoffs | Not in `docs/`. Move open items into `PLAN.md` or an issue; keep any other notes in `audits/handoffs/`. |
| Superseded notes | Fold anything still true into the guide that owns it, then delete the note or move it to `audits/retired-docs/`. |

## Rules

- Cite Isabelle results by name, linking the theory file without a `#Lnnn`
  anchor: line anchors break whenever the theory changes. Where a guide already
  uses line anchors, keep them accurate.
- State each fact once, in the guide or plan section that owns it; elsewhere,
  link to it.
- A scratch proof that `PLAN.md` relies on must not exist only as evidence:
  `*.txt`, `*.json` and `*.log` are gitignored. Save it as
  `docs/reviews/<YYYY-MM-DD>-<stage>/scratch.thy`, or install it.
- Before finishing a documentation change, run `./scripts/check-doc-links.py`
  and fix what it reports.
