# Issue tracker: GitHub

Issues and specs live in GitHub Issues for `JunmingZhao42/UTP-Angelic-CSP`. Run `gh` from this repo; use `--repo JunmingZhao42/UTP-Angelic-CSP` when running elsewhere.

## Operations

- Create an issue: `gh issue create --title "..." --body-file <file>`.
- Read an issue: `gh issue view <number> --json number,title,body,labels,comments`.
- List issues: `gh issue list --state open --json number,title,body,labels`; use label filters as needed.
- Comment: `gh issue comment <number> --body-file <file>`.
- Apply or remove labels: `gh issue edit <number> --add-label "..."` or `--remove-label "..."`.
- Close: `gh issue close <number>`.

When a skill says "publish to the issue tracker", create a GitHub issue. When it says "fetch the relevant ticket", read the issue.

## Pull requests as a triage surface

**PRs as a request surface: no.**

## Wayfinding and ticket relationships

A wayfinding map is an issue labelled `wayfinder:map`; its child tickets use `wayfinder:<type>` (`research`, `prototype`, `grilling`, or `task`). Create these labels when that workflow is used.

Use native GitHub sub-issues and issue dependencies when supported. For API relationships, use the numeric database ID from `gh api repos/JunmingZhao42/UTP-Angelic-CSP/issues/<number> --jq .id`, rather than the issue number or node ID.

If native relationships are unavailable, put `Part of #<parent>` and `Blocked by: #<number>` in child issue bodies and maintain a task list in the parent. A ticket is unblocked when every blocker is closed.

Work through unassigned, unblocked open children in map order. Claim a ticket with `gh issue edit <number> --add-assignee @me`; resolve it by commenting, closing it, and recording its outcome in the map.
