# Reviews

Each folder holds the evidence behind one open [plan](../../PLAN.md) item: a
write-up, scratch theories and scripts. When the item is settled, install the
result or state it in the guide that owns it, then delete the folder. Finished
work is recorded in commit messages, not here.

| Folder | Open item | Isabelle sessions |
| --- | --- | --- |
| [Geometry of AD parallel](2026-11-20-ad-parallel-geometry/README.md) | Off A2: remaining geometry laws to install | `AD_Geometry_Probe`, `RAD_Geometry_Probe`, `AP_Geometry_Probe` |
| [Angelic choice against a synchronising partner](2026-11-25-angelic-sync-algebra/README.md) | Stage 6 research: associativity of the least monotone parallel F | `Angelic_Sync_Probe` |

## Milestones

| Commit | Date | Result |
| --- | --- | --- |
| `f0f636f` | 1 Nov 2026 | Baseline audit and documentation link checker; paper-guide corrections in [issue #1](https://github.com/JunmingZhao42/UTP-Angelic-CSP/issues/1) |
| `5e76186`, `0cf121b` | 2 Nov 2026 | AD merge built from `j`; AD reuses D's merge conditions |
| `8d83edd` | 3 Nov 2026 | Generic par-by-merge laws in UTP's `utp_concurrency.thy` |
| `7e25c6c`, `ac0a3f8` | 7 Nov 2026 | Nondivergent AD associativity; ordinary and stateful RD laws |
| `e0fc9e9`–`3b8c7ec` | 9 Nov 2026 | RAD closure, shared choice-set lift, RAD associativity |
| `06cd91d` | 9–21 Nov 2026 | Laws split into generic and lifted theories; move to patched Isabelle2026 |
| `27c81d0` | 21 Nov 2026 | `ades_par_assoc_det`: AD associativity for any operands with a deterministic merge |
