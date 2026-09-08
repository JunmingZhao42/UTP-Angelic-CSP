# Add design parallel-by-merge with merge healthiness conditions

Add `utp_des_parallel.thy` with a parallel operator for designs and helpers
for combining the two branch results.

Define `H1m`, `H2m`, and `HDM`, prove their basic laws, and show that these
conditions are sufficient for parallel composition to preserve design
healthiness. Include helpers for using ordinary state merges with designs
and lemmas for evaluating them.

Uses `merge_eval` and the design healthiness helpers.
