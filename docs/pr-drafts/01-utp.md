# Add merge helper and a commutativity lemma for the parallel operator

Add two helpers in `utp_concurrency.thy`:

- `merge_eval` makes merge expressions easier to write using the starting
  state, the two branch results, and the final state.
- `par_by_merge_comm` proves that swapping the parallel branches leaves the
  result unchanged when the merge treats both orders the same.
