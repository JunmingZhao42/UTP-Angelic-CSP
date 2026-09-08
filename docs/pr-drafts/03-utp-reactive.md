# Add healthiness laws for reactive merge conditions

Add missing idempotence and monotonicity lemmas for the existing reactive
merge conditions `R1m`, `R1m'`, `R2m`, `R2m'`, `R2cm`, and `R3m`.
Register the corresponding facts with `[closure]` so they can be reused in
other proofs.
