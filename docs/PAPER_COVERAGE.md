# Paper coverage

This index maps Sections 5–7 and Appendix A of
[Angelic processes for CSP via the UTP](https://doi.org/10.1016/j.tcs.2018.10.008)
(Ribeiro and Cavalcanti, TCS 756, 2019, pp. 19–63) to Isabelle facts.
The thesis supplies supporting proofs. Parallel research and the standalone
associativity audit are outside the paper baseline.

## Reading the tables

- `P is H` means design healthiness; `P is X` means a fixed point of X.
- **None** means no extra premises at the stated type and displayed expression.
- **Qualified** marks an additional restriction: A3 for the reverse AD mapping
  (Theorems 6 and 8), and initial `ok = True` for Theorem 35's failure test.
- Reactive results use arbitrary `trace` instances unless list traces are stated.

Theorems 1–2 and Lemmas 1–2 are background results, not separately numbered
claims here. The tables retain every premise, including the explicit design
carrier for Theorem 67 and the printed-statement correction for Theorem 68.

## Definitions and representation

| Paper | Implementation | Representation detail |
| --- | --- | --- |
| Def. 15 | `PBMH`, `pbmh_step` in `utp_ades_core` | Closure under extending the final choice set. `PBMH_ades` carries the outer design observations unchanged. |
| Defs. 16–17 | `astate`, `achoices`, `angelic_design`; `A0`, `A1`, `A` | Types specify alphabets; healthiness specifies the design carrier. `A1_eq_PBMH_ades` assumes H. |
| Defs. 18–19 | `angelic_design_seq`, `aseq` in `utp_ades_ops` | `aseq_ades` lifts relational choice composition to the full alphabet; design composition hides intermediate `ok`. |
| Def. 20, Thm. 4 | `A2_rel`, `A2_rel_eq_expanded`, `A2`, `A2_def'` | Empty/singleton choice evaluation preserves initial state and outer control observations. `A2_lift` connects the two alphabets. |
| Defs. 21–25 | `d2ac`, `p2ac`, `ac2p`; record-based state substitution and `StateII` | `d2ac` constructs a contract; `p2ac` lifts a predicate. These are distinct maps. |
| Def. 26 | `rad_state`, `reactive_angelic_design` in `utp_rad_core` | Trace, refusals and waiting flag live inside the angelic state; `ok` remains outside it. |
| Defs. 27–32 | `RA1`, `RA2`, `II_Rac`, `RA3`, `RA` in `utp_rad_healthy` | Includes the trace-extension and trace-normalisation operations used by the predicates. |
| Defs. 33–35 | `CSPA1`, `CSPA2`, `RAD` in `utp_rad_designs` | `CSPA2` is instantiated by the imported H2 operator. |
| Def. 36 | `ac_singleton_choice`, `ades_singleton_choice` | Singleton-choice binders at relation and full design levels. |
| Defs. 37–44 | Choices, `Chaos_RAD`, `Choice_RAD`, `Stop_RAD`, `Skip_RAD`, `PrefixSkip_RAD`, `extchoice_RAD` in `utp_rad_ops` | Compound prefix `Prefix_RAD` uses design sequential composition. |
| Def. 45 | `NDRAD` in `utp_rad_nd` | Conjunction with `Choice_RAD`; RAD healthiness is a separate premise where required. |
| Defs. 46–48 | `AP`, `II_AP`, `RA3AP` in `utp_ap_healthy` | AP and RAD share an alphabet but have different waiting/divergence conditions. |
| Def. 49 | `NDAP` in `utp_ap_nd` | Conjunction with `Choice_AP`; AP healthiness is separate. |
| Defs. 50–57 | Choices, `Chaos_AP`, `ChaosCSP_AP`, `Choice_AP`, `Stop_AP`, `Skip_AP`, `PrefixSkip_AP` in `utp_ap_ops` | Compound prefix is `Prefix_AP`. |

Definition 22 uses typed records, lenses and ordinary substitution. The
general alphabet calculus of Appendix Lemmas 27–28 has no separate numbered
Isabelle laws; mapping proofs use record equality and substitution directly.

## Angelic designs: Theorems 3–8

| Paper | Isabelle fact | Exact premises / qualification |
| --- | --- | --- |
| 3 | `utp_ades_healthy.A0_design` | None; stated on the displayed design built from the two `ok'` projections. |
| 4 | `utp_ades_healthy.A2_rel_eq_expanded` | None; `A2` uses this expanded form on the design alphabet, connected by `A2_lift` and `A2_def'`. |
| 5 | `utp_ades_designs.ac2p_d2ac` | P is H; makes the paper's “P is a design” explicit. |
| 6 | `utp_ades_designs.d2ac_ac2p` | P is A and A3. **Qualified:** A3 is an additional singleton-witness condition; `d2ac_ac2p_iff_A3` characterises its necessity on A. |
| 7 | `utp_ades_designs.d2ac_ac2p_A2` | P is A and A2. |
| 8 | `utp_ades_designs.d2ac_ac2p_A2_eq` | P is A, A2 and A3. **Qualified** by the same reverse-mapping requirement as Theorem 6. |

## Reactive angelic designs: Theorems 9–35

| Paper | Isabelle fact | Exact premises / qualification |
| --- | --- | --- |
| 9 | `utp_rad_healthy.RA1_A0_absorb` | None. |
| 10 | `utp_rad_designs.RA1_CSPA1` | None. |
| 11 | `utp_rad_designs.RAD_design_form` | None; `RAD_design_form'` is its RAD-healthy elimination form. |
| 12 | `utp_rad_csp.rad_ac2p_RA` | P is PBMH_ades. |
| 13 | `utp_rad_csp.rad_ac2p_RA_design` | None; source design is constructed from wait-false and `ok'` projections. |
| 14 | `utp_rad_csp.rad_p2ac_R` | None. |
| 15 | `utp_rad_csp.rad_p2ac_R_design` | None; displayed CSP design uses wait-false projections. |
| 16 | `utp_rad_csp.rad_ac2p_p2ac_inverse` | None. |
| 17 | `utp_rad_csp.rad_p2ac_ac2p_refine` | P is PBMH_ades. |
| 18 | `utp_rad_csp.rad_p2ac_ac2p_RA_design` | Both wait-false/`ok'` components of P are A2-healthy, as required in the paper. |
| 19 | `utp_rad_ops.RAD_angelic_choice_design` | P and Q are RAD. |
| 20 | `utp_rad_ops.RAD_angelic_choice_CSP` | None. |
| 21 | `utp_rad_ops.RAD_angelic_choice_CSP_refine` | P and Q are RAD. |
| 22 | `utp_rad_ops.RAD_demonic_choice_design` | P and Q are RAD. |
| 23 | `utp_rad_ops.RAD_demonic_choice_CSP_distrib` | None. |
| 24 | `utp_rad_ops.RAD_demonic_choice_CSP` | None. |
| 25 | `utp_rad_ops.Chaos_RAD_angelic_choice_unit` | P is RAD. |
| 26 | `utp_rad_ops.Choice_RAD_angelic_choice` | P is RAD. |
| 27 | `utp_rad_ops.Choice_RAD_demonic_choice` | P is RAD. |
| 28 | `utp_rad_ops.Stop_RAD_angelic_choice` | P is RAD. |
| 29 | `utp_rad_ops.Skip_RAD_angelic_choice` | P is RAD. |
| 30 | `utp_rad_seq.RAD_seq_design` | P and Q are RAD. |
| 31 | `utp_rad_ops.PrefixSkip_RAD_angelic_choice` | P is RAD; list traces. |
| 32 | `utp_rad_ops.extchoice_RAD_Stop` | P is RAD. |
| 33 | `utp_rad_ops.extchoice_RAD_Stop_unit` | P is RAD and A2. |
| 34 | `utp_rad_nd.NDRAD_design_form` | P is RAD. |
| 35 | `utp_rad_nd.NDRAD_fixed_point` | P is RAD. **Qualified:** the universal failure test is guarded by initial `ok = True`. |

## Angelic processes: Theorems 36–63

| Paper | Isabelle fact | Exact premises / qualification |
| --- | --- | --- |
| 36 | `utp_ap_healthy.AP_design_form` | None. |
| 37 | `utp_ap_healthy.AP_wait_cond_design` | None. |
| 38 | `utp_ap_nd.NDAP_design_form` | P is AP. |
| 39 | `utp_ap_rad.H1_RAD_design` | None. |
| 40 | `utp_ap_rad.RA1_AP_design` | None. |
| 41 | `utp_ap_rad.RA1_H1_RAD` | None. |
| 42 | `utp_ap_rad.H1_RA1_AP_refine` | None; applied to the AP image. |
| 43 | `utp_ap_nd.H1_RA1_NDAP_AP` | None; applied to the NDAP/AP image. |
| 44 | `utp_ap_nd.NDAP_angelic_closure` | P and Q are NDAP. |
| 45 | `utp_ap_ops.RA1_H1_angelic_choice` | P and Q are RAD. |
| 46 | `utp_ap_ops.H1_RA1_angelic_choice_refine` | P and Q are AP. |
| 47 | `utp_ap_nd.NDAP_demonic_closure` | P and Q are NDAP. |
| 48 | `utp_ap_ops.RA1_H1_demonic_choice` | P and Q are RAD. |
| 49 | `utp_ap_ops.H1_RA1_demonic_choice_refine` | P and Q are AP. |
| 50 | `utp_ap_ops.Chaos_AP_angelic_choice_unit` | P is AP. |
| 51 | `utp_ap_ops.H1_Chaos_RAD` | None. |
| 52 | `utp_ap_ops.RA1_ChaosCSP_AP` | None. |
| 53 | `utp_ap_ops.H1_Choice_RAD` | None. |
| 54 | `utp_ap_ops.RA1_Choice_AP` | None. |
| 55 | `utp_ap_ops.H1_Stop_RAD` | None. |
| 56 | `utp_ap_ops.RA1_Stop_AP` | None. |
| 57 | `utp_ap_ops.H1_Skip_RAD` | None. |
| 58 | `utp_ap_ops.RA1_Skip_AP` | None. |
| 59 | `utp_ap_ops.AP_seq_design` | P and Q are AP. |
| 60 | `utp_ap_ops.RA1_H1_seq_refine` | P and Q are RAD. |
| 61 | `utp_ap_ops.H1_RA1_seq_refine` | P and Q are AP. |
| 62 | `utp_ap_ops.RA1_H1_seq` | P and Q are both RAD and NDRAD. |
| 63 | `utp_ap_nd.NDAP_seq_closure` | P and Q are both AP and NDAP. No associativity assumption or audit theorem is used. |

## Appendix theorems and numbered lemmas

| Paper | Isabelle fact | Exact premises / qualification |
| --- | --- | --- |
| Thm. 64 | `utp_ades_healthy.PBMH_ades_H1_commute` | None; `PBMH_H1_commute` is the relation-level guard law. |
| Thm. 65 | `utp_ades_healthy.PBMH_ades_H2_commute` | None; `PBMH_H2_commute` is the restricted lifted-relation presentation. |
| Thm. 66 | `utp_rad_healthy.PBMH_ades_RA2_absorb` | None. |
| Thm. 67 | `utp_rad_healthy.RA_A` | P is H. The design carrier is explicit; arbitrary predicates on the design alphabet do not qualify merely by type. |
| Thm. 68 | `utp_rad_healthy.RA1_RA3_commute` | None. Uses the commutation established by the paper's proof; the printed statement repeats one side. |
| Thm. 69 | `utp_rad_healthy.RA2_RA3_commute` | None. |
| Thm. 70 | `utp_rad_healthy.PBMH_ades_RA1_absorb` | None. |
| Thm. 71 | `utp_rad_healthy.RA1_RA2_commute` | None. |
| Thm. 72 | `utp_ades_designs.p2ac_design`, `p2ac_design_nonempty` | None beyond the displayed design form; equality is conjoined with nonempty final choices. |
| Lemma 3 | `utp_ades_healthy.PBMH_ac_empty` | None. |
| Lemma 4 | `utp_ades_designs.ac2p_alt` | None. |
| Lemma 5 | `utp_rad_examples.Prefix_Stop_Stop_R` | `a ≠ b`; makes the distinct-event case explicit. |
| Lemma 6 | `utp_rad_csp.rad_p2ac_ac2p` | None; `p2ac_ac2p_rel_A2` gives the relation-level form. |
| Lemma 7 | `utp_rad_ops.RAD_demonic_choice_CSP_A2` | P and Q are both RAD and A2. |
| Lemma 8 | `utp_rad_examples.rad_ac2p_Stop_Skip` | None. |
| Lemma 9 | `utp_rad_examples.Stop_Skip_seq_Chaos` | None. |
| Lemma 10 | `utp_ap_rad.H1_RA_A_true_design` | None; postcondition is the displayed projection. |
| Lemma 11 | `utp_ap_ops.Chaos_AP_design` | None. |
| Lemma 12 | `utp_ap_ops.H1_PrefixSkip_RAD` | None; list traces. |
| Lemma 13 | `utp_ap_ops.RA1_PrefixSkip_AP` | None; list traces. |
| Lemma 14 | `utp_ap_examples.Prefix_ChaosCSP_AP` | None; list traces. |
| Lemma 15 | `utp_ades_healthy.PBMH_ac_non_empty`, `PBMH_ades_ac_non_empty` | None. |
| Lemma 16 | `utp_ades_healthy.PBMH_ades_rdesign`, `PBMH_rdesign` | Restricted-design presentation with relation-level components. |
| Lemma 17 | `utp_ades_healthy.A2_rdesign` | Restricted-design presentation with relation-level components. |
| Lemma 18 | `utp_ades_healthy.A_state_subst` | Substitution is a function of state alone; independence of `ok` and choices is enforced by its type. |
| Lemma 19 | `utp_rad_healthy.RA3_wait_false_absorb` | None. |
| Lemma 20 | `utp_rad_healthy.RA_design_wf_ok_false` | None; displayed projected design. |
| Lemma 21 | `utp_rad_healthy.RA_design_wf_ok_true` | None; displayed projected design. |
| Lemma 22 | `utp_rad_healthy.RA_design_post` | None. |
| Lemma 23 | `utp_rad_healthy.RA1_design_pre` | None. |
| Lemma 24 | `utp_ades_designs.ac2p_design` | P is H. |
| Lemma 25 | `utp_ades_designs.ac2p_PBMH_ades` | None. |
| Lemma 26 | `utp_ades_designs.PBMH_ades_p2ac` | None. |
| Lemmas 27–28 | Typed record/substitution reasoning | No separate named mechanisation of the paper's general alphabet calculus. |

## Supporting results

Sequential closure, A2 closure, mapping/Galois laws and the general prefix
forms `Prefix_RAD_design` (thesis T.5.4.29) and `Prefix_AP_design` (T.6.4.23)
support the paper results. They are not additional numbered paper theorems.
Worked calculations live in the RAD/AP example theories; shared prefix
observations are in `utp_rad_seq`, and shared RA1 facts in `utp_rad_healthy`.

The [sequential audit](../audits/seq-associativity/README.md) is a separate
session. General reassociation must not be assumed; promoting its conditional
laws and adding more thesis algebra remain separate work, neither needed for
Theorem 63. See [baseline checks](BASELINE.md) for the build procedure.
