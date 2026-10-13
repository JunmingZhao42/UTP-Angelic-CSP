# Reactive angelic designs: definitions and results

[Paper coverage](PAPER_COVERAGE.md) · [AD](AD.md) · [AP](AP.md) · [RAD parallel](RAD_PARALLEL.md) · [Semantic notes](SEMANTIC_NOTES.md)

This guide connects the current `rea_vars_ext` implementation to:

- **Paper:** Ribeiro and Cavalcanti, [*Angelic processes for CSP via the UTP*](https://doi.org/10.1016/j.tcs.2018.10.008), TCS 756 (2019), Section 6 and Appendix A.
- **Thesis:** Ribeiro, [*Angelic Processes*](https://arxiv.org/abs/1505.04726v2), PhD thesis (2014), Chapter 5 and Appendix G.

It covers paper Definitions 26–45, Theorems 9–35, relevant numbered lemmas, and the main supporting thesis results. Routine record, substitution and automation facts are grouped at the end. **Support** denotes an implementation result without a separate numbered source claim; **Research** denotes the later parallel development.

## Alphabet and notation

Paper Definition 26 / thesis Definition 107 is implemented in [utp_rad_core.thy](../reactive-angelic-designs/utp_rad_core.thy):

```isabelle
type_synonym ('t, 'e) rad_state = "('t, 'e set) rea_vars_ext"
type_synonym ('t, 'e) reactive_angelic_design =
  "('t, 'e) rad_state angelic_design"
```

One `rad_state` has constructor `rea_vars_ext wait tr ref`, with `wait :: bool`, `tr :: 't`, and `ref :: 'e set`. The refusal set occupies the extension's `more` field. A complete RAD predicate has the schematic observation:

```text
P(ok, s, ok′, X)       s :: rad_state, X :: rad_state set
```

Each element of `X` has its own waiting flag, trace and refusal set. The two `ok` flags are outside these states. The type gives the alphabet; `P is RAD` additionally requires `RAD P = P`.

| Notation in this guide | Meaning / implementation |
| --- | --- |
| `P`, `Q` | Predicates on the RAD alphabet; healthiness is stated separately. |
| `D`, `E` | Ordinary predicates of type `('t, 'e set) rp_hrel`. |
| `P is H` | Ordinary design healthiness, written `P is 𝐇` in Isabelle. |
| `P ⊑ Q` | UTP refinement: `Q` implies `P` at every observation. |
| `P_f` | Initial waiting flag set to false: [`rad_wait_false`](../reactive-angelic-designs/utp_rad_healthy.thy#L557). |
| `F(P) = (P_f)^f`, `T(P) = (P_f)^t` | Also set final `ok′` to false / true. Initial `ok` remains free. |
| `𝒟(a,q) = (RA ∘ A)(a ⊢ q)` | Document shorthand for a reactive angelic design expression. |
| `U ◁ b ▷ V` | `U` if `b`, otherwise `V`. |
| `;;A` | [`aseq_ades`](../angelic-designs/utp_ades_ops.thy#L150): choice composition on the full design alphabet. |
| `;;RAD` | [`seq_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L704): the inherited angelic **design** sequential operator. |

`F`, `T` and `𝒟` are document abbreviations. Traces use the library's general `'t::trace` algebra; event-prefix results specialise to `'e list`.

## Healthiness definitions

For an initial state `s`, define the eligible and normalised final choices:

```text
E(s)   = {z. s.tr ≤ z.tr}
s₀     = s[tr := 0]
N(s,X) = {z[tr := z.tr − s.tr] | z ∈ X ∧ s.tr ≤ z.tr}

RA1 P(ok,s,ok′,X) = P(ok,s,ok′,E(s) ∩ X) ∧ E(s) ∩ X ≠ {}
RA2 P(ok,s,ok′,X) = P(ok,s₀,ok′,N(s,X))
II_Rac(ok,s,ok′,X) = (¬ok ∧ E(s) ∩ X ≠ {}) ∨ (ok′ ∧ s ∈ X)
RA3 P(ok,s,ok′,X) = if s.wait then II_Rac(ok,s,ok′,X) else P(ok,s,ok′,X)
```

RA1 filters choices and requires an eligible witness. RA2 removes the initial trace from each eligible outcome. RA3 gives identity behaviour while the preceding process is waiting.

| Paper / thesis definition | Implementation | Meaning or formula |
| --- | --- | --- |
| D27 / D108 | [`rad_trace_extensions`](../reactive-angelic-designs/utp_rad_healthy.thy#L10) | `E(s)` above. |
| D28 / D109 | [`RA1`](../reactive-angelic-designs/utp_rad_healthy.thy#L16) | Nonempty trace-extending choices. |
| D29 / D110 | [`RA2`](../reactive-angelic-designs/utp_rad_healthy.thy#L301) | Uses [`rad_zero_trace`](../reactive-angelic-designs/utp_rad_healthy.thy#L255), [`rad_trace_difference`](../reactive-angelic-designs/utp_rad_healthy.thy#L260), [`rad_normalise_choices`](../reactive-angelic-designs/utp_rad_healthy.thy#L267). |
| D30 / D111 | [`II_Rac`](../reactive-angelic-designs/utp_rad_healthy.thy#L513) | Reactive identity above. |
| D31 / D112 | [`RA3`](../reactive-angelic-designs/utp_rad_healthy.thy#L736) | Waiting behaviour above. |
| D32 / D113 | [`RA`](../reactive-angelic-designs/utp_rad_healthy.thy#L861) | `RA = RA1 ∘ RA2 ∘ RA3`. |
| D33 / D114 | [`CSPA1`](../reactive-angelic-designs/utp_rad_designs.thy#L10) | `CSPA1 P = P ∨ RA1(¬ok)`. |
| D34 / D115 | [`CSPA2`](../reactive-angelic-designs/utp_rad_designs.thy#L60) | `CSPA2 P = H2 P`. |
| D35 / D116 | [`RAD`](../reactive-angelic-designs/utp_rad_designs.thy#L86) | `RAD = RA ∘ CSPA1 ∘ CSPA2 ∘ PBMH_ades`. |

Composition applies from right to left. `PBMH_ades` is the full-alphabet form of the paper's upward closure in the final choice set. It is applied first: RA1 and PBMH do **not** commute in general (paper Example 11; [`RA1_PBMH_ades_not_commute`](../reactive-angelic-designs/utp_rad_healthy.thy#L228)).

### Idempotence, monotonicity and closure

All seven constituent/composite operators below are monotonic and idempotent on their stated predicate types; these properties do not require healthy inputs.

| Operator | Idempotence | Monotonicity |
| --- | --- | --- |
| RA1 | [`RA1_Idempotent`](../reactive-angelic-designs/utp_rad_healthy.thy#L135) | [`RA1_Monotonic`](../reactive-angelic-designs/utp_rad_healthy.thy#L142) |
| RA2 | [`RA2_Idempotent`](../reactive-angelic-designs/utp_rad_healthy.thy#L375) | [`RA2_Monotonic`](../reactive-angelic-designs/utp_rad_healthy.thy#L507) |
| RA3 | [`RA3_Idempotent`](../reactive-angelic-designs/utp_rad_healthy.thy#L820) | [`RA3_Monotonic`](../reactive-angelic-designs/utp_rad_healthy.thy#L855) |
| RA | [`RA_Idempotent`](../reactive-angelic-designs/utp_rad_healthy.thy#L1166) | [`RA_Monotonic`](../reactive-angelic-designs/utp_rad_healthy.thy#L1175) |
| CSPA1 | [`CSPA1_Idempotent`](../reactive-angelic-designs/utp_rad_designs.thy#L24) | [`CSPA1_Monotonic`](../reactive-angelic-designs/utp_rad_designs.thy#L17) |
| CSPA2 | [`CSPA2_Idempotent`](../reactive-angelic-designs/utp_rad_designs.thy#L74) | [`CSPA2_Monotonic`](../reactive-angelic-designs/utp_rad_designs.thy#L63) |
| RAD | [`RAD_Idempotent`](../reactive-angelic-designs/utp_rad_designs.thy#L191) | [`RAD_Monotonic`](../reactive-angelic-designs/utp_rad_designs.thy#L94) |

The thesis supplies the component algebra (including T.G.5.1 for CSPA1); the named `Idempotent`/`Monotonic` facts expose it to Isabelle's closure machinery.

| Source | Premises | Result | Implementation |
| --- | --- | --- | --- |
| Paper T9 / thesis T.5.2.1 | None | `RA1(A0 P) = RA1 P` | [`RA1_A0_absorb`](../reactive-angelic-designs/utp_rad_healthy.thy#L146) |
| Paper T10 | None | `RA1(CSPA1 P) = RA1(H1 P)` | [`RA1_CSPA1`](../reactive-angelic-designs/utp_rad_designs.thy#L34) |
| Thesis T.5.2.18 | None | `CSPA1(RA1 P) = RA1(H1 P)` | [`CSPA1_RA1`](../reactive-angelic-designs/utp_rad_designs.thy#L40) |
| Paper T71 / thesis T.5.2.10 | None | RA1 and RA2 commute. | [`RA1_RA2_commute`](../reactive-angelic-designs/utp_rad_healthy.thy#L407) |
| Paper T68 / thesis T.5.2.16 | None | RA1 and RA3 commute. | [`RA1_RA3_commute`](../reactive-angelic-designs/utp_rad_healthy.thy#L825) |
| Paper T69 / thesis T.5.2.17 | None | RA2 and RA3 commute. | [`RA2_RA3_commute`](../reactive-angelic-designs/utp_rad_healthy.thy#L829) |
| Paper T70 / thesis T.5.2.5 | None | `PBMH_ades(RA1(PBMH_ades P)) = RA1(PBMH_ades P)` | [`PBMH_ades_RA1_absorb`](../reactive-angelic-designs/utp_rad_healthy.thy#L174) |
| Paper T66 / thesis T.5.2.11 | None | Same absorption law for RA2. | [`PBMH_ades_RA2_absorb`](../reactive-angelic-designs/utp_rad_healthy.thy#L482) |
| Thesis T.5.2.15 | None | Same absorption law for RA3. | [`PBMH_ades_RA3_absorb`](../reactive-angelic-designs/utp_rad_healthy.thy#L815) |
| Paper T67 | `P is H` | `(RA ∘ A) P = (RA ∘ PBMH_ades) P` | [`RA_A`](../reactive-angelic-designs/utp_rad_healthy.thy#L926) |
| Thesis T.5.2.21 | `P is RAD` | `P is PBMH_ades` | [`RAD_is_PBMH_ades`](../reactive-angelic-designs/utp_rad_designs.thy#L107) |
| Support | `P is RAD` | `P is RA` | [`RAD_is_RA`](../reactive-angelic-designs/utp_rad_designs.thy#L225) |

**Printed correction:** paper T68 and thesis T.5.2.16 repeat one side of the equation. The implementation states the commutation law established by the proof. T67's design-healthiness premise is explicit; the predicate type alone does not supply it.

### Design normal form

Paper T11 / thesis T.5.2.20 gives the central representation theorem:

```text
RAD P = 𝒟(¬F(P), T(P))
```

[`RAD_design_form`](../reactive-angelic-designs/utp_rad_designs.thy#L118) holds for arbitrary `P`; [`RAD_design_form'`](../reactive-angelic-designs/utp_rad_designs.thy#L138) rewrites a RAD-healthy `P` itself into this form. For healthy `P`, [`RAD_RA_design_form`](../reactive-angelic-designs/utp_rad_designs.thy#L181) further gives `P = RA(¬F(P) ⊢ T(P))` because the extracted design is already PBMH-healthy.

| Source | Result / role | Implementation |
| --- | --- | --- |
| Paper L19 | `RA3 P = RA3(P_f)`. | [`RA3_wait_false_absorb`](../reactive-angelic-designs/utp_rad_healthy.thy#L840) |
| Paper L20–21 | Compute the failure/success projections of `𝒟(¬F(P),T(P))` through `RA2 ∘ RA1 ∘ PBMH_ades`. | [`RA_design_wf_ok_false`](../reactive-angelic-designs/utp_rad_healthy.thy#L1010), [`RA_design_wf_ok_true`](../reactive-angelic-designs/utp_rad_healthy.thy#L1038) |
| Paper L22 | `RA(a ⊢ q) = RA(a ⊢ RA2(RA1 q))`. | [`RA_design_post`](../reactive-angelic-designs/utp_rad_healthy.thy#L1055) |
| Paper L23 | `RA1(a ⊢ q) = RA1(¬RA1(¬a) ⊢ q)`. | [`RA1_design_pre`](../reactive-angelic-designs/utp_rad_healthy.thy#L130) |
| Thesis T.G.4.5 | Re-extracting the components of the constructed normal form gives the same process. | [`RA_design_form_idem`](../reactive-angelic-designs/utp_rad_healthy.thy#L1144) |
| Support | `P is H` and `P_f = P` imply `(RA ∘ A) P is RAD`. | [`RAD_design_closure`](../reactive-angelic-designs/utp_rad_designs.thy#L236) |

`rad_closure` packages the last rule for operator definitions. It checks design healthiness and initial-wait independence; it does not impose normality or independence from final choices.

## Direct correspondence with ordinary reactive predicates

The ordinary reactive alphabet is exactly `rad_state des_vars_scheme`. Therefore the generic AD maps [`p2ac`](../angelic-designs/utp_ades_designs.thy#L10) and [`ac2p`](../angelic-designs/utp_ades_designs.thy#L158) apply directly. Names such as `rad_p2ac_R` name **theorems**, not conversion wrappers.

```text
p2ac D(ok,s,ok′,X) = ∃z∈X. D((ok,s),(ok′,z))
ac2p P((ok,s),(ok′,z)) = ∃Y ⊆ {z}. P(ok,s,ok′,Y)
```

These are paper D23–24 ([`p2ac`](../angelic-designs/utp_ades_designs.thy#L10), [`ac2p_subset`](../angelic-designs/utp_ades_designs.thy#L199)). If `P is PBMH_ades`, the second expression reduces to `P(ok,s,ok′,{z})` ([`ac2p_healthy_obs`](../angelic-designs/utp_ades_designs.thy#L166)). For arbitrary `P`, the empty subset must still be considered.

### Healthiness mapping

Here `R` is the library's ordinary reactive healthiness `𝐑`.

| Source | Premises | Law | Implementation |
| --- | --- | --- | --- |
| Thesis T.G.7.1 | `P is PBMH_ades` | `ac2p(RA1 P) = R1(ac2p P)` | [`rad_ac2p_RA1`](../reactive-angelic-designs/utp_rad_csp.thy#L43) |
| Thesis T.G.7.2 | `P is PBMH_ades` | `ac2p(RA1(RA2 P)) = R1(R2(ac2p P))` | [`rad_ac2p_RA1_RA2`](../reactive-angelic-designs/utp_rad_csp.thy#L55) |
| Thesis T.G.7.3 | None | `ac2p(RA3 P) = R3c(ac2p P)` | [`rad_ac2p_RA3`](../reactive-angelic-designs/utp_rad_csp.thy#L87) |
| Paper T12 / thesis T.5.3.1 | `P is PBMH_ades` | `ac2p(RA P) = R(ac2p P)` | [`rad_ac2p_RA`](../reactive-angelic-designs/utp_rad_csp.thy#L102) |
| Paper T13 / thesis T.5.3.2 | None, at the displayed form | `ac2p(𝒟(¬F(P),T(P))) = R(¬ac2p(F(P)) ⊢ ac2p(T(P)))` | [`rad_ac2p_RA_design`](../reactive-angelic-designs/utp_rad_csp.thy#L111) |
| Thesis T.G.7.8 | None | `p2ac(R1 D) = RA1(p2ac D)` | [`rad_p2ac_R1`](../reactive-angelic-designs/utp_rad_csp.thy#L167) |
| Thesis T.G.7.9 | None | `p2ac(R1(R2 D)) = RA2(p2ac D)` | [`rad_p2ac_R1_R2`](../reactive-angelic-designs/utp_rad_csp.thy#L176) |
| Thesis T.G.7.10 | None | `p2ac(R3c D) = RA3(p2ac D)` | [`rad_p2ac_R3`](../reactive-angelic-designs/utp_rad_csp.thy#L196) |
| Paper T14 / thesis T.5.3.3 | None | `p2ac(R D) = RA(p2ac D)` | [`rad_p2ac_R`](../reactive-angelic-designs/utp_rad_csp.thy#L209) |
| Thesis L.G.7.2 | None | `p2ac II_C = II_Rac` | [`rad_p2ac_II_C`](../reactive-angelic-designs/utp_rad_csp.thy#L187) |
| Support | None | `ac2p II_Rac = II_C` | [`rad_ac2p_II_Rac`](../reactive-angelic-designs/utp_rad_csp.thy#L76) |

For paper T15 / thesis T.5.3.4, let `F_D = wait_f(D^f)` and `T_D = wait_f(D^t)` on the ordinary reactive alphabet. [`rad_p2ac_R_design`](../reactive-angelic-designs/utp_rad_csp.thy#L268) states:

```text
p2ac(R(¬F_D ⊢ T_D)) = 𝒟(¬p2ac(F_D), p2ac(T_D))
```

There are no extra premises for these projected components. The more general [`rad_p2ac_R_design_components`](../reactive-angelic-designs/utp_rad_csp.thy#L250) explicitly requires `p2ac F_D` and `p2ac T_D` to be independent of final `ok′`.

### Round trips and A2

| Source | Premises | Law | Implementation |
| --- | --- | --- | --- |
| Paper T16 / thesis T.5.3.5 | None | `ac2p(p2ac D) = D` | [`rad_ac2p_p2ac_inverse`](../reactive-angelic-designs/utp_rad_csp.thy#L278) |
| Paper L6 | None | `p2ac(ac2p P)(ok,s,ok′,X) = (∃y∈X. ∃Y⊆{y}. P(ok,s,ok′,Y))` | [`rad_p2ac_ac2p`](../reactive-angelic-designs/utp_rad_csp.thy#L284) |
| Support | None | `p2ac(ac2p P) = ac_non_empty ∧ A2 P` | [`rad_p2ac_ac2p_A2_form`](../reactive-angelic-designs/utp_rad_csp.thy#L293) |
| Paper T17 / thesis T.5.3.6 | `P is PBMH_ades` | `P ⊑ p2ac(ac2p P)` | [`rad_p2ac_ac2p_refine`](../reactive-angelic-designs/utp_rad_csp.thy#L301) |
| Thesis L.G.7.11 | `P is A2` | `p2ac(ac2p P) = ac_non_empty ∧ P` | [`rad_p2ac_ac2p_A2`](../reactive-angelic-designs/utp_rad_csp.thy#L312) |
| Paper T18 / thesis T.5.3.7 | `F(P)`, `T(P)` both A2 | `p2ac(ac2p(𝒟(¬F(P),T(P)))) = 𝒟(¬F(P),T(P))` | [`rad_p2ac_ac2p_RA_design`](../reactive-angelic-designs/utp_rad_csp.thy#L319) |
| Support | `P is RAD`, `P is A2` | `p2ac(ac2p P) = P` | [`rad_p2ac_ac2p_RAD_A2`](../reactive-angelic-designs/utp_rad_csp.thy#L369) |

A2 uses only empty and singleton choices ([`A2_obs`](../angelic-designs/utp_ades_healthy.thy#L1273)). RAD excludes empty final choice sets, so RAD + A2 gives an exact round trip. This is the implemented basis for the paper's CSP correspondence; unrestricted RAD predicates need not survive that round trip unchanged.

## Process operators

### Singleton choice and primitive definitions

Paper D36 / thesis D122 supplies the binder used in the postconditions:

```text
(∈ac y. B(y))(ok,s,ok′,X) = ∃y∈X. B(y)(ok,s,ok′,{y})
```

[`ades_singleton_choice`](../angelic-designs/utp_ades_healthy.thy#L1169) both selects `y` and evaluates its body with the choice set replaced by `{y}`. [`ac_singleton_choice`](../angelic-designs/utp_ades_healthy.thy#L1153) is its relation-level counterpart.

| Paper / thesis definition | Operator | Implementation / formula |
| --- | --- | --- |
| D37 / D117 | Angelic choice | [`achoice_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L10): `P ⊔RAD Q = P ∧ Q`. |
| D38 / D118 | Demonic choice | [`dchoice_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L101): `P ⊓RAD Q = P ∨ Q`. |
| D39 / D119 | Chaos | [`Chaos_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L183): `𝒟(false, ac_non_empty) = RAD true`. |
| D40 / D120 | Choice | [`Choice_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L240): `𝒟(true, ac_non_empty)`. |
| D41 / D121 | Stop | [`Stop_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L360): `𝒟(true, stop_post)`. |
| D42 / D123 | Skip | [`Skip_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L570): `𝒟(true, skip_post)`. |
| D43 / D124 | Event then Skip | [`PrefixSkip_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L722): `𝒟(true, prefix_post a)`. |
| Paper §6.4.7 / thesis §5.4.7 | Sequential composition | [`seq_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L704) reuses `angelic_design_seq`. |
| Thesis §5.4.8 | Compound prefix | [`Prefix_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L865): `a →RAD P = PrefixSkip_RAD a ;;RAD P`. |
| D44 / D125 | External choice | [`extchoice_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L902): `P □RAD Q = 𝒟(¬F(P) ∧ ¬F(Q), extchoice_post(T(P),T(Q)))`. |

The postconditions are easiest to read as formulas:

```text
stop_post     = ∈ac y. y.tr = s.tr ∧ y.wait
skip_post     = ∈ac y. y.tr = s.tr ∧ ¬y.wait
prefix_post a = ∈ac y. if y.wait
                      then y.tr = s.tr ∧ a ∉ y.ref
                      else y.tr = s.tr @ [a]

extchoice_post(U,V) = ∈ac y.
  if y.tr = s.tr ∧ y.wait then U ∧ V else U ∨ V
```

In the last line, `U` and `V` are evaluated at `{y}` by the binder. The definitions are [`stop_post`](../reactive-angelic-designs/utp_rad_ops.thy#L354), [`skip_post`](../reactive-angelic-designs/utp_rad_ops.thy#L565), [`prefix_post`](../reactive-angelic-designs/utp_rad_ops.thy#L712) and [`extchoice_post`](../reactive-angelic-designs/utp_rad_ops.thy#L876).

### Choice and primitive-process laws

Every row below assumes the displayed RAD operands are RAD-healthy. Prefix rows additionally use list traces.

| Paper / thesis result | Law | Implementation |
| --- | --- | --- |
| T19 / T.5.4.1 | `P ⊔RAD Q = 𝒟(¬F(P) ∨ ¬F(Q), (¬F(P) ⇒ T(P)) ∧ (¬F(Q) ⇒ T(Q)))` | [`RAD_angelic_choice_design`](../reactive-angelic-designs/utp_rad_ops.thy#L21) |
| T22 / T.5.4.4 | `P ⊓RAD Q = 𝒟(¬F(P) ∧ ¬F(Q), T(P) ∨ T(Q))` | [`RAD_demonic_choice_design`](../reactive-angelic-designs/utp_rad_ops.thy#L111) |
| T25 / T.5.4.8 | `Chaos_RAD ⊔RAD P = P` | [`Chaos_RAD_angelic_choice_unit`](../reactive-angelic-designs/utp_rad_ops.thy#L211) |
| Dual / T.5.4.7 | `Chaos_RAD ⊓RAD P = Chaos_RAD` | [`Chaos_RAD_demonic_choice_zero`](../reactive-angelic-designs/utp_rad_ops.thy#L225) |
| T26 / T.5.4.13 | `Choice_RAD ⊔RAD P = 𝒟(true,T(P))` | [`Choice_RAD_angelic_choice`](../reactive-angelic-designs/utp_rad_ops.thy#L295) |
| T27 / T.5.4.14 | `Choice_RAD ⊓RAD P = 𝒟(¬F(P),ac_non_empty)` | [`Choice_RAD_demonic_choice`](../reactive-angelic-designs/utp_rad_ops.thy#L330) |
| T28 / T.5.4.15 | `Stop_RAD ⊔RAD P = 𝒟(true,(¬F(P) ⇒ T(P)) ∧ stop_post)` | [`Stop_RAD_angelic_choice`](../reactive-angelic-designs/utp_rad_ops.thy#L537) |
| T29 / T.5.4.18 | `Skip_RAD ⊔RAD P = 𝒟(true,skip_post ∧ (¬F(P) ⇒ T(P)))` | [`Skip_RAD_angelic_choice`](../reactive-angelic-designs/utp_rad_ops.thy#L669) |
| T31 / T.5.4.26 | `PrefixSkip_RAD a ⊔RAD P = 𝒟(true,(¬F(P) ⇒ T(P)) ∧ prefix_post a)` | [`PrefixSkip_RAD_angelic_choice`](../reactive-angelic-designs/utp_rad_ops.thy#L835) |
| T32 / T.5.4.30 | `P □RAD Stop_RAD = 𝒟(¬F(P), ∈ac(T(P)))` | [`extchoice_RAD_Stop`](../reactive-angelic-designs/utp_rad_ops.thy#L976) |
| T33 / T.5.4.31 | **Also `P is A2`:** `P □RAD Stop_RAD = P`. | [`extchoice_RAD_Stop_unit`](../reactive-angelic-designs/utp_rad_ops.thy#L1006) |

Both choices distribute over each other without healthiness premises: [`RAD_angelic_demonic_distrib`](../reactive-angelic-designs/utp_rad_ops.thy#L169), [`RAD_demonic_angelic_distrib`](../reactive-angelic-designs/utp_rad_ops.thy#L175) (paper §6.4.2).

### Sequential composition and general prefix

Paper T30 / thesis T.5.4.21 is [`RAD_seq_design`](../reactive-angelic-designs/utp_rad_seq.thy#L276). For `P`, `Q` both RAD-healthy, write `J = ades_state_choice`, so `J(ok,s,ok′,X)` means `s ∈ X`. Then:

```text
P ;;RAD Q = 𝒟(pre, post)

pre  = ¬(RA1(F(P)) ;;A RA1(true))
       ∧ ¬(RA1(T(P)) ;;A (¬s.wait ∧ RA2(RA1(F(Q)))))

post = RA1(T(P)) ;;A
       (J ◁ s.wait ▷ RA2(RA1(¬F(Q) ⇒ T(Q))))
```

The first conjunct excludes failure in `P`; the second excludes handing a terminating outcome to a failing `Q`. A waiting intermediate state is retained by `J`. The `;;A` inside these formulas is distinct from `;;RAD`.

Thesis T.5.4.29 is [`Prefix_RAD_design`](../reactive-angelic-designs/utp_rad_seq.thy#L480). For `P is RAD`:

```text
a →RAD P = 𝒟(¬prefix_handover a (RA2(RA1(F(P)))),
                 prefix_continuation a (RA2(RA1(T(P)))))
```

[`prefix_handover`](../reactive-angelic-designs/utp_rad_seq.thy#L404) and [`prefix_continuation`](../reactive-angelic-designs/utp_rad_seq.thy#L413) name the intermediate-state predicates in that calculation. [`Prefix_Skip_RAD_RA`](../reactive-angelic-designs/utp_rad_seq.thy#L569) proves that compound prefix followed by `Skip_RAD` agrees with the primitive `PrefixSkip_RAD` definition.

### Operator closure

These are implementation closure rules; the thesis-numbered A2 results are identified explicitly.

| Operation | Premises | Closure | Implementation |
| --- | --- | --- | --- |
| Angelic / demonic choice | `P`, `Q` both RAD | RAD | [`RAD_angelic_closure`](../reactive-angelic-designs/utp_rad_ops.thy#L48), [`RAD_demonic_closure`](../reactive-angelic-designs/utp_rad_ops.thy#L133) |
| Chaos / Choice / Stop / Skip / primitive prefix | None | RAD | [`Chaos_RAD_is_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L206), [`Choice_RAD_is_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L250), [`Stop_RAD_is_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L505), [`Skip_RAD_is_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L637), [`PrefixSkip_RAD_is_RAD`](../reactive-angelic-designs/utp_rad_ops.thy#L803) |
| Stop / Skip / primitive prefix | None | A2 | [`Stop_RAD_is_A2`](../reactive-angelic-designs/utp_rad_ops.thy#L524), [`Skip_RAD_is_A2`](../reactive-angelic-designs/utp_rad_ops.thy#L656), [`PrefixSkip_RAD_is_A2`](../reactive-angelic-designs/utp_rad_ops.thy#L822) |
| `P ;;RAD Q` | `P`, `Q` both RAD | RAD | [`RAD_seq_closure`](../reactive-angelic-designs/utp_rad_seq.thy#L353) |
| `P ;;RAD Q` | `P`, `Q` both RAD and A2 | A2 | [`RAD_seq_A2_closure`](../reactive-angelic-designs/utp_rad_seq.thy#L363) (T.5.4.25) |
| `a →RAD P` | `P is RAD` / `P is A2`, respectively | RAD / A2 | [`Prefix_RAD_closure`](../reactive-angelic-designs/utp_rad_seq.thy#L368), [`Prefix_RAD_A2_closure`](../reactive-angelic-designs/utp_rad_seq.thy#L374) |
| `P □RAD Q` | `P`, `Q` both RAD | RAD | [`extchoice_RAD_closure`](../reactive-angelic-designs/utp_rad_ops.thy#L937) |
| `P □RAD Q` | `P`, `Q` both RAD and A2 | A2 | [`extchoice_RAD_A2_closure`](../reactive-angelic-designs/utp_rad_ops_csp.thy#L130) (T.5.4.35) |

### Operator mapping laws

Plain `⊔` and `⊓` on ordinary predicates mean conjunction and disjunction in the UTP refinement lattice. `csp_extchoice` and `PrefixSkip_R` are the explicit ordinary operators in [utp_rad_ops_csp.thy](../reactive-angelic-designs/utp_rad_ops_csp.thy), following thesis D64 and D62.

| Source | Premises | Law | Implementation |
| --- | --- | --- | --- |
| Paper T20 / thesis T.5.4.2 | None | `ac2p(p2ac D ⊔RAD p2ac E) = D ⊔ E` | [`RAD_angelic_choice_CSP`](../reactive-angelic-designs/utp_rad_ops.thy#L63) |
| Paper T21 / thesis T.5.4.3 | `P`, `Q` both RAD | `P ⊔RAD Q ⊑ p2ac(ac2p P ⊔ ac2p Q)` | [`RAD_angelic_choice_CSP_refine`](../reactive-angelic-designs/utp_rad_ops.thy#L79) |
| Paper T23 / thesis T.5.4.5 | None | `p2ac(ac2p P ⊓ ac2p Q) = p2ac(ac2p P) ⊓RAD p2ac(ac2p Q)` | [`RAD_demonic_choice_CSP_distrib`](../reactive-angelic-designs/utp_rad_ops.thy#L147) |
| Paper L7 / thesis L.5.4.1 | `P`, `Q` both RAD and A2 | `p2ac(ac2p P ⊓ ac2p Q) = P ⊓RAD Q` | [`RAD_demonic_choice_CSP_A2`](../reactive-angelic-designs/utp_rad_ops.thy#L153) |
| Paper T24 / thesis T.5.4.6 | None | `ac2p(p2ac D ⊓RAD p2ac E) = D ⊓ E` | [`RAD_demonic_choice_CSP`](../reactive-angelic-designs/utp_rad_ops.thy#L162) |
| Support | None | `p2ac(D ;; E) = p2ac D ;;RAD p2ac E` | [`rad_p2ac_seq`](../reactive-angelic-designs/utp_rad_seq.thy#L19) |
| Thesis T.5.4.22 | `P`, `Q` both RAD | `P ;;RAD Q ⊑ p2ac(ac2p P ;; ac2p Q)` | [`RAD_seq_CSP_refine`](../reactive-angelic-designs/utp_rad_seq.thy#L25) |
| Thesis T.5.4.23 | `P`, `Q` both RAD and A2 | `p2ac(ac2p P ;; ac2p Q) = P ;;RAD Q` | [`RAD_seq_CSP_A2`](../reactive-angelic-designs/utp_rad_seq.thy#L34) |
| Thesis T.5.4.24 | None | `ac2p(p2ac D ;;RAD p2ac E) = D ;; E` | [`RAD_seq_CSP_inverse`](../reactive-angelic-designs/utp_rad_seq.thy#L42) |
| Thesis T.5.4.27–28 | List traces | `ac2p(PrefixSkip_RAD a) = PrefixSkip_R a`, and conversely via `p2ac`. | [`rad_ac2p_PrefixSkip_RAD`](../reactive-angelic-designs/utp_rad_ops_csp.thy#L50), [`rad_p2ac_PrefixSkip_R`](../reactive-angelic-designs/utp_rad_ops_csp.thy#L34) |
| Support / thesis T.5.4.32 | None | `p2ac(csp_extchoice D E) = p2ac D □RAD p2ac E`; applying `ac2p` recovers `csp_extchoice D E`. | [`rad_p2ac_extchoice`](../reactive-angelic-designs/utp_rad_ops_csp.thy#L80), [`RAD_extchoice_CSP`](../reactive-angelic-designs/utp_rad_ops_csp.thy#L106) |
| Thesis T.5.4.33 | `P`, `Q` both RAD | `P □RAD Q ⊑ p2ac(csp_extchoice (ac2p P) (ac2p Q))` | [`RAD_extchoice_CSP_refine`](../reactive-angelic-designs/utp_rad_ops_csp.thy#L112) |
| Thesis T.5.4.34 | `P`, `Q` both RAD and A2 | The preceding refinement is an equality. | [`RAD_extchoice_CSP_A2`](../reactive-angelic-designs/utp_rad_ops_csp.thy#L121) |

## Non-divergence

Paper D45 / thesis D126 defines [`NDRAD`](../reactive-angelic-designs/utp_rad_nd.thy#L9):

```text
NDRAD P = P ⊔RAD Choice_RAD
```

| Source | Premises | Result | Implementation |
| --- | --- | --- | --- |
| Thesis T.5.5.1 | None | `NDRAD(NDRAD P) = NDRAD P` | [`NDRAD_idem`](../reactive-angelic-designs/utp_rad_nd.thy#L12) |
| Support | None | NDRAD is monotonic. | [`NDRAD_Monotonic`](../reactive-angelic-designs/utp_rad_nd.thy#L23) |
| Support | `P is RAD` | `NDRAD P is RAD` | [`NDRAD_RAD_closure`](../reactive-angelic-designs/utp_rad_nd.thy#L26) |
| Paper T34 / thesis T.5.5.2 | `P is RAD` | `NDRAD P = 𝒟(true,T(P))` | [`NDRAD_design_form`](../reactive-angelic-designs/utp_rad_nd.thy#L34) |
| Paper T35 / thesis T.5.5.3, **qualified** | `P is RAD` | `NDRAD P = P ⟷ (∀observations. ok ⇒ ¬F(P))` | [`NDRAD_fixed_point`](../reactive-angelic-designs/utp_rad_nd.thy#L43) |
| Thesis T.G.6.1; derived closure | `P`, `Q` both RAD and NDRAD | Sequential normal form has precondition `true`; `P ;;RAD Q is NDRAD`. | [`NDRAD_seq_design`](../reactive-angelic-designs/utp_rad_nd.thy#L89), [`NDRAD_seq_closure`](../reactive-angelic-designs/utp_rad_nd.thy#L142) |

The initial-`ok` guard in T35 is essential with the explicit design observations. The printed unguarded statement is refuted by `Choice_RAD` at an unstarted observation: [`theorem35_counterexample`](../reactive-angelic-designs/utp_rad_nd.thy#L180). No normality restriction is introduced here.

## Worked examples and numbered lemmas

These source calculations are in [utp_rad_examples.thy](../reactive-angelic-designs/utp_rad_examples.thy). Prefix examples use list traces; consult each linked statement for its event premises.

| Paper result | Calculation / role | Implementation |
| --- | --- | --- |
| Ex11 | RA1 and PBMH disagree on an empty-choice predicate. | [`RA1_PBMH_ades_ac_empty_example`](../reactive-angelic-designs/utp_rad_examples.thy#L15) |
| Ex12; L5 | Angelic choice between differently prefixed deadlocks; ordinary CSP comparison (`a ≠ b`). | [`Prefix_Stop_Stop_angelic_choice`](../reactive-angelic-designs/utp_rad_examples.thy#L433), [`Prefix_Stop_Stop_R`](../reactive-angelic-designs/utp_rad_examples.thy#L488) |
| Ex13 | Maps the ordinary reactive identity to `II_Rac`. | [`rad_p2ac_Skip_R`](../reactive-angelic-designs/utp_rad_examples.thy#L622) |
| Ex14 | Singleton round trip of the two-prefix postcondition (`a ≠ b`). | [`rad_p2ac_ac2p_prefix_stop_pair`](../reactive-angelic-designs/utp_rad_examples.thy#L636) |
| Ex15; L8 / thesis L.5.4.2 | Choice of Stop and Skip; its CSP image is the reactive top. | [`Stop_Skip_angelic_choice`](../reactive-angelic-designs/utp_rad_examples.thy#L23), [`rad_ac2p_Stop_Skip`](../reactive-angelic-designs/utp_rad_examples.thy#L64) |
| L9 / thesis L.5.4.3 | `(Stop_RAD ⊔RAD Skip_RAD) ;;RAD Chaos_RAD = Stop_RAD`. | [`Stop_Skip_seq_Chaos`](../reactive-angelic-designs/utp_rad_examples.thy#L83) |
| Ex16 / thesis Ex33 | Prefixed deadlock avoids the divergence reached through the terminating branch. | [`Prefix_Stop_Skip_seq_Chaos`](../reactive-angelic-designs/utp_rad_examples.thy#L272) |
| Ex17 / thesis Ex34 | Termination is chosen over divergence after the same prefix. | [`Prefix_Skip_Chaos_angelic_choice`](../reactive-angelic-designs/utp_rad_examples.thy#L380) |
| Ex18 | Different prefixed events (`a ≠ b`) expose RAD's preservation of trace history. | [`Prefix_Skip_Chaos_different_events`](../reactive-angelic-designs/utp_rad_examples.thy#L593) |
| Ex19 | External choice with Stop prevents choosing an event leading to divergence. | [`Prefix_Chaos_Chaos_extchoice_Stop`](../reactive-angelic-designs/utp_rad_examples.thy#L673) |
| Ex20–21 | `NDRAD Chaos_RAD = Choice_RAD`; primitive prefix is a fixed point. | [`NDRAD_Chaos_example`](../reactive-angelic-designs/utp_rad_examples.thy#L521), [`NDRAD_Prefix_Skip`](../reactive-angelic-designs/utp_rad_examples.thy#L526) |

## Parallel research

Parallel-by-merge is an extension of this repository's paper development. Its definitions and closure conditions are documented separately in [RAD parallel](RAD_PARALLEL.md); they have no numbered RAD parallel counterpart in the source material indexed above.

| Research result | Premises | Implementation |
| --- | --- | --- |
| Lift an ordinary reactive merge using nonempty branch choices and `∀left ∀right ∃output` coverage. | None | [`rad_lift_merge`](../reactive-angelic-designs/utp_rad_parallel.thy#L276) |
| RADm is a monotonic, idempotent transformer on ordinary reactive merges. | None | [`RADm`](../reactive-angelic-designs/utp_rad_parallel.thy#L170), [`RADm_Monotonic`](../reactive-angelic-designs/utp_rad_parallel.thy#L187), [`RADm_Idempotent`](../reactive-angelic-designs/utp_rad_parallel.thy#L184) |
| `p2ac(RD D) = RAD(p2ac D)`. | None | [`rad_p2ac_RD`](../reactive-angelic-designs/utp_rad_parallel.thy#L370) |
| `ac2p P is RD`. | `P` both RAD and A2 | [`rad_ac2p_RD`](../reactive-angelic-designs/utp_rad_parallel.thy#L444) |
| Raw lifted parallel is RAD-healthy; applying RAD afterwards is redundant. | `P`, `Q` both RAD and A2; `M is RADm` | [`rad_par_raw_RADm`](../reactive-angelic-designs/utp_rad_parallel.thy#L455), [`rad_par_eq_raw`](../reactive-angelic-designs/utp_rad_parallel.thy#L461) |

The migration-only [representation comparison](../reactive-angelic-designs/utp_rad_representation.thy) checks correspondence with the former custom record. Its encode/decode definitions are not used by the RAD implementation or by the proofs above.

## Where to find supporting lemmas

| File | Supporting material |
| --- | --- |
| [utp_rad_core](../reactive-angelic-designs/utp_rad_core.thy) | Native record selectors, updates, cases and lenses; implementation support for D26. |
| [utp_rad_healthy](../reactive-angelic-designs/utp_rad_healthy.thy) | Trace-set algebra; `ok`/wait substitution and independence; RA distribution and composition. `RA1_conj/disj`, `RA2_conj/disj`, `RA3_conj/disj` correspond to thesis T.5.2.2–3, 6–7, 12–13. |
| [utp_rad_designs](../reactive-angelic-designs/utp_rad_designs.thy) | Healthy components, bounds and normal-form closure. |
| [utp_rad_csp](../reactive-angelic-designs/utp_rad_csp.thy) | Component mapping, substitution and round-trip lemmas. |
| [utp_rad_ops](../reactive-angelic-designs/utp_rad_ops.thy) | Primitive postcondition normalisation, substitutions and healthiness. |
| [utp_rad_seq](../reactive-angelic-designs/utp_rad_seq.thy) | RA1/RA sequential normal forms (T.G.8.6 / T.G.8.5); prefix handover and continuation calculations. |
| [utp_rad_ops_csp](../reactive-angelic-designs/utp_rad_ops_csp.thy) | Explicit ordinary prefix/external-choice definitions and correspondence. |
| [utp_rad_nd](../reactive-angelic-designs/utp_rad_nd.thy) | Non-divergence and the guarded T35 characterisation. |

This is an index of the implemented results, not a claim that every theorem in thesis Chapter 5 has a separate mechanisation. In particular, the general sequential algebra should not be inferred from closure or mapping laws; retain the qualifications described in [Semantic notes](SEMANTIC_NOTES.md).
