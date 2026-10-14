# Paper and thesis correspondence review

Reviewed on 2026-10-14 at commit `e01d4309c857382e7990615c17f037153330bcaf`. This report records findings and proposed documentation changes; the corrections below have not been applied.

The review covers the non-parallel mappings in [AD](../paper/AD.md), [RAD](../paper/RAD.md), [AP](../paper/AP.md), and the [coverage index](../paper/README.md): source statements, documented formulas and premises, and linked Isabelle declarations. It includes the mapped definitions, main theorems, appendix results and examples, with selected thesis results rather than the whole thesis. AP's numbered theorem statements and premises matched. There are documentation errors and some explicit differences from the literal printed sources in AD and RAD.

In the initial review, all 366 declaration links in the non-parallel body of the three guides resolved to the expected names. This is a source-level correspondence review, not a fresh Isabelle build or replay of the proofs. Parallel operators and the standalone associativity audit were excluded.

## Sources and line links

- Ribeiro and Cavalcanti, [Angelic processes for CSP via the UTP](https://doi.org/10.1016/j.tcs.2018.10.008), TCS 756 (2019), pp19–63. Page references below are printed journal pages; in the reviewed PDF, subtract 18 for the PDF page number.
- Ribeiro, [Angelic Processes](https://arxiv.org/abs/1505.04726v2), PhD thesis, December 2014, arXiv version 2. Printed and PDF page numbers coincide for the reviewed passages.

Exact documentation and theory links below are pinned to the reviewed commit. They preserve the evidence after the working guides are edited. The guide links above follow the current checkout. The review used the local copies `angelic-paper.pdf` and `angelic-thesis.pdf`; ambiguous notation was checked on rendered pages.

## Findings and recommended corrections

### 1. RAD Example 13 points to reactive identity instead of CSP Skip

**Locations:** [docs/RAD.md:328][ref1]; [rad_p2ac_Skip_R][ref2] and its preceding source comment. The underlying identity result is [rad_p2ac_II_C][ref3].

**Assessment:** Paper Example 13, p39, starts from `Skip_R = R(true ⊢ tr′ = tr ∧ ¬wait′)` and maps it to the process represented by `Skip_RAD`. The linked Isabelle lemma instead states `p2ac II_C = II_Rac`. This is a valid reactive-identity result, but it is not that example. Identity preserves the complete inner state, including refusals; the source Skip permits a terminating same-trace state with different refusals. The mismatch affects the claimed correspondence, not the truth of the identity lemma.

**Recommended correction:** Describe Example 13 as the Skip calculation. Link a full matching theorem if one is established; otherwise say that its process-level correspondence is not supplied by the current link. Keep the identity lemma under its actual source counterpart, thesis L.G.7.2, p588. Correct the misleading theory comment separately; renaming or replacing the lemma needs a caller check and is not necessary for the documentation fix.

### 2. RAD Theorem 29 silently corrects the printed success projection

**Locations:** [docs/RAD.md:234][ref4]; [Skip_RAD_angelic_choice][ref5].

**Assessment:** Paper T29, p43, and thesis T.5.4.18, p164, print `P_t^t`; Isabelle and the guide use `P_f^t`, setting initial waiting to false. This is a real difference from the printed formula. The implemented form follows the general angelic-choice and design-normal-form laws. For a RAD predicate, the printed `P_t^t` selects waiting identity behaviour instead of the process's started success behaviour. The thesis proof repeats the wrong projection on pp638–639. The printed parenthesis placement also needs correction.

**Recommended correction:** Keep the Isabelle statement. Add a short note immediately below the row: “The paper and thesis print `P_t^t`; this formula uses `P_f^t`, as required by the design normal form and general choice law.” Mention T29 alongside the already recorded T68 printing correction in the coverage index. The new source-level explanation was not separately formalised as a counterexample during this review.

### 3. The AD right-identity result is faithful to the thesis

**Locations:** [docs/AD.md:182][ref6], [docs/PAPER_COVERAGE.md:44][ref7], [docs/SEMANTIC_NOTES.md:49][ref8]; [Skip_AD_seq_right_unit_iff][ref9] and [Skip_AD_seq_right_unit_iff_normal][ref10].

**Assessment:** Thesis T.4.5.8, p120, already states that an A-healthy design has right identity exactly when its precondition is independent of final choices. Isabelle expresses this equivalently as normality. Calling it “qualified” alongside repairs to source claims misleadingly suggests the mechanisation added a restriction absent from the thesis.

**Recommended correction:** Remove “qualified” from this row. Retain the normality premise and the warning against unconditional right identity, phrased as agreement with the thesis. Update the coverage index and semantic notes consistently so they do not present this as a source defect.

### 4. AD relation-composition closure cites the wrong thesis section

**Locations:** [docs/AD.md:178][ref11]; [PBMH_aseq_closure][ref12].

**Assessment:** The stated law matches thesis T.F.3.1, p478: composition of two PBMH-healthy relations is PBMH-healthy. The cited §4.4 concerns refinement and lattice extremes.

**Recommended correction:** Replace “Thesis §4.4” with “Thesis T.F.3.1, p478”. The formula, premises and implementation link can remain.

### 5. AP sequential composition and prefix cite nonexistent paper subsections

**Locations:** [docs/AP.md:120][ref13] and [docs/AP.md:121][ref14].

**Assessment:** The paper headings are §7.3.7, p52, and §7.3.8, p53, rather than §7.4.7 and §7.4.8. The thesis references §6.4.7 and §6.4.8 and both implementation links are correct.

**Recommended correction:** Change only the paper subsection numbers.

### 6. RAD Example 14 links a supporting calculation rather than the full process equation

**Locations:** [docs/RAD.md:329][ref15]; [rad_p2ac_ac2p_prefix_stop_pair][ref16].

**Assessment:** Paper Example 14, p40, and thesis Example 31, p155, map the entire two-prefix process. The linked lemma maps the conjunction of its postconditions. The current description accurately says “postcondition”, but the example label can still suggest complete coverage of the source equation.

**Recommended correction:** Say “Supporting postcondition calculation for Example 14”. A future process-level theorem can replace that wording once established. Preserve the explicit `a ≠ b` premise.

### 7. Some implementation statements are stronger than the cited thesis statements

**Locations:** [docs/AD.md:179][ref17] with [angelic_design_seq_A_closure][ref18]; [docs/RAD.md:297][ref19]; [docs/RAD.md:361][ref20] with [RA1_design_seq][ref21] and [RA_design_seq][ref22].

**Assessment:**

- Thesis T.4.5.3, pp118–119, prints both A-healthiness and independence of `ok, ok′` for its operands. Isabelle proves A-closure with just A-healthiness. The unusual printed independence condition may be a source mistake or an intended component-level proviso; its intention was not established.
- Thesis T.5.4.32, p172, describes CSP-process operands. The implementation's equation for its explicitly defined external-choice helper needs no healthy-input premise.
- Thesis T.G.8.5–6, pp649/659, impose stronger component independence and PBMH assumptions than the corresponding Isabelle component calculations.

**Recommended correction:** Keep the actual Isabelle premises in the tables. Add brief prose beside these entries explaining that the implementation proves a more general statement. No new classification column or theorem weakening is needed.

### 8. AD Theorems 6 and 8 retain a genuine additional A3 premise

**Locations:** [docs/AD.md:125][ref23], [docs/AD.md:127][ref24], [docs/AD.md:131][ref25]; [d2ac_ac2p_iff_A3][ref26], [d2ac_ac2p][ref27], [d2ac_ac2p_A2_eq][ref28].

**Assessment:** Paper T6/T8, p34, and thesis T.4.6.8/T.4.6.10, pp133–134, omit A3. The mechanisation includes it. The existing `P_dummy` counterexample and the A3 characterisation justify the qualification on the implemented carrier. This difference is already clearly documented; it must not disappear in a readability pass.

**Recommended correction:** Retain the explicit premises and the nearby counterexample link. Keep the explanation in AD as the authoritative account; the coverage index needs only a short pointer. Do not describe the equality as unconditional on A+A2.

### 9. RAD Theorem 35 retains the initial ok guard

**Locations:** [docs/RAD.md:315][ref29]; [NDRAD_fixed_point][ref30] and [theorem35_counterexample][ref31].

**Assessment:** Paper T35, p46, and thesis T.5.5.3, p175, print an unguarded universal failure test. Isabelle uses `ok ⇒ ¬F(P)` on full observations. The existing `Choice_RAD` counterexample establishes why the unguarded reading is unsuitable for those observations. The current guide explains this correctly.

**Recommended correction:** Preserve the guard in the formula and its nearby explanation. Keep it visible when simplifying notation or moving rows; no additional normality premise is needed.

### 10. Keep the existing T67 domain premise and T68 printing correction

**Locations:** [docs/RAD.md:98][ref32], [docs/RAD.md:103][ref33], [docs/RAD.md:107][ref34]; [RA1_RA3_commute][ref35] and [RA_A][ref36].

**Assessment:** Paper T67, p57, uses “A1 is PBMH” in its proof. Isabelle makes the required design-healthiness premise explicit. This is a domain restriction, not something provided by the predicate type alone. Paper T68 on the same page and thesis T.5.2.16, p146, repeat one side of an equation; their proofs establish the commutation implemented in Isabelle.

**Recommended correction:** Retain both explanations. Present T67 as an explicit domain premise and T68 as a printing correction, in ordinary prose rather than adding a classification system.

## Agreed documentation layout and progress

Updated on 2026-10-14 after the reader-navigation discussion. This plan supersedes the original recommendations below. The findings and pinned evidence above remain unchanged; their corrections are still deferred.

- [x] Keep [paper coverage](../paper/README.md) as a short landing page with layer links and theorem ranges.
- [x] Organise AD by paper §5.1–5.6, RAD by §6.1–6.5, and AP by §7.1–7.3, with alphabet/background material first.
- [x] Group existing definitions, theorems, lemmas and examples under their paper topics. Keep brief descriptions, essential premises and direct Isabelle links; add no full statements or proof explanations.
- [x] Place existing thesis references and implementation support in collapsed **Supplementary results** blocks beneath their related topics. Keep paper-referenced operator entries visible in the main tables.
- [x] Put paper appendix theorems and lemmas together near the end of AD/RAD, followed by the theory-file map. Preserve the existing parallel material without revising it.
- [x] Preserve numbered anchors and update contents and coverage-page links. Following the requested anchor cleanup, section links use Markdown heading anchors rather than redundant HTML aliases.
- [x] Check move integrity: all 157 numbered entries and 46 supplementary rows retained once, with existing premises and Isabelle links preserved; local navigation targets checked.
- [x] Step 4: verify the reorganised guides against the linked declarations, source section order and reader-navigation routes; see the results below.
- [ ] Later: address the documented correspondence corrections. Proof changes, if needed, require a separate task.

Adding missing thesis coverage and a correspondence-classification scheme is outside the agreed work. No additional layer guides are needed.

The subsequent documentation cleanup retired `SEMANTIC_NOTES.md`: unique lifting, closure, composition and singleton-evaluation notes moved into AD supplementary blocks; native representation details moved to RAD’s theory-file section; migration history now lives beside the [RAD parallel representation notes](../parallel/RAD.md#common-notations), following retirement of the separate research-scope page. Repeated qualifications remain beside their existing layer-guide entries. The pinned historical evidence for the retired file is retained below.

The folder reorganisation places the source-navigation guides in `docs/paper/`
and the parallel notes in `docs/parallel/`, each with a short `README.md`.
The [documentation index](../README.md) links both reading paths, build checks
and this review. At that stage the AD parallel guide retained its reviewed prose,
formulas, tables and layout; only its link paths changed. RAD/AP use similar
definition-and-premise tables, with AP's divergence example after the laws.
Local links were updated, including audit references; historical evidence URLs
remain pinned to their original paths. The findings above remain deferred.

A later requested cleanup shortened the AD parallel guide's last two sections
to definitions, core properties and closure/mapping results. Standalone examples
and unused supporting laws were removed from its Isabelle theory; the retained
statements and proofs are unchanged. `A3j w` remains a candidate construction,
without changing the definition of `ades_par`.

## Step 4 verification results

Completed on 2026-10-14 against the current working guides. This checks the documentation after restructuring; it does not certify that every retained correspondence agrees with the printed sources. The findings above remain open.

| Check | Result |
| --- | --- |
| Numbered entries | All 157 occur once: D15–57, T3–72, L3–28 and Ex11–28. AD has 31, RAD 74 and AP 52. |
| Content preservation | All numbered rows and 46 supplementary rows retain their prior descriptions, premises and Isabelle links. |
| Declaration links | All 237 line links in the non-parallel guide bodies land on the named declaration: AD 59, RAD 110, AP 68. The five whole-theory links also resolve. |
| Local navigation | All 55 Markdown fragment links across the guides, landing page, README and this report resolve. Numbered anchors are retained; redundant section aliases were subsequently removed at the user’s request and their links redirected to Markdown headings. Collapsed blocks are balanced. |
| Paper section placement | All 157 numbered entries checked against the local paper text. One misplaced entry was corrected, as described below. |
| Premises and qualifications | Retained summaries checked against the current declarations, including component-form restrictions, healthy-image equations, list-trace restrictions and example inequalities. No new discrepancy was found in those premise summaries. |
| Prior evidence | All 43 pinned evidence links resolve to existing lines in the locally available reviewed commit. All 18 linked theory files match that commit byte-for-byte. |

**Layout correction:** [RAD D36](../paper/RAD.md#d36), the singleton-choice binder, had been placed under §6.4 Operators. The paper introduces it in §6.3.1, p38, immediately before Example 12. Its unchanged row now sits there. This fixes the new navigation layout without applying any of the deferred mathematical/source-reference corrections.

The representative reader routes are:

| Result | Route through the current docs | Qualification checked |
| --- | --- | --- |
| [AD T6](../paper/AD.md#t6) | Coverage qualifications → T6 → declaration | A and A3; nearby counterexample link. |
| [RAD T29](../paper/RAD.md#t29) | RAD guide → Operators → Skip → T29 → declaration | RAD premise. The missing printed-correction note remains finding 2. |
| [RAD T35](../paper/RAD.md#t35) | Coverage qualifications → T35 → declaration | RAD premise and initial-ok guard; nearby counterexample. |
| [Thesis T.4.5.8](../paper/AD.md#composition-support) | Coverage qualifications → AD composition support → expand Supplementary results → row → declaration | A premise and right identity iff normality. The misleading “qualified” label remains finding 3. |
| [AP T63](../paper/AP.md#t63) | AP guide → Operators → Sequence → T63 → declaration | Both operands AP and NDAP; no associativity claim. |

These are Markdown/anchor checks, not browser interaction tests. The short landing page intentionally does not provide a one-click entry for every theorem; the topic links supply the intermediate steps. No fresh Isabelle build, proof replay, parallel-operator review or expanded thesis-coverage audit was performed.

<details>
<summary>Original recommendations and work order (superseded)</summary>

## Tidying the current reader documentation

The existing division is useful: a coverage entry point and one guide per semantic layer. Keep those files and improve the routes through them. A reader should be able to go from a source number to its statement, exact premises and Isabelle declaration without first learning the implementation's file layout.

### Make the coverage index the source-number entry point

Extend [PAPER_COVERAGE.md](../paper/README.md) with compact source-ordered lookup tables. Use **paper reference**, **thesis reference**, **topic**, and **guide link**. Give each numbered theorem an individually searchable entry; use separate small tables for definitions, lemmas and examples. These index rows should link to the authoritative layer-guide entry rather than repeat its formula and premises. Index the thesis results actually covered; do not suggest that all thesis results are mechanised.

For example, a paper reader looking for T29 should reach the Skip choice law and its printed-correction note directly. A thesis reader looking for T.4.5.8 should reach the right-identity equivalence. Add stable anchors to source entries where a section link is too broad. Keep the current topic table for readers who know a concept rather than a theorem number.

### Give the three layer guides the same reading pattern

Use the existing content in this order:

1. Source sections and a short navigation list.
2. Alphabet and the notation needed to read the formulas.
3. Healthiness and normal forms.
4. Correspondence mappings.
5. Operators and their laws, including sequential composition and prefix.
6. Non-divergence where applicable, then worked examples.
7. Supporting implementation facts and file map.

Most of this structure is already present. Use **Paper reference**, **Thesis reference**, **Premises**, **Statement**, and **Isabelle declaration** where a table benefits from separate columns. Keep entries compact and put long quantified formulas below their row. Include source page numbers so readers can open the relevant PDF passage. Keep the exact premises adjacent to the statement rather than relying on a distant paragraph.

### Lead with the closest mathematical statement

At [docs/AD.md:166][ref37], present thesis T.4.5.1 first through [angelic_rdesign_seq][ref38] using the source's pre/postcondition components. Keep the extracted `pre_D`/`post_D` calculation as secondary implementation detail. This removes the need to understand component extraction before comparing the theorem.

Explain representation changes only where they matter: typed records/lenses for D22/D101, general trace types versus source event sequences, and full observations versus healthy predicates. The current explanations are useful; avoid repeating them in every table. Move routine closure machinery and substitution helpers to the existing support sections, while leaving the main source result linked from its mathematical topic.

### Fill the small source-reference gaps

- [docs/RAD.md:171][ref39]: add thesis **L.5.3.1, p154** beside paper L6.
- [docs/RAD.md:292][ref40]: the sequential mapping is also thesis **T.G.7.11, p597**.
- [docs/AP.md:100][ref41]: add thesis **L.6.3.1, p184** beside paper L10.
- [docs/AP.md:222][ref42]: paper Ex22–25 correspond to thesis **Ex40–43**, on pp184, 184, 186 and 187.
- [docs/AD.md:113][ref43]: clarify that the two state-substitution links are representation support for D22/D101, rather than a standalone implementation of the source's whole general alphabet calculus.

### Reduce duplication without hiding important differences

Keep detailed explanations of A3, the initial-ok guard and printed corrections beside the corresponding theorem in the layer guide. The coverage index should summarise and link to them. The relevant [AD](../paper/AD.md) and [RAD](../paper/RAD.md) sections now retain the useful representation and composition distinctions from the retired semantic notes. Keep this audit as the maintenance record, separate from the reader's main route through the mathematics.

This cleanup uses the existing guides without adding a classification scheme. Parallel material remains outside this pass.

## Suggested order of work

1. Correct the wrong Example 13 correspondence, the T29 note, the misleading T.4.5.8 qualification and the erroneous citations. Make Example 14's partial evidence explicit.
2. Add the missing thesis references and short notes for stronger implementation statements.
3. Improve source-number lookup and stable guide anchors; then make table layout and reading order consistent across the existing guides.
4. Recheck every moved link and preserve every premise. Check that a reader can locate T6, T29, T35, T.4.5.8 and T63 from the source index in one step, then reach the corresponding Isabelle declaration in one more step.

The first three steps are proposed documentation work. Establishing full process-level Example 13/14 lemmas, if needed, is a separate proof task and should not be claimed complete by relabelling existing lemmas.

</details>

[ref1]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L328
[ref2]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_examples.thy#L622
[ref3]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_csp.thy#L187
[ref4]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L234
[ref5]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_ops.thy#L669
[ref6]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L182
[ref7]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/PAPER_COVERAGE.md#L44
[ref8]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/SEMANTIC_NOTES.md#L49
[ref9]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_healthy.thy#L1092
[ref10]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_healthy.thy#L1115
[ref11]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L178
[ref12]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_healthy.thy#L125
[ref13]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AP.md#L120
[ref14]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AP.md#L121
[ref15]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L329
[ref16]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_examples.thy#L636
[ref17]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L179
[ref18]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_healthy.thy#L1013
[ref19]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L297
[ref20]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L361
[ref21]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_seq.thy#L50
[ref22]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_seq.thy#L130
[ref23]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L125
[ref24]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L127
[ref25]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L131
[ref26]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_designs.thy#L357
[ref27]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_designs.thy#L427
[ref28]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_designs.thy#L456
[ref29]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L315
[ref30]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_nd.thy#L43
[ref31]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_nd.thy#L180
[ref32]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L98
[ref33]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L103
[ref34]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L107
[ref35]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_healthy.thy#L825
[ref36]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/reactive-angelic-designs/utp_rad_healthy.thy#L926
[ref37]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L166
[ref38]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/angelic-designs/utp_ades_healthy.thy#L488
[ref39]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L171
[ref40]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/RAD.md#L292
[ref41]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AP.md#L100
[ref42]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AP.md#L222
[ref43]: https://github.com/JunmingZhao42/UTP-Angelic-CSP/blob/e01d4309c857382e7990615c17f037153330bcaf/docs/AD.md#L113
