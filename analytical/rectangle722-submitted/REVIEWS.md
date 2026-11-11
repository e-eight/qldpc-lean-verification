# Independent hostile review of the complete pinned-instance proof

Each reviewer received only DRAFT.typ, including the full analytic proof,
714 numerical input rows, and complete witness multiplication tables. No
outside JSON, source code, author reasoning, or other review was available.
Fixed integer/polynomial diagnostics were allowed because the document prints
all inputs, operations and results; candidate-error/logical searches were forbidden.

- Descartes (`01a1cc04-18f9-7683-9146-c44dd2de9145`): no substantive objection.
  Checked all714 ordered rows/anchors/clipping cases and all129 witness product
  terms. Verified exact cancellation multisets, weights23/20 and intersection65.
- Maxwell (`01a1cc04-18eb-7d01-8c06-d07c4abe62ef`): no substantive objection.
  Independently checked the same fixed arithmetic, five-case counts
  17,17,289,17,17 in each sector, all residual anchors and final transport.
- Archimedes (`01a1cc04-190a-73e1-b7ec-a80008da6940`): no substantive objection.
  Checked all714 rows and all43 monomial inputs/129 products, pairing and every
  physical/model transition. No omitted or duplicated row or support was found.

All three also attacked the full charge-completeness, run-exit and disjoint
accounting argument, the two physical recurrences, and Pauli support containment.
They accept ranks357,k8,sector lower17 and Z/Pauli upper20 for the printed matrices.
No objection survived. External JSON provenance was excluded from their reading;
separate pinned-source/regeneration tests establish that practical correspondence.

Their arithmetic-only check scripts are retained as referee_1_check.py,
referee_2_check.py and referee_3_check.py. Only naming, import ordering, formatting,
and an ambiguous loop-variable name were cleaned up; all diagnostics reran and pass.
They verify supplied identities, not searched supports or numerical certificates.

## Final author audit

Root reread the entire final source from the main theorem through all proof
steps, witness tables and all714 input rows. Rechecked the two polynomial
recurrences, ordinary-domain cancellations versus quotient units, all charge
kernel dimensions and actual image inclusions, both reflection/index conventions,
every endpoint exception, disjoint surplus allocation, physical support counting,
all five derived row cases in each sector, and both exact witness products.
The independent arithmetic scripts were rerun after style cleanup. An ambiguous
copied sentence about a 'bound twenty' was removed; it changed no result or data.
The JSON distance label is never a premise. No numerical rank or error search
is load-bearing. The capstones and all focused guarded audits pass.

The final 30-page PDF was rendered and inspected page by page. Witness and
input table columns are legible; the only changes after review were grade/title
labels, the sentence deletion described above, and page/table layout. No
mathematical statement, numerical input, or proof argument changed.

## Restructured edition: contribution-first presentation (2026-11-11)

The final manuscript is now33 pages. Main Sections1–7 occupy pages1–8 and
contain the code statement, qualified contribution discussion, full local
run-exit proof, and elementary derivation/application of both recurrences.
AppendixA contains elementary proofs of established algebra and ranks;
AppendixB contains complete boundary charges and cut transport; AppendixC
identifies the fixed input; AppendixD verifies upper witnesses; AppendixE
prints all714 input rows. Six primary references are in references.bib.
The original DRAFT.typ and the earlier reviews above remain historical records.

Three NEW independent hostile referees received only PROOF.typ and
references.bib, with no author notes, previous reviews, Lean sources, or
external evidence:

- Newton (`01a1cce1-ec54-72e1-b1d5-e43b6274dcff`): no surviving objection.
  Checked both cheap-exit cases, disjoint allocation, all appendix dependencies,
  all714 input rows, full witness arithmetic and internal references.
- Planck (`01a1cce1-ec66-7f42-aa55-e416853ea3f2`): no surviving objection.
  Checked recurrence ranges, parity/cancellation, missing and existing endpoint
  targets, dimension arguments, fixed arithmetic and qualified novelty wording.
- Carver (`01a1cce1-ec3e-79a0-86cd-423f903c0214`): no surviving objection.
  Checked the weight-three threshold, noncircular charge dependencies,
  sector/Pauli transport, all tables and the reference destinations.

All three separately confirmed that no error search was used. External
bibliographic attribution and Lean verification were not independently
replayed by these document-only referees; neither is a premise of the proof.
Attribution rests on the preceding primary-source literature audit.

Author verification: all six table blocks, all seven local lemmas with proofs,
and the complete disjoint allocation proof were compared byte-for-byte with
the previously reviewed edition and are identical. The theorem renumbering,
appendix ordering, dependency guide and both physical derivations were checked
for missing definitions and circular references. The domain argument was
expanded locally and the reflection map explicitly defined where first used.
All numerical data and mathematical conclusions are unchanged.

Final layout verification covered every page: pages1–18 and33 were visually
inspected (unchanged main pages also compared across rendering iterations);
the changed table-opening pages19 and26 were inspected; the bodies of the
other12 input-table pages were pixel-identical to the previously inspected
PDF at the same rendering resolution, excluding the page-number footer.
Post-review edits only adjusted page breaks, one displayed-equation line break,
monospace capstone formatting and bibliography presentation/year visibility.
No mathematical argument or citation target changed in those final edits.
No new Lean run was needed because no Lean source changed.

## Math rendering and live references (2026-11-11)

AppendixD's formerly plain-text polynomial expressions, bars, superscripts,
coefficient notation, witness coordinates and residuals now use Typst math.
Added spacing after H_X/H_Z prevents row indices from being absorbed into
subscripts; indexed polynomial function arguments elsewhere were corrected
for the same parser issue. The mathematical values and arguments are unchanged.

All internal theorem, lemma, appendix and numbered-section references now use
labels. Statement headings use native referenceable figure counters with
Theorem/Lemma supplements; appendix prefixes are taken from the target's
heading counter. External paper locators inside bibliography citations remain
literal, since they refer to numbering in those papers.

Validation: Typst compilation passes; all18 theorem/lemma labels have the
expected generated numbers. An unpublished insertion probe shifts main theorem
numbers and appendix prefixes automatically, confirming that forward references
are not tied to hardcoded numbers. Source scanning finds no hardcoded internal
numbered references. All6 tables and witness-coordinate tuple multiplicities
match the prior version after stripping math delimiters. AppendixD pages16–18,
the contribution/reference page and the physical derivation were visually
inspected. The output remains33 pages.

Independent editorial reviewer Ptolemy
(`01a1ccf6-c6c7-7211-b37e-db2f9a634f17`) found two remaining formatting issues
(indexed arguments and plain coordinate lists); both were fixed and rereviewed.
Final verdict: no objection within the editorial scope, mathematical content
preserved, labels coherent. This is an editorial verification, not a new
three-referee mathematical review. No Lean source changed or Lean run occurred.
