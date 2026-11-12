# Three independent hostile mathematical reviews

> **Source format note (2026-11-11).** This record concerns the Typst sources
> (`*.typ`) as reviewed. They were later replaced by LaTeX translations with the
> same basenames (`*.tex`). The reviewed Typst files, and the line numbers and
> hashes quoted here, are in commit `fa8b57a2d87f41e04ba9b5f5c1ed62e3debf511a`.

All reviewers received only `DRAFT.typ`. They were started without conversation
history or author reasoning and were prohibited from reading other files,
computing, or browsing. They were explicitly asked to find a fatal flaw.
The reviewed freeze is identified by FREEZE.sha256.

- Poincare (`01a1cb9c-83e7-73a3-9b38-d46559f6aa2e`): no fatal flaw or
  mathematical objection requiring a change. Checked all boundary intersections,
  both independent rank recurrences, monic-division remainder determinant,
  exact kernel dimension289, quotient algebra without a field assumption,
  both power bases, the image/kernel equality in the same84-dimensional space,
  stabilizer cases, dual reflection, both flux endpoints, and physical Pauli weight.
- Meitner (`01a1cb9d-e801-7b12-a036-e3ceaa4e797b`): no substantive objection.
  Specifically attacked the distinction between polynomial-domain cancellation
  and units in a possibly nonfield charge algebra; both uses are valid. Verified
  that equal dimensions are combined with actual inclusion, and that surjectivity
  produces physical cycles rather than assuming a lifting theorem.
- Kepler (`01a1cb9f-0a59-7dd3-a669-ec4fe30efc2a`): no substantive objection.
  Verified the complete low-charge kernel equals the stabilizer space, reflected
  ranges, index20 being a syndrome rather than physical coordinate, integer
  rounding, both nonempty logical minima from quotient dimension8, and mixed
  Pauli support containment.

All three accept the analytic conclusion dX,dZ,dPauli>=9 for the explicitly
specified rectangular model. None claims distance20, a literal external-input
identification, or Lean verification. No corrections were required by these
reviews. The first referee additionally reread the final frozen DRAFT.typ and again
reported no surviving objection. The concrete charge-completeness, both physical
sector bounds, QECLean CSS transport, and mixed-Pauli capstone now pass Lean and
their guarded audits. Final PROOF.typ retains the reviewed mathematical argument,
updates status labels, omits research-only scope text, and expands elementary
polynomial/domain and dimension justifications. No result is strengthened.

## Final author adversarial self-audit

Reread the complete final source from the main theorem through the final mixed-
Pauli argument. Rechecked all six shifts, the two truncation directions, both
eliminants, ordinary-polynomial monic division, its nonzero determinant, support
extrema and kernel289, all quotient inverses without assuming irreducibility,
the two eight-element bases, the common ambient84-dimensional boundary spaces,
image inclusion before dimension equality, actual lifting from image equality,
all low/interior/high stabilizer cases, the reflected tested ranges, both cut
endpoints, physical union support, nonempty minima, and integer rounding.
No external premise, numerical rank, generated support search, or hidden case
list remains. Inspected every rendered page and compacted the layout to avoid
an orphan concluding paragraph. All final claims are THEOREM-grade.

This proves a lower bound9 for the explicit model; it does not prove distance20
or a literal external-input recognition. The broader mission continues.
