# Independent hostile review

> **Source format note (2026-11-11).** This record concerns the Typst sources
> (`*.typ`) as reviewed. They were later replaced by LaTeX translations with the
> same basenames (`*.tex`). The reviewed Typst files, and the line numbers and
> hashes quoted here, are in commit `fa8b57a2d87f41e04ba9b5f5c1ed62e3debf511a`.

The reviewers saw only DRAFT.typ, without the author reasoning, project sources,
or other reviewers' reports. They were instructed to seek fatal mathematical
flaws, omitted cases, phase errors, and degenerate-space overclaims. All three
reviews used hand-checkable reasoning and no computational checks.

- Pauli (`01a1cb92-27dc-7670-9b11-7fb7715a3038`): accepted the criterion and
  all conditional CSS/Pauli consequences. Explicitly checked infinite check
  index sets, empty coordinate sets, zero/dependent check rows, the sector
  reversal, absence of a phase-only logical loophole, and union-support weight.
  Noted correctly that the criterion is sufficient, not necessary.
- Cicero (`01a1cb92-27f5-73d2-80a9-e2f4ed3456c7`): no fatal flaw, omitted
  case, or phase error. Checked phase-one stabilizer generators cannot generate
  minus identity, and that empty logical spaces yield only vacuous universal
  bounds. Noted that the original title's numerical-distance wording needed
  the body's nonempty-minimum convention.
- Volta (`01a1cb8f-9390-7852-8c20-d8361d709a70`): no surviving mathematical
  objections. Independently checked all three cardinality cases, CSS inclusion,
  stabilizer pair product space, Pauli support overlap, and empty cases.

All three stressed that the draft's 722 adapter was conditional and that their
mathematical verdicts did not verify the reported Lean run.

## Resolutions and final scope

No mathematical correction was requested. The final title states exclusion of
logicals of weight at most two, avoiding an empty-minimum reading. PROOF.typ
retains the reviewed proofs of the abstract criterion, sector corollaries and
mixed-Pauli corollary. It omits the conditional 722 application interface and
external formalization-report section entirely; they remain in the reviewed
draft and are not needed by any retained proof. Status/proposition labels were
changed after successful review and Lean replay. No 722-specific claim is made.

## Author self-audit

Reread the entire retained proof. Checked cardinalities 0/1/2 exhaust weight≤2;
nonzero F2 values equal one; every column equality is an equality of functions;
B need not be contained in the cycle space for the abstract implication;
CSS sector/stabilizer pairing is reversed correctly; subspace membership of
zero handles the empty support; no logical-existence assumption is inferred;
phase-only operators and scalar stabilizers are excluded; XZ is nonidentity;
and overlap of X/Z supports never cancels physical weight. The criterion is
never claimed necessary. All final claims have THEOREM grade.

The Lean module and guarded audit passed in the detached, capped small-v2 run.
The first run failed at an invalid Mathlib import before proof checking; replacing
it with the pinned project's standard Mathlib.Tactic import resolved that failure.
