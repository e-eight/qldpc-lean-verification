# Independent hostile review of rectangular 722 model

Each reviewer saw only DRAFT.typ and no author reasoning, project source,
research notes, or other reviews. The theorem concerns an explicitly defined
finite model, not a JSON identity or a distance assertion.

## First review and resolutions

Volta (`01a1cb8f-9390-7852-8c20-d8361d709a70`) accepted the mathematics:
intersection retention proves commutation, two separate polynomial recurrences
prove independence, and finite linear algebra gives quotient dimension8.
Two presentation objections were sustained: “planar” could imply an unproved
graph embedding, and closing external matrix/witness statements were not
self-contained. The title now says “rectangular”; those external assertions
and research distance material were removed from DRAFT.typ and preserved
only in research notes/RESEARCH.typ. No pass was recorded before resolution.

## Final independent verdicts

- Volta reread the revised draft: “No surviving objections.” Checked the
  remaining construction, both ranks357, and quotient dimension8.
- Pauli (`01a1cb92-27dc-7670-9b11-7fb7715a3038`): no fatal flaw, hidden
  computation, unproved mathematical assumption, or invalid boundary recurrence.
  Explicitly checked negative X anchors, reflected Z ranges, nonunit polynomial
  cancellation, all induction endpoints, and quotient containment.
- Cicero (`01a1cb92-27f5-73d2-80a9-e2f4ed3456c7`): main result correct,
  with no mathematical gap. Independently reconstructed both symbolic recurrence
  arguments and dimensions. This referee additionally performed a finite matrix
  calculation from the document. That calculation is NOT a premise, proof step,
  or acceptance criterion here; only the supplied analytic reasoning is used.

All three verdicts apply to commutation, ranks and binary quotient dimension,
not distance. The final PROOF.typ retains the reviewed main argument with status
labels updated; the reviewed DRAFT.typ is retained unchanged.

## Formalization and author self-audit

Parameters722.parameters722 and its guarded audit passed after the explicit
matrix/synthesis correspondence was proved. Rectangle722 further instantiates
the project's QECLean-backed CSSCode with explicit physical and row permutations;
its two ranks, encoded dimension, and logical-space transport passed five guards.
The proof checks do not identify an external input file.

Reread the entire final mathematical argument as an adversary. Checked all six
support exponents; negative/positive anchor endpoints; no intersection removed
by truncation; no transverse coefficients discarded when deriving recurrences;
the two independent eliminants; cancellation only in polynomial domains;
reflection's exact ranges; every induction endpoint; nondegenerate ambient dot
product without assuming nondegenerate row-space restrictions; containment before
quotient dimension; and 722-357-357=8. No mathematical gap or external premise
remains. All final claims have THEOREM grade. This completes the rank/commutation
checkpoint, not a distance theorem or the wider research mission.
