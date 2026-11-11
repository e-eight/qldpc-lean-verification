# Independent hostile reviews of the local weight-fifteen proposition

All reviewers saw only DRAFT.typ, with no author context, other documents,
source code, computation, or external sources. Each was asked to find a fatal flaw.

- Singer (`01a1cbaa-d9b1-7451-bbdb-cd0ebd23b7e1`): no fatal flaw. Checked
  polynomial run endpoints, singleton exclusivity, every local gap case,
  distinct forward/backward equations, exact exceptional endpoints, exhaustive
  gap categories and overlap-safe charging multiplicities.
- Jason (`01a1cbaa-d997-7513-a3d7-4161876e269c`): no fatal flaw. In particular
  verified that branch targets are injective, gap interiors are disjoint, and
  these TWO budgets need not be disjoint from each other; the coefficient six
  in the final estimate correctly permits overlap. Verified rounding 6W>=86.
- Hypatia (`01a1cbac-2d0f-78e1-935b-5d90068048c7`): no substantive objection.
  Checked every recurrence index stays in2..18, four-singleton proofs need only
  one empty endpoint, all monomial exponents counted are distinct, and all
  gaps fall into lengths2,3,4,5,or≥6.

The verdicts establish the internal implication from the two stated polynomial
recurrences and adjacent-slice nonemptiness to coefficient weight at least15.
They do NOT discharge an external code adapter or Lean formalization. All three
explicitly distinguished that scope. No mathematical corrections were requested.
The full local polynomial lemmas, actual global gap-count construction, and
recurrence adapter now pass Lean and their guarded audits. The final PROOF.typ
retains the reviewed argument, updates status labels, and expands elementary
polynomial-domain, support-union, divisibility, and rounding justifications.
No theorem statement is strengthened by those expansions.

## Final author self-audit

Reread from the two recurrence hypotheses through the final integer bound.
Verified every recurrence substitution, the forward/backward directions,
singleton exclusivity, coefficient cancellations, polynomial nonzero factors,
the two untested endpoint exceptions, all five exhaustive gap categories,
distinct targets, disjoint interiors, and permitted overlap between the two
budgets. Checked the total baseline counts occupied prefixes/suffixes and the
integer identity W=19-z+E. No hidden rank, code recognition, search, or external
weight premise occurs. All final statements are THEOREM-grade. Application to
the rectangular code is a separate bridge and is not claimed by this document.
