# Independent hostile review of the local seventeen bound

> **Source format note (2026-11-11).** This record concerns the Typst sources
> (`*.typ`) as reviewed. They were later replaced by LaTeX translations with the
> same basenames (`*.tex`). The reviewed Typst files, and the line numbers and
> hashes quoted here, are in commit `fa8b57a2d87f41e04ba9b5f5c1ed62e3debf511a`.

Each reviewer saw only DRAFT.typ, without author context, other files,
computations or external sources, and was instructed to find a fatal flaw.

- Rawls (`01a1cbd3-bd8d-7100-be03-08f924c39239`): no substantive objection.
  Checked arbitrary heavy feeds, cheap-exit cases, exact run propagation,
  complete run partition, extra-unit disjointness, tails and endpoint discount.
- Sagan (`01a1cbd5-11a9-75f2-b272-4a787c104659`): no substantive objection.
  Explicitly checked that terminal weight at least three, rather than mere
  heaviness, supplies an unreserved unit even in a long short-gap run.
- Popper (`01a1cbd5-11bc-71d0-a2d6-0e45d8943530`): no substantive objection.
  Verified the two recurrence directions independently, coefficient cancellations,
  all long-gap baselines, and the sole missing target in each orientation.

All three accept E>=z-1-epsilon and W>=18-epsilon>=17, with18 when epsilon=0,
from the exact hypotheses stated in the document. No corrections were requested.
The new local polynomial lemmas, actual weighted-run accounting, and recurrence
adapter now pass Lean and guarded audits. The author reread the complete final PROOF.typ and inspected all six rendered
pages. Exact recurrence ranges, domain cancellation, missing endpoints,
reserved excess units and disjoint selection were checked. No objection survived.
