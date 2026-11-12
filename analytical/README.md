# Analytic proof inventory

Final `PROOF.tex` files are self-contained hand proofs with three independent
hostile reviews, resolved objections, author self-audits and checked Lean
formalizations. Drafts and research notes retain their explicit grades.

| Grade | Result | Proof | Main Lean result |
| --- | --- | --- | --- |
| THEOREM | Analytic lattice minima for all 16 submitted bicycle applications and both even regressions | [Instance lattice proof](family-integration/PROOF.tex) | `Lattice.BasisSeparation.BasisData.bound` and each instance's `shortest_relation` |
| THEOREM | Every positive cyclic binomial code: ranks, dimension, exact shortest-relation distances; coprime rotated-square families | [Cyclic family proof](cyclic-distance/PROOF.tex) | `Bicycle.Connected.Match.parameters_all`, `Bicycle.GaussianFamily.parameters` |
| THEOREM | Every open rectangle: eight logical qubits and sector bounds M−2, N−2, including mixed Paulis | [Rectangle family proof](rectangle-family-distance/PROOF.tex) | `Planar.RectangleFamily.parameters_and_bounds`, `pauli_lower` |
| THEOREM | Uniform repetition preserves k and dX and multiplies dZ by the replication factor | [Repetition proof](qubit-replication/PROOF.tex) | `QubitReplication.exact_distances`, `ranks` |
| THEOREM | Polynomial strips of every length L≥3 have weight at least L−2, or L−1 without the endpoint exception | [Uniform strip proof](strip-family/PROOF.tex) | `Planar.StripFamilyRunRecurrence.weight_ge_length_sub_two` |
| THEOREM | Arbitrary rectangle ranks, including sides of length two | [Independent rank proof](rectangle-family/PROOF.tex) | `Planar.RectangleFamily.parameters` |
| THEOREM | Submitted 722: ranks 357, k = 8, 17 ≤ d ≤ 20 | [Complete proof](rectangle722-submitted/PROOF.tex), [PDF](rectangle722-submitted/PROOF.pdf) | `Rectangle722Submitted.parameters_and_bounds`, `pauli_bounds` |
| THEOREM | Explicit rectangular 722: sector and mixed-Pauli lower bounds 17 | [Model proof](rectangle722-distance17/PROOF.tex) | `Rectangle722.pauli_lower_seventeen` |
| THEOREM | Explicit rectangular 722: commutation, ranks 357, k = 8, both sector and mixed-Pauli lower bounds 15 | [Complete combined proof](rectangle722-distance15/PROOF.tex) | `Rectangle722.pauli_lower_fifteen` |
| THEOREM | Complete boundary charges and earlier model bound 9 | [Boundary-charge proof](charge722/PROOF.tex) | `Rectangle722.pauli_lower` |
| THEOREM | Short-run exit accounting gives weight at least 17, and 18 without the directional endpoint exception | [Run proof](strip-runs/PROOF.tex) | `Planar.StripRunRecurrence.weight_ge_seventeen` |
| THEOREM | Local exact strip recurrences and adjacent nonemptiness imply coefficient weight≥15 | [Local strip proof](strip-deficits/PROOF.tex) | `Planar.StripRecurrence.weight_ge_fifteen` |
| THEOREM | Explicit rectangular model's ranks and quotient dimension | [Rank proof](planar722/PROOF.tex) | `Planar.Parameters722.parameters722` |
| THEOREM | Generic column criterion excludes logicals of weight at most two | [Column proof](small-support/PROOF.tex) | `Planar.SmallSupport.pauli_lower` |
| THEOREM | Nonzero lattice 281 divides 7u+145v has minimum L1 length 23 | [Lattice proof](lattice562/PROOF.tex) | `Lattice.Analytic562.norm_ge_23` |

The submitted result includes a checked fixed-input adapter for all 714 rows.
Earlier model bounds remain recorded as intermediate theorems. Exact distance
20 remains open. No new exact submitted-instance count is asserted.

Final proofs are LaTeX (`PROOF.tex`); the earlier instance drafts are LaTeX too
(`DRAFT.tex`, and so on), while the family drafts and research notes remain
Markdown. The LaTeX sources use only
standard AMS packages, `mathtools` and `hyperref` with the default `article`
layout; every display equation is numbered, and every cross-reference is a
label. Start new documents from [`TEMPLATE.tex`](TEMPLATE.tex), whose header
comments state these rules. Build a PDF with `latexmk -pdf PROOF.tex` in the result directory. The generated `INPUT.tex` and
`WITNESS.tex` appendices are emitted and byte-checked by
`scripts/gen_rectangle722.py` and `scripts/check_rectangle722_witness.py`.

For the earlier instance results, referees reviewed Typst sources (`*.typ`), which were replaced
on 2026-11-11 by LaTeX translations with the same mathematical content. Those
reviewed Typst sources remain available in commit
`fa8b57a2d87f41e04ba9b5f5c1ed62e3debf511a`. Historical review records, notes and
hash manifests that name a `.typ` file refer to that commit; the dated evaluation
records both the Typst hashes and the current LaTeX hashes.

The four family proofs written in Markdown (`cyclic-distance`, `family-integration`,
`qubit-replication` and `rectangle-family`) were replaced on 2026-11-12 by `PROOF.tex`
translations with the same mathematical content; their reviewed drafts remain Markdown.
The final `PROOF.md` sources remain in commit
`cee205f5615f9404e1b27eafd7513604663abe95`. On the same date the
`rectangle-family-distance` LaTeX sources were brought to the standard above
(numbered displays, theorem environments and labelled references) without
mathematical change. The family dated records list the new hashes and keep the
replaced ones under `document_revisions`.

Each result directory contains its reviewed draft and review record. Exact
source hashes, pinned dependency manifest, resource limits and verification
scopes are in [the dated evaluation](../data/analytical-evaluation/2026-11-11/).
The new family proofs have a separate [verification record](../data/family-theory-evaluation/2026-11-12/).
Their use in the existing instance capstones has a later [integration record](../data/family-integration-evaluation/2026-11-12/), including proof-body dependency checks.
[PROGRESS.md](../PROGRESS.md) is the continuing research registry, including
unproved hypotheses and counterexamples. Only final proofs have THEOREM grade.
