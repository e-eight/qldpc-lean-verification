# Analytic proof inventory

Final `PROOF.tex` files are self-contained hand proofs with three independent
hostile reviews, resolved objections, author self-audits and checked Lean
formalizations. Drafts and research notes retain their explicit grades.

| Grade | Result | Proof | Main Lean result |
| --- | --- | --- | --- |
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

All documents are LaTeX (`PROOF.tex`, `DRAFT.tex`, and so on). They use only
standard AMS packages, `mathtools` and `hyperref` with the default `article`
layout; every display equation is numbered, and every cross-reference is a
label. Build a PDF with `latexmk -pdf PROOF.tex` in the result directory. The generated `INPUT.tex` and
`WITNESS.tex` appendices are emitted and byte-checked by
`scripts/gen_rectangle722.py` and `scripts/check_rectangle722_witness.py`.

The referees reviewed the earlier Typst sources (`*.typ`), which were replaced
on 2026-11-11 by LaTeX translations with the same mathematical content. Those
reviewed Typst sources remain available in commit
`fa8b57a2d87f41e04ba9b5f5c1ed62e3debf511a`. Historical review records, notes and
hash manifests that name a `.typ` file refer to that commit; the dated evaluation
records both the Typst hashes and the current LaTeX hashes.

Each result directory contains its reviewed draft and review record. Exact
source hashes, pinned dependency manifest, resource limits and verification
scopes are in [the dated evaluation](../data/analytical-evaluation/2026-11-11/).
[PROGRESS.md](../PROGRESS.md) is the continuing research registry, including
unproved hypotheses and counterexamples. Only final proofs have THEOREM grade.
