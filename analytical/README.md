# Analytic proof inventory

Final `PROOF.typ` files are self-contained hand proofs with three independent
hostile reviews, resolved objections, author self-audits and checked Lean
formalizations. Drafts and research notes retain their explicit grades.

| Grade | Result | Proof | Main Lean result |
| --- | --- | --- | --- |
| THEOREM | Submitted 722: ranks 357, k = 8, 17 ≤ d ≤ 20 | [Complete proof](rectangle722-submitted/PROOF.typ), [PDF](rectangle722-submitted/PROOF.pdf) | `Rectangle722Submitted.parameters_and_bounds`, `pauli_bounds` |
| THEOREM | Explicit rectangular 722: sector and mixed-Pauli lower bounds 17 | [Model proof](rectangle722-distance17/PROOF.typ) | `Rectangle722.pauli_lower_seventeen` |
| THEOREM | Explicit rectangular 722: commutation, ranks 357, k = 8, both sector and mixed-Pauli lower bounds 15 | [Complete combined proof](rectangle722-distance15/PROOF.typ) | `Rectangle722.pauli_lower_fifteen` |
| THEOREM | Complete boundary charges and earlier model bound 9 | [Boundary-charge proof](charge722/PROOF.typ) | `Rectangle722.pauli_lower` |
| THEOREM | Short-run exit accounting gives weight at least 17, and 18 without the directional endpoint exception | [Run proof](strip-runs/PROOF.typ) | `Planar.StripRunRecurrence.weight_ge_seventeen` |
| THEOREM | Local exact strip recurrences and adjacent nonemptiness imply coefficient weight≥15 | [Local strip proof](strip-deficits/PROOF.typ) | `Planar.StripRecurrence.weight_ge_fifteen` |
| THEOREM | Explicit rectangular model's ranks and quotient dimension | [Rank proof](planar722/PROOF.typ) | `Planar.Parameters722.parameters722` |
| THEOREM | Generic column criterion excludes logicals of weight at most two | [Column proof](small-support/PROOF.typ) | `Planar.SmallSupport.pauli_lower` |
| THEOREM | Nonzero lattice 281 divides 7u+145v has minimum L1 length 23 | [Lattice proof](lattice562/PROOF.typ) | `Lattice.Analytic562.norm_ge_23` |

The submitted result includes a checked fixed-input adapter for all 714 rows.
Earlier model bounds remain recorded as intermediate theorems. Exact distance
20 remains open. No new exact submitted-instance count is asserted.

Each result directory contains its reviewed draft and review record. Exact
source hashes, pinned dependency manifest, resource limits and verification
scopes are in [the dated evaluation](../data/analytical-evaluation/2026-11-11/).
[PROGRESS.md](../PROGRESS.md) is the continuing research registry, including
unproved hypotheses and counterexamples. Only final proofs have THEOREM grade.
