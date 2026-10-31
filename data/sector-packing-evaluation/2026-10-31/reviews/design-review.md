# Independent design review

## Verdict and scope

No conceptual blockers in the design dated 2026-10-31. The proposed sector argument follows from complete logical coordinates and weighted overlap counting. It does not yet strengthen a literal-code bound.

This review covers the plan, the prototype contract, and the existing `Coverage.lean` and `Overlap.lean` interfaces. It does not review unfinished implementations. No Python tests, numerical searches, or Lean compilation ran for this review.

The baseline is `e9e33f21946bc781e6ae3c3c04adaac86abb36dd`. Reviewed SHA-256 identities:

| File | SHA-256 |
| --- | --- |
| `../README.md` | `3270451fbec2b8d2bafa104ed3b243e0a2e25b296f872f18ed5640466546f33f` |
| `../lean-prototype/README.md` | `8e9fb6a7f06e8f05881fc1c038c4e9837aded7f93426806a99272e2c82b46b2a` |
| `lean/QldpcVerification/Coverage.lean` | `d552cf1c01c7c0adbccba7b40011d2e2ad9902a2080d1c309454a981bce0b626` |
| `lean/QldpcVerification/Overlap.lean` | `aca10d73d0dbac3a9a1af2dab6ab42057e09bf77c1a8e548f96cd3d66d0040ff` |

The Lean paths in this table are relative to the repository root. The README paths are relative to this review directory.

## Mathematical assessment

`CoverageCertificate.difference_mem_iff` identifies equal logical coordinates with a difference in the boundary subspace. It requires both physical vectors to belong to the cycle subspace. Any detector annihilating that boundary subspace then pairs equally with both vectors. The existing overlap theorem requires pairing one for each selected detector, so it permits different detector classes within one sector certificate.

Fifteen independent good detector classes in an eighteen-dimensional logical space leave a three-dimensional annihilator. Its seven nonzero elements are logical sectors. Each sector contains physical representatives differing by boundaries. A single reference vector labels a sector but supplies no weight bound by itself.

The stabilizer-extension interpretation is valid for the remaining Z problem if the added X checks commute and are independent modulo the old X checks. It changes the stabilizer code on the same physical qubits. Adding commuting stabilizers preserves the existing global lower bound of six. It implies no physical Hamming isometry and does not by itself establish the desired stronger bound of seven. The residual Z bound of seven still requires new certificates.

## Finite hypotheses required before continuation

1. Bind every artifact to the pinned literal 566-qubit matrices and the full, original threshold-seven families. The compact bound-six export supplies no threshold-seven premise.
2. Establish complete eighteen-dimensional coordinates in each orientation. Make sure that witnesses are cycles, detectors annihilate boundaries, and the full pairing matrix is the identity. Preserve each orientation's independently paired witnesses.
3. Recompute the strict threshold for every qualifying good family and its rank in logical coordinates. A physical rank computation alone does not establish independence modulo stabilizers.
4. State the map between canonical coordinates and the selected weighted basis. Make sure that its inverse, ordering, and physical pairings agree. The fifteen good directions form a prefix only after that ordering receives evidence.
5. Enumerate all seven nonzero residual Z patterns, including sums. Give each physical reference a cycle-membership check and direct pairings in both coordinate systems. For every residual pattern, make sure that each selected detector pairs to one with its reference and annihilates boundaries.
6. Retain original-row witnesses and exact index checks when pooling or deduplicating representatives. Independently recompute every selected physical support from its base and row witness. Pool indices must identify the same supports throughout the certificate.
7. Recompute all 566 weighted loads with natural-number arithmetic. Require positive integer weights and `6 * cap < totalWeight`. Reject Boolean weights, fractional values, threshold equality, missing sectors, and invalid indices. Floating-point solver results and restricted-pool duals are search diagnostics.
8. Assemble the good-direction bounds with every residual-sector bound. A conditional sector theorem cannot strengthen the global distance alone. A Z-only improvement leaves the overall certified lower bound at six.

The independent validator must derive these checks from literal data rather than trust producer summaries. Negative controls must include a coordinate-basis permutation, an omitted sum sector, and missing boundary annihilation. The planned two-qubit example distinguishes a sector improvement from a global one.

## Continuation gates

Freeze the numerical sources, certificates, and validator records before their final review. Freeze the generic Lean sources and focused audit separately. Final reviews must distinguish source inspection from actual kernel replay and identify the exact current hashes.

Proceed to literal Z formalization only after all seven certificates pass independent review and the generic adapter passes its audit. Measure the X pilot before expanding to all 2,047 residual patterns. Failure on the stored representative pool proves no general packing obstruction.

The literature audit must compare exact hypotheses before making a novelty claim. This design review makes no literature or novelty finding.
