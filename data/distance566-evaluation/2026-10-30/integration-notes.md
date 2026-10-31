# Integration and documentation updates

This task adds standalone distance modules and a focused audit.
It leaves the shared Lean umbrella, main audit, dependency pins, and root documentation unchanged.
The parent owns the existing uncommitted edits to `RECOMMENDATIONS.md`.
No commit, push, upstream PR, or maintainer message occurs in this task.
An independent human or agent review of these additions remains necessary.

## Integration

Import `QldpcVerification.Distance566Pauli` from the package umbrella after review.
This import includes the coordinate, packing, and Pauli results.
Add `Distance566Audit.lean` to the full audit runner, or import its guards from the main audit.
The focused audit contains fourteen guarded dependency checks and two finite negative/positive controls.
Use the ordered replay list in this record for the new modules.

Review the conversion from sparse supports to packed masks, the row-combination soundness proof, and both sector orientations.
Also review the generator's literal input hashes, complete eighteen-coordinate coverage, and strict integer thresholds.
The independent sparse-set validator is a second numerical implementation, not an independent reviewer.

## Root documentation

Update `README.md` with the new partial result for the submitted 566 matrices.
State that complete logical coverage and the stored X upper witness are proved.
Keep the inventory at nineteen submitted exact-distance instances.
The new result does not establish distance twenty.

Append this dated record to `CHECKS_AND_RESULTS.md`.
Include the final theorem scope, guarded checks, Python results, source hashes, and measured resource limits.
Preserve older records and their original scopes.

Update the completion strategy in `RECOMMENDATIONS.md` with the measured search outcomes.
The seventy-two tested packing families give bounds of three or four.
No family reaches the strict threshold for twenty.
The information-set candidates provide lighter classes spanning all eighteen coordinates.
Use those candidates to improve detector selection and pricing before increasing exhaustive-search resources.
A failed restricted search supplies no impossibility theorem.
The Z correction stage still lacks its source lower-bound premise.

Add a short reference to the row-combination checker in `CERTIFICATES.md`.
Keep the existing packing mathematics and integer ceiling unchanged.
Avoid duplicating the full proof or this evaluation narrative.

## Lean documentation

Add the five new theory/audit modules and ten generated input modules to `lean/README.md`.
Link this evaluation record and its guarded replay.
State that the partial Pauli result uses QECLean's existing CSS bridge.
Keep operational cluster configuration and raw logs under ignored local storage.
