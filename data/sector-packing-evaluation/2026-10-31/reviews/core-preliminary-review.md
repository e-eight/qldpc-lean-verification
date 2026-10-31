# Preliminary review of the generic core

## Verdict and scope

No mathematical blockers in the current `SectorPacking.lean`. Its hypotheses match the initial design. This is source inspection, not a final proof or integration review. Examples, negative controls, and the guarded audit remain outside this verdict.

Current source identities, relative to the repository root:

| File | SHA-256 |
| --- | --- |
| `lean/QldpcVerification/SectorPacking.lean` | `5d41e0251e24ec404b009ca7cb4a9d57f4927a7fc761cc601364c435b379a253` |
| `lean/QldpcVerification/Coverage.lean` | `d552cf1c01c7c0adbccba7b40011d2e2ad9902a2080d1c309454a981bce0b626` |
| `lean/QldpcVerification/Overlap.lean` | `aca10d73d0dbac3a9a1af2dab6ab42057e09bf77c1a8e548f96cd3d66d0040ff` |

The retained core-v2 compile receipt records exit status zero and 183.305 seconds for source hash `e62b6a89443371ee4df55b570a8ae67302d37476162da82d6cca22f9f5b76384`. That hash differs from the current core. This review therefore does not attribute the v2 replay to the current bytes.

The receipt records `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`. Its resource record reports one CPU, an 8 GiB memory ceiling, zero swap, and process peak RSS of 2,104,452 KiB. I inspected those records but ran no compilation or tests. Final acceptance requires a successful replay and guarded audit for the frozen current hashes.

## Proof assessment

`pairing_eq_of_coordinates` requires both vectors to lie in the cycle subspace. It uses complete coordinates to put their difference in the boundary subspace. Explicit boundary annihilation then transfers each detector pairing. It assumes neither a physical coordinate map nor weight preservation.

`weight_ge_of_sector` transfers pairing one for every detector, then applies `weighted_overlap_bound`. The strict natural-number inequality retains the integer ceiling. The argument handles zero weights and zero cap without division. Allowing zero weights in this generic theorem is sound, although the numerical export requires positive selected weights.

`Certificate` includes cycle membership for the reference, its exact coordinates, boundary annihilation, pairing one, all physical qubit loads, and the strict threshold. `Certificate.lower_bound` compares the target vector with that reference in the correct direction. Different detector classes require no extra assumption once these fields hold.

`weight_ge_of_coordinate_cover` requires a cover of every nonzero coordinate vector. Its good-direction premise quantifies over every relevant physical vector, rather than only a reference. Its residual premise supplies a complete sector certificate. Neither branch treats a conditional result as a global bound.

The prefix/suffix lemmas distinguish a prefix hit from a nonzero suffix. `weight_ge_of_prefix_sectors` requires a complete paired basis and certificates for every nonzero suffix, including sums. `residual_pattern_count` gives `2^s - 1`, including the empty suffix case. These declarations do not establish that a numerical basis already has the desired good prefix.

The homological X and Z specializations use the correct opposite-cycle spaces to discharge boundary annihilation. They retain reference membership, complete coordinates, individual pairings, capacities, and thresholds. The source contains no `sorry`, added axiom, unsafe declaration, or `native_decide`. A source scan does not replace the pending dependency audit.

## Remaining gates

Final review must cover the frozen examples and guarded audit with current replay receipts. The missing-annihilation control must exhibit equal coordinates and different pairings, with the false weight-two conclusion excluded by the missing hypothesis.

Literal application must independently establish threshold-seven good families, basis ordering, complete pairings, original-row provenance, and all seven Z-sector certificates. This generic core alone changes no submitted-code bound. The existing overall bounds remain `6 <= d <= 20`.
