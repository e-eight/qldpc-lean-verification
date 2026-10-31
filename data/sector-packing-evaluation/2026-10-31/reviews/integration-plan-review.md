# Static review of the integration plan

## Scope and status

This reviews the draft integration runner and documentation plan before the handwritten literal proof is frozen. It is not final source acceptance. I did not inspect generated inputs or duplicate Turing's data review. No tests or Lean commands ran.

The initial runner SHA-256 is `253aa2dacf9f8067a2e297834e64c935550980acee9c3bb7d69c7daf14e2d7c9`. The dated plan README SHA-256 at that inspection is `ebca551e21017ddfb4ab451f6dee4b9d7d75b15e8a35db20265dc12658e3808a`. These identify the draft assessed below, rather than future frozen integration sources.

The plan correctly keeps the current overall lower bound at six. It distinguishes the seven numerical Z sectors from a literal Lean proof. The residual numerical bounds eleven through thirteen do not raise the proposed uniform Z bound beyond seven because the good directions remain at seven.

## Runner findings before freeze

1. The resource gate in `integration/replay.sh` uses Python `assert` statements. `PYTHONOPTIMIZE` can disable them. Replace these with explicit failures or reuse the approved prototype resource verifier. The final record must still capture the actual effective cgroup and CPU limits.
2. The root compile writes `QldpcVerification.olean` without rejecting retained artifact links. Prepare a fresh owned output path and make sure that neither the output nor its parent directory redirects into retained caches. The prototype and helper runners already reject linked outputs. This matters when staging imports through links.
3. The audit loop includes the generic prototype and future literal audit, but not `literal-z/helper/HelperAudit.lean`. Execute its thirteen guards and twelve controls in the integration scope, or explicitly carry them into an executed focused audit. If they remain standalone-only, record that narrower integration scope clearly.

The runner currently performs only its own source preflight. The final wrapper must also capture source postflight, as the approved standalone records do. The source and compiled-artifact identities must link the generated modules and handwritten capstone to this combined run. A root compilation with warm imports is not a recompilation of all new modules.

## Documentation gates

Keep README capabilities, CERTIFICATES mathematics, RECOMMENDATIONS priorities, and CHECKS_AND_RESULTS history in their assigned roles. After a successful literal replay, state `d_X >= 6` and `d_Z >= 7` separately. The overall result remains `6 <= d <= 20`, with nineteen exact submitted instances. Do not describe the eleven-to-thirteen residual numerical values as the unconditional Z bound.

Scope the RECOMMENDATIONS sentence that a complete packing certificate at twenty needs qualifying classes spanning all eighteen coordinates. That is a requirement of the basis-family method. The new sector-cover method can replace a deficient span with residual certificates, so it is not a universal necessity for packing certificates.

The thirty-two successful X samples leave 2,015 nonzero patterns unchecked. The disjointness shortcut's bounded failures prove no general obstruction. Preserve both qualifications when selecting the next experiment. Keep the original weighted export available for threshold seven and stronger experiments.

Final documentation must identify the current replay, audit counts, independent reviews, generation comparisons, and measured resource scopes. Preserve earlier records as historical snapshots. State which new modules compile freshly and which imports use warm objects. Keep operational details and raw logs private.

## Final acceptance still pending

At initial inspection, the package umbrella and main audit still lacked the new imports and targets. That was an expected integration task, not a defect in unfinished sources. Final review must cover their frozen changes, the handwritten literal proof and audit, the combined replay, and the documentation claims against actual results.

## Intermediate integration follow-up

The parent then added the generic imports and all twenty-five prototype plus thirteen helper guarded targets. I confirmed the current main audit has 517 textual entries and 338 distinct targets. It retains 179 historical repeated entries. The two counts measure different things. Literal targets remain pending.

The intermediate umbrella SHA-256 is `7073357eda9443b79d9d1ebb453335660da6e18c85b2224f291aa7f81e174c0a`. The main audit SHA-256 is `9a8792a225f32c9700078d4925694086fbbbc169f0c2205378f745167a90ced2`. This confirms source inclusion only, not a successful combined replay.

The new CERTIFICATES section matches the reviewed generic and helper mathematics. It retains complete coordinates, boundary orthogonality, strict thresholds, and exhaustive suffix coverage. It also keeps numerical and pilot results separate from the literal capstone. Its reviewed SHA-256 is `17a7c1edcb55fd42d9943b06690d1a927636908d665e1b27850aab9f4d59fa87`.

The integration runner remains at its initial reviewed hash. Adding the helper axiom targets to the main audit covers that part of finding 3. The twelve standalone finite helper controls still need an executed integration location or an explicit standalone-only scope statement. The remaining runner and documentation findings stay open for the final freeze.

## Static findings resolved

The revised runner at SHA-256 `f4420a29470306f3b95f06857bc3d276edea018c347ae188daa4fd2a0ad752ea` addresses all three source-level findings. It uses explicit resource failures, rejects a linked root output or any linked parent, and executes the standalone helper audit after fourteen project audits. It also checks source hashes after execution.

RECOMMENDATIONS at SHA-256 `288371adb05bdf1a908e5fd01d2da54efe99c7fb10e57dd1c1fff4a2f737cce8` scopes the spanning requirement to the basis-family method and states the sector alternative. These resolutions follow limited source inspection. Actual combined replay, final source identities, and literal-proof acceptance remain pending. No additional review cycle is required before the handwritten proof is ready.
