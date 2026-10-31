# Independent review of the literal Z proof

## Final verdict

Approved. No blocking mathematical, audit, provenance, or replay-record findings remain in the frozen literal Z proof. `Distance566SectorZ.lower_Z` proves the unconditional Z lower bound of seven for the literal submitted matrices. X remains at six, so the overall bound remains `6 <= d <= 20`. Exact distance remains open, with nineteen exact submitted instances unchanged.

This is independent source and execution-record review, not a second kernel replay. I ran no Lean commands or tests. Turing separately approved the numerical inputs and the corrected exporter/data interface. Shared root integration, its execution, and final documentation remain separate acceptance work.

## Final frozen identities

| File, relative to the repository root | SHA-256 |
| --- | --- |
| `lean/QldpcVerification/Distance566SectorZ.lean` | `33934ca185240456c985a6ba65eafd72be8ede8eba83b16ce967e581d56abd47` |
| `lean/QldpcVerification/Distance566SectorAudit.lean` | `8dda6918229b02fa808a47c5ddb8a19e5fca73df82d08613792447f793a1ae5d` |

Both current files match the frozen source snapshots. The 61-entry [source manifest](../literal-z/proof/source-sha256.txt) has SHA-256 `3251a66812b45a4d70aa17ccc538d9344aa950a4c9f821bafb381c8555e92eb7`. Every entry matches its current file.

The [source-to-artifact map](../literal-z/proof/source-artifact-map.json) has SHA-256 `3a3489e20f15df4eef5f96c3714c146859e9621d586eb7b48fee5cbf744c3c6e`. All 61 retained object hashes match it. Their fetched paths and parents contain no links. The corrected 59-module manifest has SHA-256 `ceb066e1948071dad4989871bc9f04df9706b0a5d54852e484dd0407fe7f08c4`.

## Final mathematical and audit assessment

The final proof retains the initial statements and hypotheses. Its changes make cycle-membership transport and code arguments explicit. `Classical.choose` selects a certificate from the proved exhaustive coverage statement. These proof-body changes neither weaken coverage nor add a source-distance assumption.

Reference Z cycles, own-base X-cycle checks, actual HX row-span differences, and base-support equalities supply the physical pairing argument. Opposite-cycle membership establishes annihilation of Z boundaries. The good families certify the actual first fifteen detector coordinates. All seven nonzero suffixes receive certificates, including sums. Capacities cover all positions zero through 565, and every family uses the strict natural threshold for seven.

All 33 distinct guarded targets match the accepted axiom probe after whitespace normalization, as the audit specifies. The seven controls retain the suffix ordering and zero-prefix shift. Four dependency-message expectations changed from the draft after the actual probe. Every final message permits only `propext`, `Classical.choice`, and `Quot.sound`, with smaller sets for range checks. No capstone depends on `sorryAx` or `native_decide`.

Range facts compile and pass their guards as separate provenance evidence. The mathematical soundness theorem over committed finite rows needs no artificial dependency on raw-syntax range facts.

## Final execution-record checks

I matched each accepted source hash and object hash to exactly one successful module receipt. Coverage is seven frozen pilot modules, 41 modules from completed chunks, eleven modules recovered from the timed-out residual chunk, and two handwritten modules. This accounts for 59 generated modules plus the proof and audit. Every matched compiler command includes `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`.

The eleven recovered modules have successful individual receipts and matching retained objects. The residual chunk's terminal timeout is preserved as a timeout. The remaining module has its own successful recovery receipt. The final identity check establishes current-source freshness rather than inferring it from an old checkpoint.

The handwritten proof receipt reports exit zero in 98.35 seconds with process peak RSS of 2,191,452 KiB. The independent axiom probe reports exit zero in 16.52 seconds. The guarded audit reports exit zero in 16.15 seconds. The terminal literal allocation completed in 144 seconds with exit code `0:0`.

Public proof and audit receipts match the retained raw-run receipts. The recorded resource envelope is one CPU/thread, an effective 8 GiB memory ceiling, and zero swap. Generated source checks pass before and after the final replay. The final receipts separately bind both handwritten source hashes and object hashes. These checks use warm pinned imports and do not constitute a cold project build.

All 621 earlier-file preservation entries still match. Both approved generic source manifests also match. No implementation edits or additional computation were needed for this review.

## Integration boundary

The literal proof can enter parent integration. Final root imports, main guard inclusion, combined execution, and documentation claims still require their separate frozen review. Textual audit entries and unique targets must remain distinct metrics.

The preliminary review below records the earlier draft and its then-pending gates. The final approval above supersedes its pending literal-proof status.

## Preliminary verdict and scope, historical snapshot

No mathematical blockers in the draft handwritten proof or audit. Final approval remains pending frozen current-source hashes, complete compilation, guarded audit results, and terminal replay receipts. Elaboration fixes can change these draft identities.

This pass covers `Distance566SectorZ.lean`, `Distance566SectorAudit.lean`, and the theorem contracts that connect them to the approved generic and finite helpers. It does not duplicate Turing's exporter or generated-data review. No Lean commands or tests ran locally.

Draft SHA-256 identities:

| File, relative to the repository root | SHA-256 |
| --- | --- |
| `lean/QldpcVerification/Distance566SectorZ.lean` | `cfb49b37486851d19d86735130434e3e4880f1d38fce2e2fe9b0711c5aee8055` |
| `lean/QldpcVerification/Distance566SectorAudit.lean` | `02911e19f126eeedeadda7139dad8d96a329d351da1a554dd5b58281f1c18823` |

## Physical orientation and reference coordinates

References are Z cycles: their explicit `kernelCheck hx` discharges the dual-boundary equation for the literal code. Each selected base is an X cycle through `kernelCheck hz`. The proof connects each base mask to the support used for its pairing check.

`reference_coordinates` uses the existing complete `Distance566Weighted.zCoverage`, with X detectors and their independently paired Z witnesses. It checks all eighteen reference pairings through the ordered old X-support list. The finite shift theorem identifies exactly fifteen zero prefix bits followed by the three-bit suffix. It makes no physical weight claim about that logical encoding.

The good-family contracts use the same first fifteen existing X detectors as `Fin.castAdd 3 a`. Their actual class witnesses and strict thresholds discharge the prefix bounds directly. The proof does not infer this ordering from the reported detector rank alone.

## Original rows, pairings, and physical weight

Good-family class membership uses the existing checked X row-mask table and the span of the actual literal HX rows. Mixed-family membership uses each entry's own base through `entryAt`, with that same checked table. It establishes actual boundary-span membership, rather than only a zero syndrome.

`reference_pairs_one` first proves pairing with the selected base support, then rewrites it to the physical base vector. The reference's explicit Z-cycle proof annihilates the X boundary difference. This supplies the required pairing with each mixed representative.

Mixed representatives are X cycles because their own bases are X cycles and their differences lie in X boundaries. Consequently, they annihilate Z boundaries. Both pairing transfer and sector-boundary annihilation therefore have the required physical hypotheses.

The capacity contracts are `capCheck 566`, and `cap_of_check` quantifies over `Fin 566`. This covers every physical position from zero through 565. The sum conversion preserves natural weights, and each good and residual threshold is strictly `6 * cap < totalWeight`.

## Exhaustive assembly and audit

`residualTail` encodes patterns one through seven. Its finite kernel proofs establish nonzero tails and exhaust every nonzero element of `Fin 3 → ZMod 2`, including sums. `residualCertificate` includes the reference cycle, exact coordinates, transferred pairings, boundary annihilation, physical capacity, and strict threshold.

`lower_Z_cycle` applies the approved prefix/suffix theorem to all nontrivial Z cycles. A good-prefix hit gives seven. Every remaining nonzero suffix gets its own certificate. `lower_Z` converts the literal code's Z-logical predicate through the existing logical equivalence. No source-distance assumption remains in its statement.

The draft audit has 33 distinct guarded targets and seven finite controls. It includes all handwritten theorem endpoints, the certificate, the finite pattern checks, and the generated interface gates. It also includes physical support/mask ranges and the good/mixed raw-index gates. The separate helper audit remains in the combined runner. Draft dependency-message expectations still need actual execution before acceptance.

The proof source contains no `sorry`, added axiom, unsafe declaration, or `native_decide`. Its small enumerations use `decide +kernel`. This source inspection does not replace the pending transitive dependency audit.

## Remaining final gates, historical snapshot

Freeze the handwritten sources after elaboration fixes. Link them to a successful full generated-module replay and literal audit with source checks before and after execution. Retain the approved prototype/helper identities and the independent exporter/data review.

The literal data gates must compile and pass their audit for every physical mask, original-row index, and selected base index. These separate facts establish the connection to the intended raw inputs. The soundness theorem about committed vectors and finite matrix rows does not need an artificial dependency on raw-syntax range facts. Finite types suffice for that mathematical theorem, while the separately checked range facts establish that decoding preserves the intended raw indices. The current gate contracts supply those provenance obligations.

Review the frozen umbrella, main audit, final documentation, and combined replay separately. Distinguish textual audit entries from unique targets. A completed Z lower bound of seven will leave X at six and the overall result at `6 <= d <= 20`, with nineteen exact submitted instances.
