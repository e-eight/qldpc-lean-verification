# Independent review of the integration runtime records

## Verdict and scope

Approved. No blocking runtime-record or source-identity findings remain for the combined integration replay. The accepted result is `d_X >= 6`, `d_Z >= 7`, and overall `6 <= d <= 20` for the literal 566-qubit code. Exact distance twenty remains open.

This is independent inspection of published records, retained receipts, sources, and fetched objects. It is not a second Lean replay. I ran no Lean commands, tests, numerical searches, or generation. The run uses warm project and pinned dependency imports, rather than a cold full-project build.

The final worker artifact inventory was still being assembled when this review began. This report binds the factual files below directly. It does not edit those files or approve future changes to them.

## Reviewed factual identities

All filenames in this table are relative to `../integration/`.

| File | SHA-256 |
| --- | --- |
| `integration-validation.json` | `421c47b7faebd2864b0a3bbf666d1fadf1e2f56ec1bf1d61a03e5bd09b1e615c` |
| `job-results.json` | `c66999a42d4865e45de750a4f73482a1643cc5cce9f4108818fd77b8e494b84a` |
| `commands.json` | `03f5e1336e980b74d00467648d7cf80a902254500314fa2a3dca66879a3be17b` |
| `resources.json` | `c4869229c1c0cc6a47bba4e4655925c1018f9bf5529096b8267157a6c7dae3d4` |
| `dependency-configurations.json` | `2df32ea764abfab3a48a81a5ea9128f452988dd4e66fc358e94fbdd615e7448c` |
| `imported-artifact-association.json` | `986888a870d20ef4098974978add39a3ed9078e137d6e524ec66b543953bb35b` |
| `fresh-artifacts.json` | `3d422bc1e987aff6634723c30790fd4dc3fb06895f6088450866009767891f3a` |
| `results.log` | `9cad7fa34bea58723f5e9f80c9db0dab4d5368b7fa591444d6c4a036d97d8e1f` |

The frozen 428-entry source manifest remains `0f6bc39cd6f06b3499dd0164a406dcc0076f596fd7a9c4439266c32bb0fb73e5`. The actual runner remains `f4420a29470306f3b95f06857bc3d276edea018c347ae188daa4fd2a0ad752ea`, matching the approved static review and its execution receipt.

## Execution and audit coverage

All thirteen timed receipt files match the retained raw-run receipts and the corresponding entries in `commands.json`. Every receipt reports exit status zero. The exact runner reports 414.428 seconds and maximum process RSS of 2,036,092 KiB. The additional fresh main audit reports 21.123 seconds and 2,039,212 KiB.

The raw exact-run log contains all fifteen audit labels in the expected order. Fourteen are project audits, and the last is the standalone helper audit. The runner uses `set -e`, checks the sources afterward, and reports exit zero. This supports completion of each audit command, rather than merely its printed start marker.

For each audit, I recomputed source identity and textual metrics from the current source. The main audit has 371 `#guard_msgs` targets and 550 `#print axioms` commands. Its 371 distinct printed targets equal the set of guarded targets. The 179 additional historical prints are not additional guards. The literal, generic prototype, and helper controls execute in their respective audit files.

The fresh-output preflight confirms empty root and main-audit artifact prefixes before execution. Both fetched fresh objects match their public hashes, sizes, and current source identities. Their fetched files and parents are regular, unlinked paths. The main object matches its explicit successful `-o` compiler receipt.

## Sources, retained imports, and pinned configurations

The raw source preflight and postflight each contain 428 successful comparisons. The exact runner contains another 856 successful lines from its internal before/after checks. Every current repository entry also matches the frozen manifest.

The separate Python-v3 preflight matches all 347 entries of its tested snapshot. No Python tests or generation reran in this integration allocation. Prototype and helper source checks each pass all ten entries before and after execution.

The retained import-state records are identical before and after the run. Their 61 literal source/primary-object identities match the accepted literal map. Their four generic identities match the approved prototype and helper objects. The public association record agrees with these retained records. This establishes association with the previously reviewed compilations, not fresh compilation of all 65 modules.

All eleven package revisions and origins match the pinned Lake manifest and the retained state records. The 33 distinct regular configuration records give three files per package. Their hashes remain identical across the run and agree with the public configuration record. I inspected the checker that compares the private package state and configuration hashes against its pinned metadata. Both literal input JSON hashes also match the retained before/after records.

These checks concern the recorded warm import state and primary `.olean` identities. They do not claim a cold dependency rebuild or independent recompilation of imported modules.

## Resources and terminal state

Public and retained resource records agree on an effective 8 GiB memory ceiling, zero swap, one CPU of affinity, and one Lean thread. Compiler commands retain `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`. Explicit resource failures remain active independently of Python assertion optimization.

The scheduler accounting agrees with `COMPLETED`, exit `0:0`, and 450 seconds for the single allocation. Its sampled batch RSS is 4,522,900 KiB. That measurement has a different scope from the two command RSS maxima above. The allocation finishes within its twenty-minute limit, and the worker records no remaining allocation.

## Acceptance boundary

The combined runtime gate is closed. The accepted literal proof, generic helpers, exact source snapshot, and root audit now have a consistent execution chain. This adds no exact submitted instance and does not raise the overall lower bound above six.

Final narrative and artifact-inventory assembly must preserve these factual identities and the distinction between sector bounds, overall distance, audit guards, and raw print counts. This runtime review does not replace the separate final documentation review.
