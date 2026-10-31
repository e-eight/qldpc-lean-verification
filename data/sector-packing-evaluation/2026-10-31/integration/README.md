# Integration of logical-sector packing

## Status

The generic prototype, numerical Z handoff, literature audit, and mixed-family helper have passed independent review.
The literal exporter and generated data have passed independent review after a successful seven-module pilot.
The literal Z capstone, focused audit, and combined replay have passed.
The completed sector bounds are `d_X >= 6` and `d_Z >= 7`, with overall bounds `6 <= d <= 20`.
The exact-distance inventory remains nineteen submitted instances.

## Replay contract

The new modules have compiled and the source manifest is frozen. Run this from the repository root inside a detached, bounded Slurm allocation:

```bash
bash data/sector-packing-evaluation/2026-10-31/integration/replay.sh
```

The runner requires an effective cgroup memory ceiling of at most 8 GiB, zero permitted swap, one CPU of affinity, and one Lean thread.
Its explicit resource failures also apply when Python optimization is enabled.
It rejects linked root artifact destinations and linked output parents.
Private staging must first prepare real owned output directories and retain imported artifacts without modifying their source caches.

The runner checks source hashes before and after execution, recompiles the package root, and executes fourteen project audit sources.
It also executes the standalone mixed-family helper audit, including all thirteen dependency guards and twelve finite controls.
Direct Lean calls use `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`.
The final wrapper must capture input identities, actual resource ceilings, fresh main-audit output, dependency configurations, terminal accounting, and source/artifact hashes.

This is a combined replay with warm imports, not a cold full-project build.
Separate records identify freshly compiled generated inputs and handwritten modules.
The main audit has 371 unique targets: the earlier three hundred, thirty-eight generic/helper targets, and thirty-three literal sector targets.
It retains 179 historical repeated axiom prints, giving 550 textual `#print axioms` commands and 371 guarded targets.
The 428-entry source manifest includes all active Lean sources, the exact 347 tested Python inputs, pins, the corrected generated manifest, and the public runner.
Mutable narratives and runtime summaries are excluded to avoid circular hashes.

## Evidence boundaries

All seven nonzero residual Z patterns now have closed kernel proofs, establishing the Z lower bound of seven.
The original fifteen good directions limit the uniform proposed Z bound to seven, despite stronger residual numerical values.
A Z improvement alone leaves the overall lower bound six because the X lower bound remains six.
The X pilot checks thirty-two of 2,047 patterns, leaving 2,015 unchecked.
The failed bounded disjointness diagnostic gives no infeasibility result.

## Completed execution

The exact runner passed root compilation and all fifteen audit sources in 414.43 seconds.
An additional fresh main-audit compilation passed in 21.12 seconds.
All 428 source hashes and 65 retained module identities matched before and after execution.
The current 347-entry Python snapshot, eleven dependency pins, 33 regular configuration files, and both literal input hashes also matched.

The allocation completed with exit `0:0` in 450 seconds, using one CPU, one thread, an effective 8 GiB memory ceiling, and zero permitted swap.
The runner's maximum process RSS was 2,036,092 KiB; the fresh main audit used 2,039,212 KiB.
Scheduler-sampled batch RSS was 4,522,900 KiB, with a different measurement scope.
The combined allocation exhausted neither its memory ceiling nor its twenty-minute wall limit.
The standalone record separately preserves earlier setup failures, profiling candidates, and the recovered residual timeout.

Earlier generated sources, proof records, archives, and dependency pins must retain their bytes.
Operational cluster details and raw logs remain under ignored `.local/` storage.
Final public summaries must state review scope, measurement scope, and which sources each successful run checked.
