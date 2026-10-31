# Integration of the weighted 566-qubit distance bound

## Status and scope

The standalone additive proof, focused audit, and combined package replay passed,
establishing `6 <= d <= 20` for the literal submitted matrices.
This directory records package integration separately from the standalone
[proof evaluation](../README.md) and the immutable numerical
[exploration](../../../distance566-packing/2026-10-30-weighted/).

The package umbrella imports `Distance566WeightedPauli`. The main audit includes
all thirty focused weighted targets, giving 300 unique guarded targets.
The focused audit also checks nine finite positive and negative controls.
The earlier distance proof, datasets, dependency pins, and archived sources
retain their bytes. Exact distance twenty remains open; the submitted
exact-distance inventory remains nineteen.

## Replay

From the repository root, inside a detached, bounded Slurm allocation, run:

```bash
bash data/distance566-bound6-evaluation/2026-10-30/integration/replay.sh
```

The runner checks its source manifest, enforces one CPU of affinity, an effective
cgroup memory cap of at most 8 GiB, and zero permitted swap. It recompiles the
package root and runs all twelve guarded audits. Direct Lean invocations pass
the Lake configuration's `autoImplicit=false` and `maxSynthPendingDepth=3`
options explicitly, with one Lean thread and the compiler limit `-M7000`.

All project modules and pinned dependency artifacts must already be built.
This is a combined replay with retained artifacts, not a cold full-project build.
The source manifest covers active Lean sources, Python tools and tests, pins,
the prior distance and weighted exploration records, selected additive proof
inputs, and the exact runner. Mutable integration narratives and results are
excluded to avoid circular hashes.

## Evidence boundaries

The [validation record](integration-validation.json) confirms all 408 source
hashes before and after the run, the 124 standalone source entries, and the
403-entry tested Python snapshot. The exact tracked runner passed package-root
compilation and all twelve audits in 476.77 seconds. An additional fresh
main-audit compilation passed in 32.37 seconds.

The [resource record](job-results.json) reports a completed allocation, exit
`0:0`, and elapsed time `9:09`. Its limits were one CPU, one Lean thread, 8 GiB,
zero permitted swap, and twenty minutes. The runner process RSS was
2,027,100 KiB; the scheduler sampled 4,418,664 KiB for the batch step.
Those measurements have different scopes. No memory or time limit was exhausted.

All 114 default Python tests passed, with one expected optional SciPy skip.
Ruff, exact regeneration of the 79 weighted modules and compact certificate,
the ten earlier distance modules, and the removal emitter check passed.
The [Python record](../python-checks.json) belongs to a separate bounded
allocation; its tested sources still match this snapshot. The isolated
exploration environment separately covers all 22 weighted-search tests.

The first two integration attempts stopped before compilation on private
package-cache metadata and a missing configuration file. The successful run
uses isolated Git/configuration mirrors for all eleven pinned packages.
[Configuration hashes](pinned-configuration.json) identify 33 files restored
from pinned Git objects. Tracked pins and shared cache worktrees were unchanged.

The standalone report and its review precede this combined run; their pending
integration wording describes that earlier handoff. This directory supplies
the subsequent successful runtime result. The separate
[preservation manifest](preserved-sha256.txt) identifies 474 unchanged earlier
proof, data, archive, and pin files.

[Commands](commands.json) and [results](results.log) are sanitized.
Review reports distinguish source and record inspection from an independent
kernel replay. Private scheduler identifiers, connection details, paths, and raw
logs remain under ignored `.local/` storage.

The parser and certificate search remain outside Lean. The theorem concerns
the committed literal matrices; input hashes and exact byte regeneration
connect them to the upstream JSON files. No source-code distance hypothesis
is needed for the direct target proof.
