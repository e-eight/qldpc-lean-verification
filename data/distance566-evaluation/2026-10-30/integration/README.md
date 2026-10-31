# Integration of the reviewed 566 partial distance proof

The submitted `566-18-20` matrices have kernel-proved overall bounds `3 <= d <= 20`.
Complete eighteen-coordinate coverage and explicit packing certificates prove both sector lower bounds of three.
The submitted weight-twenty X witness supplies a nontrivial Pauli logical attaining the upper bound.
Exact distance twenty remains open, and the submitted exact-distance inventory remains nineteen.

## Review and source scope

The [independent review](../independent-review.md) found no blocking mathematical findings.
It covered all fifteen new Lean modules, four Python scripts, tests, literal input associations, and the recorded validation evidence.
The reviewer inspected proofs and execution records without a separate Lean replay.

The reviewed distance modules retain their original bytes.
The only existing proof files changed for integration are the package umbrella and main audit.
The umbrella imports `Distance566Pauli`, and the main audit adds fourteen guards for a total of 270 unique targets.
The replay also runs the focused distance audit, including its two finite row-combination controls.

The separate [integration review](independent-review.md) found no blocking findings in the exports, audit coverage, replay paths, or documentation.
It confirmed all fourteen focused targets in the main audit and consistent bounds and inventory across the root documents.
That review did not rerun Lean or Python checks.

The parent [implementation record](../README.md) preserves the standalone compilation and search evidence.
Its review status field and integration checklist describe the implementation handoff, when review and integration were pending.
The original source and artifact manifests remain unchanged.
This record supplies the subsequent review and combined-validation status.

## Combined validation

The combined cluster replay passed source preflight, package-root compilation, and all eleven guarded audits.
The main audit has 270 unique guarded targets, including all fourteen focused distance targets.
The replay took 439.54 seconds with retained project and dependency artifacts.
An additional main-audit check passed in 30.76 seconds.
All 81 Python tests, Ruff, shell syntax, and byte regeneration of the ten generated modules passed.
The reviewed proof modules and original implementation records retain their hashes.

The [validation record](integration-validation.json) gives source identities, audit targets, dependency pins, and check outcomes.
The [resource record](job-results.json) reports a completed allocation with exit `0:0` and elapsed time `8:11`.
The [command record](commands.log) and [result summary](results.log) are sanitized.

`source-sha256.txt` covers the active Lean sources, Python tools and tests, dependency pins, implementation records, and this replay script.
The script checks every recorded hash before compiling.
It recompiles the package root and runs all eleven guarded audits with one Lean thread.

From the repository root, inside a bounded Slurm allocation, run:

```bash
bash data/distance566-evaluation/2026-10-30/integration/replay.sh
```

The replay requires the project modules and pinned dependency artifacts already built.
Its measurements describe a combined replay with retained artifacts, not a cold full-project build.
Connection details, scheduler identifiers, workspace paths, and raw logs remain under ignored local storage.

The allocation used one CPU, one Lean thread, an 8 GiB memory limit, and zero permitted swap.
Its wall limit was twenty minutes, and no memory or time limit was exhausted.
The replay's maximum child-process RSS was 2,044,312 KiB.
The scheduler's sampled step MaxRSS was 4,294,864 KiB.
These measurements have different scopes and do not represent a cold-build memory requirement.

## Documentation and remaining work

The root README states current capabilities, recommendations state research priorities, checks and results preserve dated evidence, and certificates describe the checker interface.
The Lean README lists the new modules and the replay entry point.
The numerical candidate families do not establish an impossibility of stronger packing certificates.

The next experiment uses lighter spanning detector candidates to improve the weighted families.
A source-based route still needs source lower bounds, and Z lifting also needs a weight-controlled correction argument.
The QECLean contribution is a separate upstream PR and does not change this project's dependency pin.
