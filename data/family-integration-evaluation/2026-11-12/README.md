# Existing instances integrated with the analytic family theorems

The existing instance capstones now use the new family results in their actual
Lean proof terms. Public parameter statements and literal input rows are preserved.

Commit packaging excludes unrelated pre-existing irreducible-search work.
The clean staged snapshot passed **227 tests with 2 optional skips**; the earlier
322-test worktree run included 95 tests from that excluded work. All 206 focused
dependency sources match the verified sources, except trailing-newline cleanup
in two audit modules. Five audit files received that cleanup and all five were
rechecked successfully. [commit-scope.json](commit-scope.json) records the exact
scope, current source hashes, and selected package wiring; historical replay
hashes remain unchanged. [commit-audit-replay.json](commit-audit-replay.json)
records the fresh audit checks.

| Existing interface | Current proof path |
| --- | --- |
| Sixteen submitted bicycle applications and two even regressions | `Bicycle.Match.parameters_of_shortest` → `Connected.Match.parameters_of_shortest`, using an analytic basis minimum and a minimizing integer relation |
| Original `Bicycle262` and `Bicycle562` entry points | Identical family matrices, with explicit `HX_eq_original`/`HZ_eq_original`; public dimension, distance and rank bounds use the family proofs |
| Model and submitted 722 ranks and lower bounds | `code_eq_family` identifies the full `RectangleFamily.code 17 17`; ranks, dimension and lower 17 bounds call the family results directly |

The previous lower 9/15 statements are preserved as weakenings of17. The 722
weight 20 upper witness is retained separately. These changes preserve all
previous numerical conclusions; they prove no new exact-distance 20 result.
The three surface codes already use QECLean's surface family and are unchanged.
The 566 certificate bounds concern a different construction and are unchanged.

## Analytic arithmetic and generation

All 18 lattice minima have a [self-contained hand proof](../../../analytical/family-integration/PROOF.md).
It proves integral basis recovery and uniqueness, bounds the two coordinates
of a hypothetical short vector, derives the nine possible coordinate pairs,
and rules out all eight nonzero cases through four norm inequalities. Every
input, determinant calculation, strict bound and attaining relation is printed.
Three independent hostile referees checked all 18 rows by hand; see the
[review record](../../../analytical/family-integration/REVIEWS.md).

`scripts/bicycle_lattice_arithmetic.py` discovers candidate bases with exact
integer swaps and shears. The emitted Lean proof checks the displayed identities
and inequalities and applies the universal symbolic theorem. The discovery
procedure is not a mathematical premise. No lattice window is searched.
The compatibility declarations named `finite_exclusion` now follow from the
analytic bound and are absent from the migrated parameter proof paths.

`gen_bicycle_family.py` emits the new adapter calls. Existing generated
`Input/*Data.lean` and `Input/*Match.lean` remain byte-for-byte unchanged.
Stored physical witnesses remain independent compatibility controls; the
family theorem constructs the witnesses used by each parameter proof.
[instances.json](instances.json) records all 18 input hashes, normalization
parameters, basis vectors, and minimizing relations.

The [adapter explanation](../../../analytical/family-integration/ADAPTERS.md)
records normalized-to-joint recognition and exact rectangle specialization.
Each transfer argument also received three independent document-only passes.

## Verification and proof dependencies

The ordered replay passed **68 modules**. Two legacy focused audits were then
rechecked after replacing their package-umbrella import with direct imports
of their targets. There are 70 recorded compiler invocations and **162 guarded
axiom commands in the final sources**. All use only subsets of `propext`,
`Classical.choice`, and `Quot.sound`; none of the audited capstones depends
on `sorryAx` or `native_decide`.

The new command `#guard_dependencies` follows the types and proof bodies of
project constants, including private constants. It checks proof reuse rather
than imports alone. Twenty bicycle parameter targets must reach both the new
shortest-relation theorem and `BasisSeparation.BasisData.norm_ge`; they must
not reach old finite-exclusion declarations, stored wx/wz witnesses, or the
original 262/562 coverage/check certificates. Two submitted722 targets must
reach family rank/distance results and avoid the old charge-specific route.
All 22 positive checks passed. Two negative controls also passed by verifying
that a missing required dependency and a forbidden dependency are rejected.
This elaborator adds no axiom or mathematical proof term.

The complete current focused import closure has 206 project sources and no
missing compiled project artifact. It does not import the cached package
umbrella. Dependencies and toolchain remain pinned. This is a warm-import
integration replay, not a cold full-package build;234 unrelated inherited
artifacts remain absent from the full package's current source closure.

The ordered compiler times total 247.973 seconds; the two final audit rechecks
total 6.697 seconds. Maximum reported child-process RSS was 4,013,964 KiB.
The detached services enforced 5 GiB memory, 128 MiB swap, one CPU and one Lean
thread, 1,200 seconds wall time, and 1,140 seconds CPU time. Raw logs remain in
ignored `.local/`.

Python validation passed: **322 tests, 2 optional skips** in 53.04 seconds.
After the final emitted-proof adjustment, all 37 focused generator/arithmetic
tests passed again, including 18 four-file byte-for-byte regeneration cases.
Repository lint, formatting, explicit replay-helper checks and
`git diff --check` passed.

## Records and reproduction

- [results.json](results.json): scope, limits, pins, proof/supporting-file hashes, and verification counts.
- [replay.json](replay.json): current successful result for each of 68 modules, with exact source hashes.
- [ordered-replay.json](ordered-replay.json): original ordered 68-module run.
- [audit-import-recheck.json](audit-import-recheck.json): final two direct-import audit rechecks.
- [source-hashes.json](source-hashes.json): all 206 current project dependency sources.
- [replay.py](replay.py): ordered replay with source-change detection.

From the repository root, with Python 3.13 and pinned dependency artifacts
already available, launch inside a detached capped allocation:

```bash
systemd-run --user --unit=qldpc-family-integration-replay \
  --property=MemoryMax=5G --property=MemorySwapMax=128M \
  --property=CPUQuota=100% --property=RuntimeMaxSec=1200 \
  --property=LimitCPU=1140 --working-directory="$PWD" \
  /usr/bin/python3 data/family-integration-evaluation/2026-11-12/replay.py
```

The helper sets `LEAN_NUM_THREADS=1`, uses the retained pinned toolchain when
available, and stores raw output under `.local/family-integration-2026-11-12/`.
It does not allocate resources itself. Its optional `--modules` selection
permits a focused recheck within the same bounded allocation; use a separate
`--record-dir` to preserve earlier records.
