# Logical-coordinate sector packing prototype

Status: kernel replay passed for all three modules, 25 guarded axiom targets,
and ten finite controls. This generic prototype does not change any bound for
the submitted codes. Shared root imports, the main audit, and concrete target
adapters remain the parent integration's responsibility.

## Mathematical contract

`SectorPacking.pairing_eq_of_coordinates` uses a complete
`CoverageCertificate S B k`. Equal coordinates imply that the physical difference
lies in `B`. A detector annihilating `B` therefore pairs equally with every
representative of that sector. The annihilation hypothesis is explicit.

`weight_ge_of_sector` reuses the existing natural-weight overlap theorem. Every
detector must pair to one with the reference; detectors may come from different
logical classes. Per-qubit weighted load is at most `cap`, and the strict integer
threshold is `(D - 1) * cap < totalWeight`. No physical basis change is used.

`Certificate` packages this finite data. `Certificate.lower_bound` applies it to
all physical cycles with the specified coordinates. Homological X and Z adapters
discharge boundary annihilation using opposite-cycle membership.

## Coverage and examples

`weight_ge_of_coordinate_cover` combines existing detector bounds with a stated
cover of every remaining nonzero coordinate pattern. The prefix/suffix version
uses a complete paired basis of size `r+s`: after zeroing the first `r` logical
coordinates, all `2^s-1` nonzero suffixes need certificates. Basis suffixes alone
do not cover their sums. Logical coordinate maps carry no physical weight claim.

The two-qubit zero-check example mixes the two unit detector classes. Together
they certify sector `11` at two, although either singleton family has threshold
one and the code still has a nontrivial vector of physical weight one. Further
controls exhibit wrong-sector pairing, omitted sum patterns, and failure to
transfer pairing when boundary annihilation is absent. In the stronger negative
control, reference `11` and weight-one cycle `01` have equal second-bit
coordinates and differ by boundary `10`. Both unit detectors pair with the
reference, but the first detects that boundary and misses the weight-one cycle.

## Replay policy

All Lean compilation runs in detached cluster allocations with one CPU, one Lean
thread, an enforced 8 GiB memory ceiling, and zero swap. Direct Lean invocations
pass `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`. A fresh task output
directory reads retained project and pinned dependency artifacts. Prior sources,
artifacts, dependency configurations, and the bound-six proof remain unchanged.
Raw operational records and private cluster details stay in ignored `.local/`.

The exact frozen replay took 130.79 seconds with GNU time maximum process RSS
2,105,224 KiB. Source checks passed before and after compilation. All axiom
guards permit only `propext`, `Classical.choice`, and `Quot.sound`, with smaller
subsets where applicable. No capstone depends on `sorryAx` or `native_decide`.

The [source manifest](source-sha256.txt) identifies the three new modules, two
retained theory dependencies, project pins, and replay/resource-check scripts.
The [results](results.json), [resources](resources.json),
[dependency identities](dependencies.json), and [fresh artifact hashes](artifacts.json)
record the executed scope. The dependency check matched all eleven manifest
revisions. [proof-modules.txt](proof-modules.txt) lists the compile order, and
[allocations.json](allocations.json) records both successful terminal allocations.
Neither task allocation remains active.

With the matching pinned compiler, dependency artifacts, and retained project
imports already available through `PATH` and `LEAN_PATH`, run this in the bounded
allocation from the project root:

```bash
bash data/sector-packing-evaluation/2026-10-31/lean-prototype/replay.sh
```

The runner independently rejects excess cgroup memory, nonzero swap, or CPU
affinity wider than one CPU. It also refuses to overwrite linked retained
artifacts. Replay uses warm dependencies; it is not a cold full-project build.
Earlier development failures concerned import-root staging and explicit
decidability steps in toy examples; they are summarized in the results.
