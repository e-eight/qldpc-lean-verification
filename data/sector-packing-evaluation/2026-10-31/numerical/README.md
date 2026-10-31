# Numerical sector-packing handoff

The complete Z continuation gate passes exact numerical validation. The X
continuation pilot passes for its 32 requested patterns and remains incomplete.
These records add no Lean theorem: the baseline kernel result is `6 <= d <= 20`.
Final independent review and the literal Lean application belong to the parent
task. See [numerical-validation.json](numerical-validation.json) for machine-readable gates.

## Results and scope

| Bounded side | Detector side | Good-class rank | Residual dimension | Checked patterns | Pool supports | Residual packing bounds |
| --- | --- | --- | --- | --- | --- | --- |
| Z | X | 15 | 3 | All 7 | 5,885 | 11–13 |
| X | Z | 7 | 11 | 32 of 2,047 | 8,306 | 11–13 |

Every checked pattern has exact positive integer weights with `6 * cap < W`.
The Z result combines the fifteen original good-family certificates with all
seven residual certificates to supply numerical evidence for `d_Z >= 7`.
The stronger residual bounds do not strengthen the original good-family bounds.
The X pilot leaves 2,015 patterns unchecked, so it supplies no complete X bound
of seven and no stronger overall-distance claim. No lighter logical witness
search was performed.

Both pools use all 64 original target detector classes, excluding classes whose
quotient image is zero. Supports are deduplicated once; every original provenance
and its own-base stabilizer-row witness is retained. Representatives in a sector
family may have different logical classes. No enrichment or new representative
search was needed.

## Inputs and coordinate conventions

The baseline is `e9e33f21946bc781e6ae3c3c04adaac86abb36dd`. The literal 566
input SHA256 is
`061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be`,
at challenge revision `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.
[source-sha256.txt](source-sha256.txt) identifies the immutable unpruned focused
export, analysis export, canonical paired bases, validation helpers and current
sources. The compact-six export was not used as threshold-seven evidence.

The original selected 18-detector basis and its separately paired witnesses are
unchanged. A detector's selected coefficients are its physical pairings with
those witnesses. Its quotient class is the suffix after the good prefix.
A residue's selected logical pairing coordinates are its suffix pattern shifted
past that prefix; its canonical 18-bit class is exported separately. The physical
reference is the corresponding XOR of paired witnesses. The validator checks
direct physical pairing one as well as both coordinate descriptions.

The stdlib validator independently checks literal commutation/ranks, cycles,
paired bases, good-prefix rank, full annihilator dimension, all seven nonzero Z
patterns, source alignment, original-row membership, support/index ranges,
positive integer weights, all physical loads, capacities and strict thresholds.
Floating-point LP results only propose weights. Exported duals bound each stored
eligible pool; they establish no globally priced optimum or impossibility.

## Reproduction and source chronology

[commands.json](commands.json) records the executed commands with relative staged
paths. Run substantive work only in a detached bounded allocation. The isolated
environment was a private copy of the prior hash-locked numerical environment:
Python 3.13.3, NumPy 2.5.4, SciPy 1.16.3, pytest 9.2.0 and Ruff 0.16.10. No project
dependency files were changed. Software and preflight resource facts are saved
with each run.

Each pilot had a 180-second soft packing budget and at most four LP seconds per
pattern. Selection is deterministic, with no random seed. All 39 LP calls returned
status zero; exact exported arithmetic and independent validation establish the
reported gates. Fixed inputs serialize deterministically with gzip timestamp
zero, tested byte-for-byte. Cross-platform solver reruns need not choose identical
optimal weights; retained certificate bytes are the exact validation targets.

The initial Z allocation ran **20 tests**. Its source bytes were archived before
the review-driven test update. The X pilot used the same source version and did
not repeat the tests. The final validation ran **28 tests, zero skips**, Ruff, and
fresh independent Z/X validation, with no search rerun or certificate changes.
The eight added cases cover a nonidentity paired basis with nonempty Bell-pair
checks in both orientations, consistent basis permutations with wrong prefix or
reference, and nonvacuous cycle/annihilation failures.

[source-snapshots/index.json](source-snapshots/index.json) binds both archives,
their source manifests and their test hashes. Each archive contains six source
or configuration files; the three immutable data inputs remain at their hashed
repository paths. The historical certificate headers and Z/X source manifests
intentionally retain the original 20-test hash. The current manifest identifies
the 28-test source. No old execution or certificate record was rewritten.

## Resources and remaining work

| Allocation label | Terminal state | Wall seconds | Scheduler-sampled batch RSS |
| --- | --- | --- | --- |
| pilot-z-v1 | COMPLETED, exit 0 | 99 | 614,904 KiB |
| pilot-x-v1 | COMPLETED, exit 0 | 133 | 236,676 KiB |
| final-validation-v2 | COMPLETED, exit 0 | 41 | 229,032 KiB |

Each allocation enforced one CPU affinity, one thread, 8 GiB cgroup memory and
zero cgroup swap. Pilots had 20-minute limits; final validation had 15 minutes.
They ran serially. No numerical allocation remains active. Per-command GNU time
maxima and wall times are separate from sampled scheduler RSS in the execution
records; the first allocation also prepared the private environment.

Packing alone took 24.4 seconds for Z and 102.4 seconds for X. Linear extrapolation
from the X pilot gives about 109 minutes for 2,047 patterns, excluding setup,
validation and export. The sampled patterns favor low population count; this is
only a resource estimate. Full X execution requires the parent's review and
resource decision. No full campaign or new Lean run was launched.

The next useful step is independent approval of the frozen numerical gate and a
literal Z-sector Lean application. [changed-files.txt](changed-files.txt) lists
this worker's files; [artifacts-sha256.txt](artifacts-sha256.txt) freezes the public
numerical handoff independently of parent-owned documentation and reviews.
