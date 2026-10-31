# X32 disjoint certificate-size diagnostic

The prescribed greedy diagnostic found **zero seven-disjoint families in 32
sampled X sectors**. This branch is stopped. Greedy failure does not establish
infeasibility, a maximum disjoint-family size, or any code-distance obstruction.
No full 2,047-sector campaign, LP, enrichment, or Lean run was performed.

## Frozen inputs and method

The input is the approved X32 certificate, SHA256
`e5e8f386598416454e563307c55024cf6a7fff36ff1263daad5fbfd00489ccfd`,
with 8,306 stored Z-detector supports. It uses the literal 566-qubit input, SHA256
`061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be`,
at challenge revision `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.

Before searching, the frozen stdlib validator checked all immutable source hashes,
literal matrices, bases, pool provenance and original source alignment. Search
used only the original 32 patterns. Eligibility required quotient pairing one;
every eligible detector's physical mask was also checked directly against the
residue reference.

Each pattern tried shortest-first ordering followed by eight deterministic
within-length tie shuffles, seeds 0–7. A bitwise AND with the occupied mask
prevented physical overlap. All nine orders were tried for every pattern.
The search had a 90-second soft limit inside a 15-minute allocation.

## Results

Search took **0.736445 seconds**. Per-pattern times ranged from **0.015962 to
0.025693 seconds**; every time, attempted order and best partial index list is in
[summary.json](candidate-v1/summary.json). Seven patterns reached four detectors,
22 reached five, and three reached six. The patterns reaching six were 2, 48
and 64. These are found partial sizes, not upper bounds.

There are no successful seven-detector selections: their selected-pool union is
empty and its maximum/average physical weight is undefined. The producer's empty
maximum default of zero is identified explicitly in
[diagnostic-profile.json](diagnostic-profile.json).

All 32 original LP cases were retained unchanged in the new
[candidate](candidate-v1/candidate-v1.json.gz), SHA256
`2a354107c64cf1ad198a62ba79309de2b1de76b519ec28b34b9fe1535d2a8a7d`.
Its new header records the parent certificate and diagnostic source identities.
The original pool, paired basis and complete residue objects are unchanged.
The candidate's passing thresholds therefore refer to the retained LP weights,
not to newly found unit families. The record remains 32 of 2,047 sectors.

A separate frozen-validator CLI replay passed exact source alignment and all 32
retained arithmetic cases. No numerical lower bound was strengthened, and no
new kernel theorem is claimed. The prior `6 <= d <= 20` checkpoint and the
separate literal Z-sector work are unaffected.

## Checks, resources and reproduction

All **11 new tests passed, zero skips**, including unit-seven success, physical
overlap rejection, quotient/direct-pairing failures, strict equality at six,
pinned input hashes and deterministic gzip output. Ruff check and format check
passed. The new tiny positive case also passes the frozen `check_case` function.

The single allocation completed with exit zero in **59 seconds**, using one CPU
affinity, one thread, enforced 8 GiB cgroup memory and zero cgroup swap. Sampled
batch RSS was **639,868 KiB**, including private environment preparation. The
diagnostic command, which includes original validation and final export/validation,
took 19.78 seconds with GNU time maximum RSS 184,504 KiB. Separate final validation
took 8.76 seconds and 154,648 KiB. No worker allocation remains active.

[commands.json](commands.json), [execution.json](validation-v1/execution.json),
[job-results.json](job-results.json) and the software/resource records preserve
the execution scope. The private environment was copied from the existing pinned
numerical environment; no dependency files changed and no solver was called.

[source-sha256.txt](source-sha256.txt) describes the exact staged bytes; its
`inputs/codes/` entry is a staging alias for the pinned upstream literal. The
[source snapshot](source-snapshot.json) retains the six relevant code/configuration
files. All ten frozen input/source entries matched before and after execution;
all thirteen execution-source entries matched afterward. Prior numerical outputs,
28-test sources and archives remain unchanged. Raw logs and access details stay
ignored. [changed-files.txt](changed-files.txt) lists this worker's new paths.
