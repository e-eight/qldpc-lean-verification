# Python integration validation

The corrected **v2 allocation passed**: 169 tests passed, two expected optional
SciPy tests skipped, and Ruff check/format passed. All requested regeneration
checks passed byte-for-byte: 59 sector modules and the canonical compact record,
79 weighted modules and compact record, ten earlier coordinate/packing modules,
and 39 removal modules. These are source-byte checks, not a Lean kernel replay.

[validation.json](validation.json) is the aggregate;
[commands.json](commands.json) contains all eighteen successful timed commands.
The [pytest summary](pytest-summary.txt) names both skips. The earlier isolated
SciPy-enabled numerical tests remain separate immutable evidence in
[final-validation-v2](../numerical/final-validation-v2/execution.json); no LP or
search ran during this integration check.

## Tested bytes and controls

The frozen emitter SHA256 is
`786f1fc5f0a91a88e10893b89346f447f4d756f492bdfc6ae637f338b1527ed4`;
its test SHA256 is
`47dea81cb55c4b2c6e776e6c270e56e1beb800af878a4fd3bb5fe469b8b4af79`.
[source-sha256.txt](source-sha256.txt) has 347 entries and SHA256
`c626e49e4ea6a90be57983218833e891cf447f5691b034677102a76e34cf940b`.
Every entry matched before and after execution and still matches the repository.
The six orchestration sources and 59 generated sector sources also matched
before and after. All 2,902 staged upstream JSON/verification-Python entries
matched their fresh input inventory afterward. The identities record separately
checks both pinned endpoint literals, the audited 225 input, and frozen exporter
inputs. An observed file inventory alone does not prove a Git revision.

The sector check explicitly used
`literal-z/generated/compact.json.gz`, SHA256
`41422a45f3af02da426ce99d35f58f2b7c40a0083a5a44a7832e9dcde18870e2`.
The earlier ten modules were regenerated in private temporary directories, then
compared with the retained sources. No existing generated data was overwritten.

[resource-gate.py](resource-gate.py) is the exact resource-preflight source copy.
Its gates use explicit `SystemExit` failures. The runner unsets `PYTHONOPTIMIZE`
before all Python commands; both the resource preflight and locked production
environment recorded optimization flag zero. Production commands have no `-O`
flags. The fresh default environment used Python 3.13.3, NumPy 2.5.4, pytest 9.2.0
and Ruff 0.16.10, with SciPy absent. Locked offline uv setup reused retained
Python/package caches; no Lake cache or solver environment was needed.

## Resources and contained first attempt

V2 completed with scheduler exit `0:0` in **101 seconds**. It enforced one CPU
affinity, one thread, 8 GiB cgroup memory and zero swap, with a 20-minute cap.
Sampled batch RSS was **515,716 KiB**; the largest per-command GNU time RSS was
**283,688 KiB**. These measurements have different scopes. The test command took
64.89 seconds; the sector and weighted emitter checks took 9.74 and 2.24 seconds.
The [job record](job-results.json) preserves both attempts separately.

[V1](attempt-v1/failure.json) stopped at pytest: 164 passed, two skipped and five
orbit-generator tests failed because the staging list omitted the tracked
`data/reps/262-2-15.json` fixture. Later checks were not reached. V2 added that
one immutable input to the 346-entry snapshot. No production code, tests or pins
changed. V1's source inventory, receipts and failure record remain intact.

No Python-worker allocation remains active; the second slot was released to the
parent immediately after terminal success. No further compute is planned for
this record. Parent-owned Lean integration and documentation remain separate.
Raw logs and operational details stay ignored. [Changed paths](changed-files.txt)
and [artifact hashes](artifacts-sha256.txt) identify this public handoff.
