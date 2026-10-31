# Independent Python validation-record review

## Verdict and scope

**No blocking findings. The frozen Python integration-validation record is
approved.** The actual receipts support 169 passing tests, two expected optional
SciPy skips, successful Ruff checks, and all requested source-byte regeneration
checks. The first attempt's staging omission is preserved and resolved without
changing production code, tests, or dependency pins.

This review approves the Python record only. It does not approve literal Lean
proof readiness, establish a new kernel result, or substitute for generated
module/capstone compilation and axiom review. No tests, Python, generator,
solver, search, Lean, or cluster job was rerun. Independent work consisted of
static inspection, file hashes, inventory comparisons, and retained-record
comparisons. Only this report was written.

## Actual execution evidence

The public handoff declares `status: passed`, identifies `attempt-v2`, and has
an explicit completed public freeze. All eighteen published timed command
receipts equal their fetched counterparts. Their exit codes, GNU time wall
measurements, and process RSS values agree with the retained time files;
every v2 exit is zero. Public per-attempt receipts also match the fetched
records. The separate v1 failure has not been rewritten as a success.

The actual full pytest command is `uv run --locked --offline pytest -q -ra`,
using the configured `tests/` test path without a reduced selection. Its raw
log reports **169 passed, 2 skipped in 63.91 seconds**; the command wrapper
takes 64.89 seconds. Both skips are named: the weighted LP test at
`tests/test_distance566_weighted.py:85` and the sector LP test at
`tests/test_distance566_sector.py:351`. The recorded default locked environment
has SciPy absent. Earlier isolated SciPy-enabled tests remain separate evidence;
they are not counted as executed by this run.

Ruff check reports success and Ruff format reports 39 files already formatted.
The configuration covers `pyproject.toml`, `scripts/**/*.py`, and
`tests/**/*.py`. All 39 current Python files under scripts/tests are present in
the tested source inventory.

## Regeneration association

The actual commands, raw logs, and successful receipts support all **187**
requested generated-module byte checks:

| Group | Modules | Evidence inspected |
| --- | --- | --- |
| New sector inputs | 59 | Emitter `--check`, explicit canonical compact path, generated-source pre/post checks |
| Earlier weighted inputs | 79 | Weighted emitter `--check`, including its compact artifact |
| Earlier distance inputs | 10 | Separate coordinate/packing regeneration and ten explicit `cmp` commands |
| Removal inputs | 39 | Pinned removal emitter `--check` and its actual 39-module output |

The sector command explicitly uses
`literal-z/generated/compact.json.gz`, SHA256
`41422a45f3af02da426ce99d35f58f2b7c40a0083a5a44a7832e9dcde18870e2`.
It checks the retained 1,138 good representatives, seven residual families,
and 172 used pool supports. It does not silently validate a different default
output path. The weighted compact retains SHA256
`77c943fdc42dce81207f80e007942a0a794fba1f21efac4cdf3f585837b5e800`.

The earlier ten outputs are regenerated under ignored temporary paths and
compared with their retained sources: five coordinate modules and five packing
modules. The comparison wrapper uses `set -euo pipefail` and only prints its
success marker after all ten comparisons. None of these byte checks claims
Lean elaboration or kernel verification.

## Tested bytes, pins, and controls

All **347** source-inventory entries match current repository bytes. The
source pre/post raw logs contain exactly those paths and 347 successful checks
each. The inventory includes all 59 new sector inputs, all 79 weighted inputs,
the old ten and removal 39, Python tools/tests, required fixtures, and selected
stable source material. Mutable handwritten proof and documentation paths are
outside this snapshot, as intended.

All six orchestration hashes match; their pre/post logs have the same six
successful paths. The public `resource-gate.py` is an exact copy of the
executed gate. Both sector-generated hash flights have exactly 59 successes.
The fresh upstream input inventory has 2,902 successful postflight checks;
independent local hashing, with the staging alias mapped to the upstream
checkout, also matches all 2,902 entries.

The identity step independently binds the 566 and 578 endpoint JSON files,
the audited 225 JSON input, the frozen exporter/test, and the canonical sector
compact artifact. Its expected revision label is not represented as a fresh
Git-checkout attestation: the record explicitly distinguishes observed staged
file identity from proving an entire upstream commit.

The current `pyproject.toml` and `uv.lock` hashes match the tested inventory.
Setup uses `uv sync --locked --offline --python <python-bootstrap>`, and all
production invocations use the locked offline environment. Software preflight
requires Python 3.13 and records 3.13.3, NumPy 2.5.4, pytest 9.2.0, and Ruff
0.16.10. Interpreter association comes from that explicit command and observed
preflight; `.python-version` is not in the 347-entry snapshot.

The batch runner unsets `PYTHONOPTIMIZE` before Python execution. Both resource
and production preflights record optimization flag zero and an absent
`PYTHONOPTIMIZE`; commands contain no `-O` flag. Resource gates use explicit
`SystemExit` failures rather than removable assertions. They require finite
positive effective memory at most 8 GiB, zero effective swap, one CPU affinity,
and all four recorded numerical-thread environment variables equal to one.
The worker used retained offline package/interpreter caches, not a solver
environment or a Lean build cache.

## Contained v1 failure

The v1 raw pytest log and receipt record **five failures, 164 passes, and two
skips**, exit one. All five failed cases are orbit-generator regressions; their
tracebacks report insufficient independent classes. The generator conditionally
loads saved representatives from `data/reps/<slug>.json`, so omission of the
262 saved fixture explains the diagnosed staging failure.

The inventory comparison is exact: v1 has 346 entries, v2 adds only
`data/reps/262-2-15.json`, and there are no removed paths or changed hashes on
the shared entries. That fixture has SHA256
`31696a0efaeb18e3c192a1d5c020038a317b119750a0a208cb0743f2c26bd0ca`.
The production/test/pin bytes are identical. V1 explicitly records that Ruff,
regeneration, and postflight steps were not reached. V2 supplies their separate
successful execution rather than attributing them to v1.

## Resources, preservation, and reviewed identities

Retained terminal accounting agrees with the public v2 allocation record:
`COMPLETED`, exit `0:0`, 101 seconds, one CPU, 8 GiB, zero swap, and a
twenty-minute wall cap. Sampled batch RSS is 515,716 KiB. The largest recorded
command-process RSS is the pytest command's 283,688 KiB; these measurement
scopes differ. The record preserves v1 separately as a failed 86-second
allocation. No new scheduler query was made for this review.

The final artifact inventory covers all 51 other public files in the Python
handoff and every digest matches. Earlier numerical and disjoint diagnostic
inventories still verify their 35 and 21 entries respectively.

| Reviewed identity | SHA256 |
| --- | --- |
| Validation aggregate | `b897420ebc4c96db23434a3456af66aba5027a1da477d2060b4d2fa9b3728872` |
| Source inventory | `c626e49e4ea6a90be57983218833e891cf447f5691b034677102a76e34cf940b` |
| Orchestration inventory | `69577045ae40fe558caf1576fe669895f98f284501b8ed79a6141e357baf32a7` |
| Upstream input inventory | `4009565b720ba70d6327f7925214597f32c270b6779b06434ef84219ab8a37b9` |
| Commands record | `83f168e26a682552c4fd9dffbcb92633f7991cc9bb6fb281d37469edd40f7091` |
| Artifact inventory | `fce13abf08c9065f6250b566cb20cf2bc5da07713df9efcb381608ab58284639` |
| Resource-gate source copy | `56d67ae8a543b04757f7863bbf8098143aa68f26832d5286a205f54c977642f8` |
| Frozen sector exporter | `786f1fc5f0a91a88e10893b89346f447f4d756f492bdfc6ae637f338b1527ed4` |
| Frozen sector exporter tests | `47dea81cb55c4b2c6e776e6c270e56e1beb800af878a4fd3bb5fe469b8b4af79` |

Evidence paths are under `../python-validation/`, relative to this review.
The conclusions concern the exact retained run and current matched snapshot;
they are not an independently repeated Python run or approval of any ongoing
literal Lean integration. No further Python rerun is indicated by this review.

## V3 follow-up: corrected template, frozen execution record

**No blocking findings. The frozen Python-v3 record is approved.** This follow-up
reviews the separate [v3 handoff](../python-validation-v3/README.md) against its
retained execution records and current source bytes. The original v2 review
above is unchanged; its complete original bytes have SHA256
`8a1ff3862334c84e81b0f9e803481ccee645faec2effbf2f74654452c20b3080`.
Its results remain attributed to the original template version.

### Execution and generated-source association

All eighteen public command receipts match their fetched counterparts exactly
and agree with the commands aggregate. Every exit is zero; all eighteen GNU
time files agree with the corresponding recorded exit, wall time, and process
RSS. The retained allocation log also contains the final successful-completion
marker. These are inspected execution records, not independently repeated runs.

The full default command remains `uv run --locked --offline pytest -q -ra`, with
no reduced selection. Its raw output reports **169 passed, two skipped in
62.86 seconds**; the command wrapper records 63.85 seconds. The skips are the
same optional SciPy tests at `test_distance566_sector.py:351` and
`test_distance566_weighted.py:85`. The recorded locked environment has SciPy
absent; separate SciPy-enabled numerical evidence is neither rerun nor counted
here. Ruff reports success and 39 files already formatted; all 39 current
Python files under `scripts/` and `tests/` occur in the tested source snapshot.

Actual commands, raw output, and receipts support all **187 module byte checks**:
59 sector, 79 weighted, ten earlier coordinate/packing, and 39 removal modules.
The canonical sector compact is explicitly supplied to the sector emitter; both
sector and weighted compact identities remain unchanged. Sector output reports
1,138 good representatives, residual counts `[31, 35, 32, 33, 30, 28, 33]`, and
172 used pool supports. The ten earlier outputs are regenerated privately and
compared under a fail-fast shell wrapper. No byte check implies Lean acceptance.

Both generated-source flights use the **corrected** manifest at
`literal-z/proof/template-v2/generated-source-sha256.txt`, SHA256
`ceb066e1948071dad4989871bc9f04df9706b0a5d54852e484dd0407fe7f08c4`.
Their raw logs contain exactly its 59 paths, all successful. The historical
generated manifest is preserved rather than applied to the repaired aggregator.

### Source identity, controls, and preservation

Independent file hashing confirms all 347 tested source entries, six
orchestration entries, 59 corrected module entries, and 2,902 upstream input
entries. The staged `inputs/` prefix was mapped to the upstream checkout for
local input comparison. Raw pre/post logs contain exactly the corresponding
inventory paths with successful checks; the input inventory has its successful
postflight. The three pinned input literals and supplied source identities also
match. As documented, an observed file inventory does not itself attest an
upstream Git revision.

Compared with v2, the shared snapshot changes exactly the emitter and Packing
aggregator hashes, and replaces the historical generated-manifest entry with
the corrected manifest entry. The other 58 generated modules, emitter tests,
canonical compact, dependency pins, and all other shared entries retain their
bytes. Current emitter/Packing identities are `6640651b…aa694c2` and
`9744afd6…bba5a6`; their full digests are recorded in the v3 README and the
[exporter follow-up](exporter-review.md). All 51 historical Python-record
artifacts, 35 numerical artifacts, and 21 disjoint-diagnostic artifacts still
match their original inventories. The v3 inventory covers exactly its 39 other
public files, and its changed-path list covers all 40 public files.

The executed resource gate matches the published source copy. Static inspection
confirms explicit `SystemExit` failures for memory, swap, affinity, threading,
and optimization violations. The runner unsets `PYTHONOPTIMIZE`; both observed
resource and production preflights report optimization zero. Locked offline
commands use no `-O` flag. The production preflight records Python 3.13.3 and
the expected SciPy-free package environment. Interpreter identity is established
by the explicit bootstrap command and preflight, not by adding `.python-version`
to the snapshot.

Retained accounting supports `COMPLETED`, exit `0:0`, 103 seconds, one CPU,
8 GiB, and a twenty-minute wall limit. The resource receipt records zero swap.
Scheduler-sampled batch RSS is 514,604 KiB; maximum command RSS is 282,832 KiB.
These scopes are correctly distinguished. Slot release and no remaining worker
allocations are reported in the handoff; no independent scheduler query was
made. The earlier stale expected hash stopped before staging or compute and
remains separately preserved as a resolved metadata mismatch.

### Reviewed V3 identities and limits

| Reviewed identity | SHA256 |
| --- | --- |
| Validation aggregate | `8fa01f55a57aeeeefd9ac742afccb6ded3397c1cbeaeb75be9e50610709b2f37` |
| Source inventory | `3cb3c9041d49da85862516b95eb6c639a623849e142075aa5dbe2df2ee135e8d` |
| Commands record | `92f6d8f643e48c8db8b8bb243f5eed8ad0c21b96cf84f60b02b5f4fa24d03032` |
| Orchestration inventory | `edd32c14c561c42dc8a9afc3875882a1669054f4737d837c03c22b48ad9e9871` |
| Upstream input inventory | `4009565b720ba70d6327f7925214597f32c270b6779b06434ef84219ab8a37b9` |
| Job results | `9862855f775c568880859ec27b3c72a7e1743e8e3a783158da3f0643858c3c85` |
| Artifact inventory | `0e0f2d1d093145bd70d353914feb6b9fefc4d31ebbfba9337384c1da11ab7f13` |

Evidence paths for this follow-up are under `../python-validation-v3/`.
No tests, Python, generators, search, solver, Lean, or cluster jobs were run for
this review. Only this report was updated. This approval concerns the Python
record and exact generation association; it does not approve the ongoing
handwritten Lean capstone/audit or establish a new literal kernel bound.
