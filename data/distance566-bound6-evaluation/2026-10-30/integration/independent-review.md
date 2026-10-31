# Independent integration review

## Outcome

No blocking correctness, integration, or documentation findings. No separate
polish changes are requested. This completes the combined-integration review;
the earlier standalone proof and exploration reviews remain unchanged.

## Scope and execution evidence

Reviewed the shared package/export and audit changes, all four root documents,
`lean/README.md`, the standalone README, and this directory's runner, manifests,
commands, validation summary, job summary, configuration inventory, and results.
Compared the public execution summaries with the retained integration-v3 command
JSON, raw output, GNU time files, resource observation, and terminal scheduler
record. This was source and evidence inspection, not an independent kernel run.
No tests, generators, searches, Lean commands, or cluster operations were run.

All ten public execution-step summaries agree with the retained command records
and time files. The recorded runner exited zero, printed the expected Lean
4.30.0-rc2 version, compiled the package root, and visited exactly the twelve
audit modules in the documented order. The separate fresh main-audit command
also exited zero, explicitly wrote its `.olean`, and records the current main
audit's source hash. The public fresh-command metadata matches its retained
execution record exactly. The inspected runner and fresh-audit logs contain no
error diagnostics.

The exact runner's monotonic duration is 476.77045960805845 seconds; the fresh
main audit's is 32.37120593700092 seconds. The visible 476.77 and 32.37 values are
correct. Their separate GNU time measurements remain 476.76 and 32.36 seconds
in the correctly named JSON fields. The retained scheduler record supports
`COMPLETED`, exit `0:0`, and elapsed `9:09`.

The runner's 2,027,100 KiB process RSS and the scheduler's 4,418,664 KiB batch
sample are reported with different measurement scopes. Resource metadata agrees
between public and retained records: one CPU of affinity, one Lean thread,
8 GiB effective cgroup memory cap, zero permitted swap, and explicit
`-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3` compiler flags.
The documented twenty-minute allocation limit agrees with retained accounting.
These are observed warm-artifact replay measurements, not a cold-build memory
requirement or a measurement of the whole allocation's peak memory.

## Source, input, and configuration association

Independently hashed the current files in all three source inventories: 408
integration entries, 124 standalone entries, and 403 Python-test snapshot
entries; all are unique within their inventory and all match. The fetched
integration and Python manifest bytes equal their published counterparts.
The preflight/postflight raw outputs contain exactly the appropriate manifest
paths, each ending in `OK`: 408 before and after integration, 124 standalone,
and 403 for the tested Python snapshot. The runner's own output also contains
all 408 successful checks.

Parsed both literal-input raw logs. Their 566 and 578 input SHA256 values and
the original weighted-export SHA256 agree exactly before and after execution,
and match the newly added public validation fields. The two literal hashes
also match the Python software record. Independently hashing the preserved
weighted export gives the same recorded digest.

All 33 published private-configuration entries match their fetched inventory
and the corresponding file bytes read directly from the eleven pinned Git
revisions. The revisions agree with the tracked Lake manifest. The two failed
setup attempts are distinguished from the successful run and do not masquerade
as proof failures or successful compilations. Private-cache repair is described
without changing the claimed tracked dependency pins.

The 474-entry preservation inventory matches current bytes. Both relative
artifact inventories also verify against their documented record-directory
bases: thirteen standalone artifacts and thirty-five exploration artifacts.
The earlier module-list/artifact-list metadata ambiguity remains resolved:
the standalone aggregate names both paths and their distinct digests explicitly.

## Audit, exports, and documentation

The package umbrella imports `Distance566WeightedPauli`. The main audit has
300 distinct guarded targets. Comparing its expected-message blocks against
HEAD preserves all 270 earlier blocks exactly; the additional target set is
exactly the focused audit's thirty targets, with identical expected messages.
The focused audit contains nine finite controls. Each of the twelve public
audit entries has the correct current source digest and guarded/unique-target
count. The focused expected axiom sets contain only the stated standard axioms.

The root documents, Lean guide, standalone README, and integration README agree
on complete eighteen-coordinate coverage, unconditional sector lower bounds
of six, the existing nontrivial X witness of weight twenty, and the overall
Pauli bounds `6 <= d <= 20`. The exported Pauli capstones use the actual
`Removal566.Stage12.code` and the existing QECLean bridge. They introduce no
source-distance-twenty premise. Exact distance twenty remains open and the
submitted exact-distance inventory remains nineteen. Earlier bound-three
results and conditional transport bounds retain their historical scope.

The default locked environment's 114 passes and one optional SciPy skip remain
separate from the isolated exploration environment's 22 passing cases. Byte
regeneration and numerical search outcomes are distinguished from Lean proofs.
The next pricing experiment and the restricted-list counterexamples are not
presented as a global packing obstruction. All visible fresh-audit timings now
use 32.37 seconds consistently.

## Reviewed snapshot

SHA256 values below identify the reviewed bytes. Mutable results and narratives
are deliberately outside the replay source manifest.

| Integration file | SHA256 |
| --- | --- |
| `integration-validation.json` | `e442feb02bcdd77c0c7182e4c23c4af6503aba45d3b357aa4b1f52797bcc1f7e` |
| `job-results.json` | `0c39defa712cbb6b514c8247a6024cd50873b8c91366bb984e12501679b4d184` |
| `commands.json` | `f38be172b327e19c037f15618d8a37f3e8088b6af577af8b03189bc2b3d0c8bf` |
| `results.log` | `72d52a67e1b84d395f55bed0c3bf3dccf679c2bac60f8b039402c3a6fab8438a` |
| `pinned-configuration.json` | `3553cc54da553ea3a29b8f975fcfe49a8c89477b86fdc5c38ff2a0c9498e4fd0` |
| `README.md` | `e501adf5ce4006ff5637a19990866fec6a71a864bffd73434077ff62cdd2c57f` |
| `replay.sh` | `0d9f4f183a33d41ebfd48839889cb178393503de08c1da92b0f3e82c7c827a31` |
| `source-sha256.txt` | `fc6ce9a8cd4fd0d428566760b15f27b053c68209508983837e0ccefdc8503d9f` |
| `preserved-sha256.txt` | `9b4c3b182ebe27d24387f8d858cd146c5de8d15130d1e047b21b883c8d40dbfc` |

| Documentation path, relative to repository root | SHA256 |
| --- | --- |
| `README.md` | `7dd281c8f8f551b8eaf1b87a48e3fb9e4bf178628c6a6b9bdd2d72dd726e9ec1` |
| `RECOMMENDATIONS.md` | `0c3abb337c31ad9e231af9f3c01f7284ab72fb56e60a332e0406df3a0b63f611` |
| `CHECKS_AND_RESULTS.md` | `54a7586b4fe8d37c2668c3c627e3f459eb49e894025e99a7e890f205d906361a` |
| `CERTIFICATES.md` | `aa923c29e3afcf79f6a0ee9dc0270c74abf36be74dfac4cf40d674017bd3c755` |
| `lean/README.md` | `10fc0c0c145b5c8a9ff0a148574909509991885e38dd184c400c55c0fb052543` |
| `data/distance566-bound6-evaluation/2026-10-30/README.md` | `0f23a122aa9342612a5d8c850693d444f52a9e095478cc6417286ddcfbf57e99` |

## Review limits

Execution conclusions rely on the retained records inspected here, not a new
scheduler query or independent replay. This review does not establish a cold
rebuild of every retained project/dependency artifact. It supplements the
completed standalone mathematical review rather than repeating it. Input
parsing, search, and source-to-JSON association remain outside Lean's trusted
proof; the kernel theorems concern the literal matrices, with hashes and byte
regeneration providing the external association. A final documentation manifest
had not yet been produced at review time; the document hashes above identify
the inspected snapshot.
