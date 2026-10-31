# Independent review of frozen root integration sources

## Verdict and scope

No blocking source-integration findings. The frozen umbrella exports the approved generic helpers and literal Z theorem. The main audit includes all new guarded targets with their accepted dependency expectations.

This is static source and hash review. It does not approve the combined execution or final documentation. Hooke's actual replay and its terminal records remain pending. I ran no Lean commands or tests and did not duplicate the exporter/data review.

## Frozen identities

| File, relative to the repository root | SHA-256 |
| --- | --- |
| `lean/QldpcVerification.lean` | `190312a3a954b1266c7399c19250c253e62d9327d2ee03889cb5528b91677c91` |
| `lean/QldpcVerification/KernelAudit.lean` | `e10b6cbae1d11c7315cc7121e09a4bde3911594803a88e82e10208f863a10e49` |
| `data/sector-packing-evaluation/2026-10-31/integration/replay.sh` | `f4420a29470306f3b95f06857bc3d276edea018c347ae188daa4fd2a0ad752ea` |
| `data/sector-packing-evaluation/2026-10-31/integration/source-sha256.txt` | `0f6bc39cd6f06b3499dd0164a406dcc0076f596fd7a9c4439266c32bb0fb73e5` |

All 428 source-manifest entries match current files, with no duplicate paths. The manifest includes the umbrella, main audit, generic theory/examples/audit, finite helper and standalone audit, all 61 accepted literal modules, and the exact public runner.

## Imports and guard coverage

The umbrella adds only `SectorPackingExamples`, `SectorPackingCertificates`, and `Distance566SectorZ` to its prior imports. These expose the reviewed generic, finite, and literal interfaces.

The main audit has 550 textual entries and 371 distinct targets. It preserves the complete prior audit as a byte prefix. Its 179 historical repeated entries remain unchanged. All twenty-five prototype, thirteen helper, and thirty-three literal targets occur. Their guarded message comments match the corresponding accepted focused audits after whitespace normalization.

The literal source and focused audit retain hashes `33934ca1…d56abd47` and `8dda6918…93a1ae5d`, as fully recorded in the approved [literal proof review](literal-proof-review.md). No extra distance claim follows from their inclusion in the root.

## Runner contract

The runner recompiles the root and executes fourteen project audit sources plus the standalone helper audit. That includes the literal seven controls, generic ten controls, and helper twelve controls in their original executed files. The main guards separately cover all new dependency closures.

Explicit failures enforce the memory, swap, and affinity envelope. The output gate rejects a linked root artifact or linked parent. Source checks run before and after execution. Compiler commands retain `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`.

The [initial static findings](integration-plan-review.md) are resolved at source level. Actual runtime must establish that staging and output ownership satisfy these gates. The run uses warm imports and does not recompile all 61 literal modules. Their separate accepted source/object identities therefore remain part of the evidence chain.

## Remaining acceptance

Review the actual combined receipts, all fifteen audit executions, final resource and dependency records, and source pre/post comparisons when available. Then review the four root documents and Lean README against those results. Retain the distinction between `d_X >= 6`, `d_Z >= 7`, and overall `6 <= d <= 20`. The exact submitted-instance count remains nineteen.
