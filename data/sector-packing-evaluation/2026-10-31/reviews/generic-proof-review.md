# Final independent review of the generic prototype

## Verdict and reviewed scope

Approved for use in a literal-code adapter. No blocking mathematical, control, or replay-record findings remain in the frozen generic prototype. The separate literature review also remains approved. Its two reviewed files retain their recorded hashes.

This review covers the three new Lean modules and the standalone prototype evidence. It does not approve numerical certificates, a literal 566-qubit application, shared root imports, or the main audit. Turing owns the numerical review. The generic theorem alone changes no submitted-code bound.

I independently inspected the proof sources, all finite controls, guarded targets, replay scripts, resource checks, and retained execution receipts. I performed lightweight hash and metadata checks locally. I did not run Lean or tests. Actual kernel execution is the author's detached final-v1 replay, whose current-source identity and records I reviewed.

## Frozen identities

| File, relative to the repository root | SHA-256 |
| --- | --- |
| `lean/QldpcVerification/SectorPacking.lean` | `5d41e0251e24ec404b009ca7cb4a9d57f4927a7fc761cc601364c435b379a253` |
| `lean/QldpcVerification/SectorPackingExamples.lean` | `a0aed82bbb58562264bc6ef7126fa7c97e47c5a000fb34e3d5d41945b05670e2` |
| `lean/QldpcVerification/SectorPackingAudit.lean` | `4ec8a0ab96627d600ee227f0caf1e1ec5464c1a0e836726b88ba2e9db6f330e9` |

The ten-entry [source manifest](../lean-prototype/source-sha256.txt) has SHA-256 `44b940abfb25ee5953ad725cac18ee4145075ab58ab25d011bcb837a94943ac1`. Every entry matches the current local file. The fourteen-entry [artifact manifest](../lean-prototype/artifact-sha256.txt) has SHA-256 `cb4d7cdc58bcf058be990e088d5a0c5af05be8fcde0d98dacc2eadbb3f25402d`. Every entry also matches. The worker-owned changed-file list contains fifteen paths, including the artifact manifest itself.

This report resolves the current-source replay gap recorded in [the preliminary core review](core-preliminary-review.md). That earlier report remains an initial snapshot.

## Mathematical proof

The core retains the reviewed complete-coordinate argument. Both physical vectors belong to the cycle subspace. Equal coordinates put their difference in the boundary subspace. Each detector explicitly annihilates boundaries, so its reference pairing transfers to every representative of the sector.

The weighted theorem applies the existing overlap count to those transferred pairings. Natural weights, per-qubit capacities, and the strict threshold preserve integer rounding. It performs no division and assumes no physical weight property of logical coordinates.

`Certificate.lower_bound` retains every required hypothesis. The coordinate-cover theorem requires every nonzero coordinate vector to hit a good direction or have a residual certificate. The prefix theorem requires every nonzero suffix, including sums. Its good-direction bounds quantify over all relevant physical vectors. The X and Z adapters use the correct opposite-cycle spaces for boundary annihilation.

The generic theorem permits zero weights, which is sound. Positive selected weights remain a numerical-export requirement. A reference vector alone, detector rank alone, or bounds for only suffix generators cannot satisfy the complete theorem hypotheses.

## Examples, controls, and axiom audit

The two-qubit zero-check example uses distinct unit detector classes to certify weight two within sector `11`. It separately proves that the global nontrivial-cycle distance is one. The prefix assembly example exercises the coverage API without claiming a stronger global bound.

The new missing-annihilation example has reference `11`, physical vector `01`, and their difference `10`. Both share the second-bit coordinate. That coordinate's kernel is exactly `{0,10}`. Both unit detectors pair to one with the reference, but the first pairs to one with boundary `10` and to zero with `01`. The latter has physical weight one. This exhibits the failure excluded by the annihilation hypothesis.

All ten finite guards test strict rounding, zero-cap equality, correct physical loads, an invalid load cap, wrong-sector pairing, omitted sum sectors, and the seven-pattern count. The audit contains 25 distinct guarded targets, exactly matching `results.json`. It guards every core theorem and the example results, including both missing-annihilation controls.

The expected dependencies permit only `propext`, `Classical.choice`, and `Quot.sound`, with smaller sets where recorded. The successful audit checks those exact messages. No reviewed source adds an axiom, `sorry`, unsafe declaration, or `native_decide`.

## Replay and preservation evidence

The [results](../lean-prototype/results.json) match the retained execution receipts for exact replay and both source checks. All three receipts report exit status zero. The replay log names each of the three compilations in order and contains no diagnostic failure. Source hashes passed before and after execution.

The exact replay took 130.785 seconds. GNU time recorded maximum process RSS of 2,105,224 KiB. The proof allocation completed in 143 seconds with exit code `0:0`. The record distinguishes this measurement from Slurm's sampled batch RSS.

The resource record and the replay's independent cgroup check agree on one CPU, one Lean thread, an effective 8 GiB memory ceiling, and zero swap. Direct compiler commands pass `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`.

All eleven dependency revisions match the current Lake manifest. The compiler is the pinned Lean 4.30.0-rc2. The three retained fresh `.olean` files match their recorded hashes and byte sizes. Replay uses warm retained imports and dependency artifacts. It is not a cold full-project build or a root integration check.

All 621 entries in the parent's preservation snapshot still match. Earlier proofs, data, archives, and pins remain preserved within that snapshot's scope.

## Literature and continuation

The [literature review](literature-review.md) remains valid for audit hash `1d3a308218f85de10df1c0c84b3bf84bb77e69d4b9c6609cc58b8718fdb70be2` and source-catalog hash `ef8a5893f0bc348b8366ff2d358607ca6825b6abf140b6eb1e1fb9105b2ff012`. No new literature claim or search is part of this final proof review.

After independent numerical approval, proceed to the literal Z adapter. That application must prove the good-prefix ordering, the original threshold-seven family obligations, complete paired coordinates, and all seven residual certificates. A Z-only improvement leaves the overall lower bound at six. Final literal-source replay and shared integration require their own review.
