# Mixed-class finite certificate helper

Status: kernel replay passed, including thirteen guarded axiom targets and twelve
finite controls. This helper supports the literal Z-sector adapter but makes no
target-code distance claim. Its API is frozen for independent review.

`SectorPackingCertificates.RawMixedRep` stores a raw base index and one old
weighted row-witness entry. `MixedRep b m` replaces the base and row indices by
finite indices. `mixedRangeCheck n b m` checks all indices and physical mask
bounds before decoding; the no-wrap lemmas preserve their literal meanings.

`mixedClassCheck` checks each representative against its own base using the
existing packed row checker. Its soundness theorem uses the existing checked
row-mask table to prove membership in the span of the actual matrix rows.
`mixedPairCheck` checks reference pairings with the selected base supports.
Transferring these pairings to representatives requires a separate proof that
the reference annihilates the row space. No per-representative full kernel check
is required.

`patternCheck` checks a reference against all ordered detector supports and a
natural bit mask. `pattern_of_check` identifies every resulting coordinate,
including zero coordinates. The literal adapter will separately check support/
mask equality, reference cycle membership, weight capacities, strict thresholds,
and exhaustive residual coverage.

## Exact API

All declarations are under `QldpcVerification.SectorPackingCertificates`.

| Declaration | Contract |
| --- | --- |
| `RawMixedRep`, `MixedRep b m`, `decodeMixed` | Raw and finite base/row indices, preserving masks and weights |
| `mixedFamily`, `entryAt`, `mixedFamily_get`, `entryAt_mem` | Link the projected mask/weight list to each complete entry |
| `mixedRangeCheck`, `mixedRangeCheck_append` | Physical mask, base-index, and row-index range gates |
| `rawRep_range_of_mixedRangeCheck` | Reuse the old per-entry range gate |
| `decodeMixed_base_no_wrap`, `decodeMixed_row_no_wrap` | Literal raw indices survive decoding |
| `mixed_mask_bound_of_rangeCheck` | Every representative mask is below `2^n` |
| `mixedClassCheck`, `mixedClassCheck_append`, `mixedClassCheck_map_sound` | Own-base differences lie in the span of actual rows |
| `mixedPairCheck`, `mixedPairCheck_append`, `mixedPairCheck_parity`, `mixedPairCheck_sound` | Reference pairs to one with each selected base support |
| `patternCheck`, `pattern_of_check` | Every ordered detector pairing equals the expected bit |

## Replay envelope

All Lean checks run in detached one-CPU allocations with an enforced 8 GiB
memory ceiling and zero swap. The pinned compiler receives
`-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`. A fresh output tree
reads approved retained project and pinned dependency artifacts; the approved
prototype sources and artifacts remain unchanged.

The exact public replay took 86.99 seconds with GNU time maximum process RSS
2,071,704 KiB. All ten source entries matched before and after compilation.
All eleven pinned dependency revisions matched. Guarded declarations depend only
on subsets of `propext`, `Classical.choice`, and `Quot.sound`.

The [source manifest](source-sha256.txt), [results](results.json),
[resources](resources.json), [dependency identities](dependencies.json),
[fresh artifact hashes](artifacts.json), and [terminal allocation](allocations.json)
record the validated scope. The source SHA256 for `SectorPackingCertificates.lean`
is `3a9058f9b36cd241dca71f60dd501e1b969b97a98e0b9f8b09a74beea53ea9ac`.

With matching pinned compiler and retained imports available through `PATH` and
`LEAN_PATH`, run the [portable replay](replay.sh) in the bounded allocation:

```bash
bash data/sector-packing-evaluation/2026-10-31/literal-z/helper/replay.sh
```

The public [HelperAudit.lean](HelperAudit.lean) contains every guard and control.
The replay refuses linked output artifacts and reuses the approved prototype's
cgroup/affinity verifier. These are warm-cache checks, not a cold project build.
No literal generator, target input, or target capstone was run in this helper
evaluation. Historical prototype evidence is unchanged.
