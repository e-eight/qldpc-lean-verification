# Independent review of the finite helper

## Verdict and scope

Approved for use by the literal adapter. No blocking mathematical, control, or replay-record findings remain in the frozen finite helper.

This review covers `SectorPackingCertificates.lean`, the standalone `HelperAudit.lean`, their retained dependencies, and the public helper evidence. It excludes the numerical producer and validator, the formatted exporter, generated target inputs, and the handwritten literal capstone. Turing owns the numerical and exporter/data reviews.

I inspected sources and execution records and performed lightweight hash and metadata checks locally. I did not run Lean or tests. Actual kernel execution is the author's detached final-helper-v2 replay, with matching frozen sources and reviewed receipts.

## Frozen identities

The helper SHA-256 is `3a9058f9b36cd241dca71f60dd501e1b969b97a98e0b9f8b09a74beea53ea9ac`. The standalone audit SHA-256 is `9851c054f278355e2f0d4e9677d5eee049eacca86d99d2e2a1f63c00b78635b6`.

All ten entries in the [source manifest](../literal-z/helper/source-sha256.txt) match current files. Its SHA-256 is `6d120f0b4a4d048bdfdac0aaf9163ad0995d13a27004b151de213f330b8f7787`. All eleven [artifact-manifest](../literal-z/helper/artifact-sha256.txt) entries also match. That manifest's SHA-256 is `113d1c7c9fd3fe372ccc7ef8a19131613ad8d81fd348e2ed72350b28d8e12c35`.

## Mathematical checks

The raw and finite entry types preserve the base index, representative mask, original-row witness, and natural weight. `entryAt` links each projected mask/weight entry to its full original entry without changing order. Repeated supports remain valid multiplicities.

The range check covers every representative mask, base index, and row index. The no-wrap lemmas explicitly require its success and show that finite decoding preserves the raw indices. Nonzero finite index sizes remain explicit decoding hypotheses.

`mixedClassCheck_map_sound` applies the checked row-mask table and the existing packed-class theorem to each entry's own base. Its conclusion is membership in the span of actual matrix rows, rather than merely a vanishing syndrome or matching coordinates.

`mixedPairCheck_sound` proves pairing one with each selected base support. It does not claim pairing with the representative. The comments and README correctly retain reference annihilation of the row span as a separate transfer obligation.

`pattern_of_check` establishes every ordered coordinate pairing, including zero bits. Its index starts at zero and follows the supplied support list. It neither changes physical coordinates nor claims equality of arbitrary natural-number encodings beyond those checked bits.

No reviewed source introduces an axiom, `sorry`, unsafe declaration, or `native_decide`.

## Controls and replay evidence

The audit has thirteen distinct guarded targets, exactly matching the recorded list. It guards all helper theorems. Successful messages permit only subsets of `propext`, `Classical.choice`, and `Quot.sound`.

The twelve finite controls cover valid decoding, invalid base/row/mask ranges, retained weights, correct and altered row witnesses, correct and incorrect base pairings, and expected patterns with zero bits. Their scope matches the helper's finite predicates.

The [results](../literal-z/helper/results.json) match the retained exact-replay and source pre/post receipts. Each reports exit status zero. Replay took 86.993 seconds with maximum process RSS of 2,071,704 KiB. The allocation completed in 99 seconds with exit code `0:0`. The record distinguishes process RSS from sampled batch RSS.

Resource checks enforce one CPU, one Lean thread, an effective 8 GiB memory ceiling, and zero swap. Direct Lean calls pass `-j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3`. All eleven dependency revisions match the current Lake manifest. The two fresh compiled objects match their recorded hashes and sizes. These are warm-cache standalone checks, not a full project build.

All 621 preservation entries still match. The approved prototype artifact manifest and both reviewed literature hashes also remain unchanged.

## Literal-adapter obligations

The literal proof must connect each base mask to the base support used for pairing. It must prove reference cycle membership and annihilation of the row span before transferring base pairings to representatives. It must also establish detector boundary annihilation, complete logical coordinates, physical capacities, strict thresholds, and exhaustive residual coverage.

`patternCheck` compares only the supplied finite coordinate bits. If natural masks identify sectors, the application must establish their finite encoding and nonzero suffix meanings. High bits alone cannot establish a nonzero logical sector. Reference mask range and the good-prefix ordering remain application obligations.

These are explicit caller obligations, not defects in the helper's stated theorems. The literal capstone requires its own current-source review and kernel replay. The helper alone changes no submitted-code bound.
