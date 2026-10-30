# Rounded packing screen, 2026-10-30

This report corrects the necessary screen for certifying both reported CSS distance targets.
It retains integer rounding: `(D_X-1)*D_Z < n` and `(D_Z-1)*D_X < n`.
Passing supplies neither a certificate nor a proof of either reported distance.
Exclusion concerns this packing method at that target pair, not all possible lower bounds.

## Input and scope

The input snapshot is [upstream qldpc-challenge revision `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`](https://github.com/unitaryfoundation/qldpc-challenge/tree/8c87413d16b78cdd934b7b7a8592cddc81ae6eed), with a clean source working tree.
The scan reads 2,814 code documents.
It skips 202 unsupported non-CSS entries and 1,122 CSS entries with existing exact certificates.
Among 1,490 uncertified CSS target pairs, 697 pass both necessary conditions and 793 fail at least one.
These are arithmetic classifications, not new Lean results or independent distance checks.

`candidates.csv` includes every screened pair and the separate X and Z results.
The product ratio is diagnostic only, with no ratio cutoff.
`summary.json` records the script hash, input revision, counts, and output hashes.
`input-sha256.txt` identifies every code and certificate JSON input.

## Historical comparison

`historical-comparison.json` re-evaluates the numbers in the preserved `../packing_candidates.csv`.
That earlier file has 407 rows, with 365 in the old ratio-at-most-one group and 42 labelled near misses.
Seven of those 42 satisfy both rounded conditions; the other 35 fail at least one.
Passing still does not establish that a suitable family exists.
This comparison does not read the historical matrices or replace the earlier dataset.
Its snapshot and counts differ from the new full scan above.

## Reproduction

Set `QLDPC_REPO` to a checkout of the recorded challenge revision.
Use a separate output directory to preserve this report:

```bash
uv run --locked python scripts/candidates.py --output-dir /tmp/qldpc-candidate-screening
```

Compare `candidates.csv` and `input-sha256.txt` with the saved files.
The generation timestamp in `summary.json` changes on each run.
The script's default output directory is `data/candidate-screening/`.
It never writes the historical `data/packing_candidates.csv`.
