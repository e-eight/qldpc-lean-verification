# Weighted packing exploration for the literal 566 matrices

Baseline: `4461ec5e8d711cbb1cf29da5d35d0aebe987f038`.
The existing kernel proof remains `3 <= d <= 20`.
This task explores finite certificates and does not change that proof.
The earlier distance and integration records remain immutable checkpoints.

## Results and proof scope

The focused run produces independently validated finite certificates for threshold six
in both target sectors. No new Lean theorem is claimed. No logical lighter than twenty
was found, including during the final algebraic diagnostics.

| Matrix | Detector side | Bounded side | Classes evaluated | Complete finite threshold | Rank at next threshold |
| --- | --- | --- | ---: | ---: | ---: |
| 566 | Z | X | 64 | 6 | 7 at threshold 7 |
| 566 | X | Z | 64 | 6 | 15 at threshold 7 |
| 578 | Z | X | 40 | 5 | 1 at threshold 6 |
| 578 | X | Z | 40 | 5 | 7 at threshold 6 |

Every complete threshold uses 18 independent logical classes and an exact identity
pairing with separately constructed witnesses. At threshold eight both target ranks
are zero; at threshold twenty all four ranks are zero. These statements describe the
stored families, not the full set of physical representatives.

The first pilot reaches four in all sectors. Reweighting the old pools alone also
reaches four. On the final target lists, the original coordinate classes reach five,
while adaptive spanning sets reach six. The target detector bases are chosen
independently: their paired witnesses may be dense. Low-weight X and Z detector bases
are not forced to be mutually dual.

The control received one quarter of the target time per sector, fewer information-set
trials, and fewer classes. Its weaker result does not establish an effect of qubit removal.

## Construction and independent checks

The search reuses the recorded light candidates and old representatives as a starting
floor, then enriches classes using random information sets. It adds same-class
representatives through stabilizer rows, row pairs, price-biased information sets,
and derived stabilizer bases. The focused variant alternates four physical-weight
penalties with the per-qubit dual prices. It assumes no translation symmetry.

The LP supplies proposals only. Rounded nonnegative integer weights are checked using
the actual maximum per-qubit load `cap` and total weight `totalWeight`. A family
qualifies at threshold `D` precisely when `(D - 1) * cap < totalWeight`. Row witnesses
are recovered from the literal matrices, including after reanchoring to a lighter base.

The separate validator uses sparse sets and integer arithmetic, with no search, NumPy,
or solver imports. It checks literal input hashes, CSS commutation, ranks, all syndromes,
logical coordinates, original-row combinations, capacities, restricted dual feasibility,
class ranks, and all 18-by-18 pairings. It rejects altered rows, classes, weights,
capacities, duals, sector labels, and dependent bases. All 22 focused tests pass;
Ruff checks pass. No Lean run was performed in this task.

## Bottleneck and next experiments

Exact dual certificates exclude threshold twenty for every stored list. Their scope
is limited to those lists. For **all 36 selected target families**, exact elimination
finds another same-class representative of price zero, with an independently checked
stabilizer-row witness. Each is an explicit violation of extending that family's
stored-list dual globally. This supplies a concrete pricing gap, not an impossibility
result or a novelty claim. These diagnostics have weights 32 through 144.

The immediate integration step is to encode and replay the selected threshold-six
certificates through the existing generic Lean coverage and overlap tools. The next
bounded search should shorten the saved zero-price representatives within the affine
space that avoids priced qubits, then add them to the LP and compare smoothed prices.
Prioritize classes that increase the deficient rank at seven. A global lower-bound
argument at twenty remains open; this experiment does not resolve it.

## Reproduction and artifacts

- `pilot-v1/` and `focused-v1/` preserve complete families, exact validation, parameters,
  seeds, rank curves, source hashes, and sanitized source snapshots.
- `analysis-v1/analysis.json` contains the exact pricing counterexamples and row witnesses.
  `lean-ready.json.gz` keeps only 18 selected classes per sector and positive weights:
  1,449 target Z-detector representatives and 1,443 target X-detector representatives.
  Its name describes a data export; it is not a checked Lean module.
- `final-validation-v2/` records the final source and fresh independent validation of
  both runs and the compact export. The earlier validation checkpoint is preserved.
- `commands.json` records commands and staging mappings. `environment/requirements.txt`
  pins the isolated environment with package hashes; the project lockfile is unchanged.
- `exploration-validation.json` summarizes scope and bounds; `job-results.json` gives
  command exit statuses and measured resource scopes. `source-sha256.txt` and
  `artifacts-sha256.txt` identify inputs, sources, and evidence. `changed-files.txt`
  lists every new repository path.

To reproduce, stage the literal upstream inputs and the three baseline files using the
mapping in `commands.json`. Extract the appropriate source snapshot into a fresh task
directory. Install its isolated environment with `uv` and the hash-locked requirements.
Run the recorded commands only in a detached allocation with one CPU, one thread,
8 GiB of memory, zero swap, and the recorded time limit. Always use fresh output paths.
Time budgets can change search output; stored certificates support exact repeat validation.
Source snapshots retain file bytes but normalize archive ownership and timestamps.

The pilot uses seed 566430 and a 180-second soft search budget. The focused run uses
seed 566431 and 720 seconds: 288 per target sector and 72 per control sector, with
small loop-boundary overruns. See `commands.json` for trial, move, and list limits.
Software is Python 3.13.3, NumPy 2.5.4, SciPy 1.16.3 with HiGHS 1.8.0, pytest 9.2.0,
and Ruff 0.16.10. The historical search snapshots used a SciPy option spelling that
raised a warning; one CPU and `threads=1` still applied. The final source fixes that
option and passes tests with warnings treated as errors, without repeating searches.

All five serialized allocations completed with exit zero. The focused allocation took
795 seconds; its scheduler-sampled batch RSS was 175,368 KiB. The timed search process
peaked at 157,488 KiB. These are distinct scopes, not whole-allocation memory peaks.
Observed cgroup limits were 8 GiB and zero swap; final CPU affinity was one CPU.
No allocation remains queued or running. Operational identifiers and raw logs stay ignored.

Literal input SHA256 values:

```text
566 061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be
578 440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514
```

Upstream challenge revision: `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.
