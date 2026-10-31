# Packing bounds for logical sectors

## Status and scope

This work starts from checkpoint `e9e33f21946bc781e6ae3c3c04adaac86abb36dd`.
The literal 566-qubit code now has proved sector bounds `d_X >= 6` and `d_Z >= 7`.
The overall bound remains `6 <= d <= 20`; exact distance twenty remains open.
The experiment, generic Lean prototype, and literature audit ran in parallel, followed by the literal Z application.
Earlier proofs, evaluation records, archives, and dependency pins remain unchanged.

The numerical worker owns `numerical/`, two new sector scripts, and their tests.
The Lean worker owns `lean-prototype/` and the three new `SectorPacking` modules.
The literature worker owns `literature/`.
The parent owns this plan, shared integration, root documentation, and final evidence assembly.
Independent review precedes any new literal-code distance claim.

## Reviewed initial outputs and continuation

The generic [Lean prototype](lean-prototype/README.md) passes its three-module replay, twenty-five guarded targets, and ten finite controls.
The exact replay takes 130.79 seconds under the stated resource limits.
It proves sector transfer and exhaustive prefix/suffix assembly, without a new literal 566-qubit claim.

The [Z numerical pilot](numerical/z-v1/summary.json) passes exact validation for all seven residual patterns.
Its residual bounds are eleven, twelve, thirteen, thirteen, thirteen, twelve, and twelve.
The fifteen original good directions still limit the proposed uniform Z conclusion to seven.
The pilot allocation completes in 99 seconds with one CPU, 8 GiB, and zero permitted swap.
The numerical record is separate from a Lean proof.

The [literature audit](literature/audit.md) finds no conceptual blocker and gives the standard relative-distance interpretation.
The [design review](reviews/design-review.md) records the required finite hypotheses.
The numerical, generic proof, literature, and finite-helper reviews approve continuation to the literal Z adapter.
The numerical review requested stronger basis-change and boundary controls.
Those controls pass in the final twenty-eight-test run, with the initial twenty-test sources preserved separately.
The literal exporter and all fifty-nine generated inputs pass their [independent review](reviews/exporter-review.md).
Seventeen focused tests, exact byte regeneration, and the seven-module kernel pilot pass.
The [literal application](literal-z/proof/README.md) passes all fifty-nine generated modules and both handwritten modules, with thirty-three guarded targets and seven controls.
The final proof uses direct membership transport and explicit code arguments to avoid expensive inference through literal matrices.
The [current Python validation](python-validation-v3/README.md) passes 169 tests with two expected optional SciPy skips, Ruff, and exact regeneration of the new and earlier certificates.
Its 347-entry snapshot contains the corrected index-proof template; the successful bounded allocation takes 103 seconds.
The earlier [Python record](python-validation/README.md) and generated pilot remain unchanged historical handoffs.
The [integration record](integration/README.md) tracks final package replay separately.
That combined replay passes root compilation, fourteen project audits, and the standalone helper audit against 428 frozen source hashes.
Its bounded allocation completes in 450 seconds; a further fresh main-audit artifact is also checked.

The X pilot passes all thirty-two sampled patterns but leaves 2,015 patterns unchecked.
A separate [disjointness diagnostic](disjoint-x/README.md) tries seven unit-weight detectors in each sampled sector.
None of its bounded greedy attempts succeeds, so this shortcut is not expanded.
The original fractional certificates remain unchanged.
This result proves no disjoint-packing impossibility.

## Mathematical contract

The original, unpruned families qualifying at seven have reported detector ranks fifteen for the Z bound and seven for the X bound.
The Z application now checks the fifteen good-direction thresholds and every residual sector in Lean.
The X threshold-seven profile remains numerical evidence pending complete coverage and formalization.
Complete logical coordinates have dimension eighteen.
Vectors undetected by the good Z-bound detectors therefore have three remaining coordinates, giving seven nonzero patterns.
The corresponding X problem has eleven remaining coordinates and 2,047 nonzero patterns.

For each residual pattern, choose a physical reference with those logical coordinates.
Every selected detector must pair to one with that reference and annihilate stabilizer boundaries.
Every cycle with the same coordinates then has the same pairing.
The weighted overlap theorem applies even when the selected detectors have different logical classes.
Each certificate must satisfy the exact inequality `6 * cap < totalWeight` to prove a lower bound of seven.
Every nonzero residual pattern needs coverage, including sums of basis patterns.

Adding the fifteen good X detectors as extra X checks gives an equivalent view of the remaining Z problem.
This uses the same physical qubits and leaves three encoded qubits, provided the independence and commutation hypotheses hold.
The literature audit compares this interpretation with prior work on stabilizer extensions.
The prototype does not require constructing those augmented matrices.

## Numerical experiment

First verify the literal input, both paired coordinate bases, all original row witnesses, and the good detector span.
Use the full original focused export, not the compact certificate that preserves only six.
For the Z bound, enumerate all seven residual patterns and record their coordinates in both logical bases.
Check the physical reference pairings directly.

For each pattern, pool compatible representatives across all stored target detector classes.
Deduplicate physical supports while retaining provenance.
Try inexpensive integer proposals and a bounded LP, then recompute capacities and thresholds exactly.
Store shared representatives once and use positive integer weights indexed into that pool.
Solver status and restricted-pool dual bounds remain separate from proof evidence.

The initial Z search budget is approximately 180 seconds inside a twenty-minute allocation.
If necessary, one further bounded enrichment can use the saved pricing counterexamples.
The independent validator must reject missing patterns, dependent bases, wrong sectors, incorrect physical pairings, altered row witnesses, invalid indices, Boolean or fractional weights, and threshold equality.
Preserve any lighter logical witness for separate checking.

If all seven Z certificates pass exact validation, freeze them for review immediately.
Then measure an X pilot with at most 32 deterministic residual patterns and an approximately 180-second search budget.
Review measured runtime, certificate size, and arithmetic margins before expanding to all 2,047 X patterns.
Do not infer a global obstruction from failure on a stored pool.

## Lean prototype and tests

Prove transfer of pairings between cycles with equal complete logical coordinates.
Combine that transfer with the existing weighted overlap theorem.
Prove assembly from known-good detectors and an exhaustive set of residual sectors.
Use a symbolic prefix/suffix decomposition to avoid enumeration of all eighteen logical coordinates.

A two-qubit example will combine different detector classes to prove weight two within one sector.
Its global distance remains one, which prevents mistaking a conditional result for a code-wide bound.
Negative controls must cover a wrong pairing and omission of a nonzero sum sector.
Guard the final theorem dependencies against `sorryAx` and `native_decide`.

## Review gates and continuation

Review the numerical exporter and independent validator separately from the generic Lean proofs.
Compare the literature statements with the exact hypotheses used in the implementation.
Check original-row provenance, logical-coordinate orientation, complete residual coverage, strict arithmetic, and source identities.
Resolve blocking findings before literal-code formalization.

The reviewed Z results led to new target inputs and the literal lower bound through the adapter.
Retain the existing X lower bound of six and weight-twenty upper witness.
A Z improvement alone leaves the overall proved lower bound at six.
Continue the X experiment only after its pilot establishes a practical route to complete coverage and replay.

All substantive generation, tests, searches, and Lean checks use detached cluster allocations.
Initial limits are one CPU, one thread, 8 GiB, zero swap, and fifteen to twenty minutes.
At most two compute allocations run concurrently.
Direct Lean calls explicitly pass the pinned project options.
Operational settings, identifiers, private paths, and raw logs remain under ignored `.local/` storage.
Public records preserve source hashes, commands, mathematical scope, resource measurements, and contained failures.
