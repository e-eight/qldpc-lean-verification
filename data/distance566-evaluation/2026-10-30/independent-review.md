# Independent review of the distance566 additions

## Verdict and scope

No blocking findings. I found no mathematical correctness defect in the
reviewed additions. The proved result is unconditional sector bounds
`d_X >= 3`, `d_Z >= 3`, and a nontrivial X logical of weight twenty.
The Pauli bridge therefore gives `3 <= d <= 20` for the literal target.
None of the new theorems proves distance twenty or hides a source-distance
premise.

I reviewed the working snapshot against baseline
`af010ea15772841ee40c01704974f903a337b379`.
This review covers all fifteen new Lean modules, the four Python scripts,
`tests/test_distance566.py`, the replay script, and the requested evidence.
I read `AGENTS.md` and the existing definitions used by the proof.
The shared umbrella, main audit, and root documentation remain outside this
task's integration scope.

## Literal provenance and preservation

All 25 entries in `proof-source-sha256.txt` match the current files.
All 17 entries in `artifacts-sha256.txt` also match.
The linked removal-proof manifest matches all 202 of its entries.
The only modified tracked file is the parent's `RECOMMENDATIONS.md`.
The additions are untracked at review time. Existing proof sources and
dependency pins are unchanged.

The available challenge checkout is at the recorded revision
`8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.
Both submitted JSON files match the recorded raw SHA256 hashes.
I compared all 274 target X rows and all 274 target Z rows with
`Removal566Data.lean`. Their entries and row order match the submitted JSON.
Every raw physical index is below 566.

`Removal566Data.lean:289` and `:569` use `Fin.ofNat 566`.
The adjacent range gates at `:290` and `:570` establish that this conversion
does not wrap the submitted indices. The focused audit guards both range
gates as axiom-free. `Removal566Comm.lean:14` constructs the actual target
from these matrices and its proved commutation check.
The new proof uses `Removal566.Stage12.code` directly.

I parsed all coordinate masks and supports as literal data. Both eighteen-entry
lists match `coordinates.json`, and each mask encodes its listed support.
All physical indices are in range. The first X support equals the stored
submitted X witness and contains twenty positions.
These comparisons establish the external input association. The JSON parser
and SHA256 calculations are outside Lean, as the documentation states.

## Complete logical coverage

`Distance566.lean:19` checks each X witness against `HZ`.
The Z witnesses at `:22` are checked against `HX`, with an explicit bridge
between each packed mask and its support indicator.
The pairing check at `:27` proves the entire eighteen-by-eighteen identity
matrix, not only diagonal pairings.

The certificates at `Distance566.lean:31` and `:45` have the correct spaces.
Primal boundaries are X stabilizers. Dual boundaries are Z stabilizers.
Opposite cycles make detector coordinates vanish on those boundaries.
The dual pairing reverses the primal pairing with the correct index swap.

The dimension premises come from the existing kernel-proved ranks
`rankX = rankZ = 274` and `566 = 274 + 274 + 18`.
They do not use the numerical rank calculation in the generator.
I inspected the existing matrix-to-homological dimension lemmas and the
`CoverageCertificate` kernel-equality argument.
Paired witnesses give coordinate surjectivity. Rank-nullity then makes the
coordinate kernel exactly the stabilizer space.
Thus `detects_X` at `:62` and `detects_Z` at `:66` cover every nontrivial
logical class, including arbitrary sums of basis classes.

All three coordinate-check blocks contain their expected six indices.
Their aggregators cover indices zero through seventeen exactly once for
X syndrome, Z syndrome, and mask-to-support equality.
The list lengths and the `Fin 18` theorem interfaces agree.
There is no unchecked extrapolation from a smaller example or a basis subset.

## Packed row-combination soundness and packing bounds

`Distance566Certificates.lean:14` proves that decoding natural-number XOR
gives vector addition over `ZMod 2`.
The list version at `:21` follows by induction.
The support-mask theorem at `:43` proves that XOR of distinct singleton bits
decodes to the actual finite-set indicator.
Its insert proof uses the required nonmembership premise.

The checker at `Distance566Certificates.lean:54` tests exact natural-number
equality with the base XOR an explicit list of matrix rows.
Every row index has type `Fin rows.length`.
The soundness proof at `:58` turns each decoded row into a member of the
actual row span and closes the sum under addition.
Repeated row indices are harmless because they cancel in characteristic two.
No syndrome-only test substitutes for stabilizer membership.

The masks use unbounded natural numbers, not fixed-width machine words.
There is no machine-word overflow premise.
Singleton support positions have type `Fin n`.
The general row-check theorem remains sound even if base and representative
masks contain bits above `n`, because its conclusion concerns their decoded
vectors on `Fin n` and exact XOR cancellation.
All current emitted masks are below `2^566` in any case.
All emitted row witnesses are below 274 and match the compact JSON record.

I inspected the list-to-family bridge at
`Distance566Certificates.lean:87` and the existing capacity checker.
The mapped family retains each representative and gives it natural weight one.
The capacity checker covers every physical position and counts duplicate
representatives with their multiplicities.
Its soundness lemma uses the same decoded supports as the packing theorem.

The orientations in `Distance566Packing.lean` are correct.
The X representative family differs from its X base by `HX` rows at `:17`.
The Z family differs from its Z base by `HZ` rows at `:22`.
The X lower bound at `:28` consequently uses Z families modulo dual boundaries.
The Z lower bound at `:41` uses X families modulo primal boundaries.
The required cycle hypotheses come from the logical predicates.

Every packing-check block uses `decide +kernel` for class membership,
capacity, and threshold. The aggregators cover all eighteen coordinates in
both sectors. I checked their declaration sets and orientations, as well as
the complete literal data in the compact export.
All 36 emitted families match `compact-packing.json.gz`.
They contain eleven to thirteen representatives and have capacities five or
six. Each satisfies the natural-number threshold
`(3 - 1) * cap < totalWeight`.
The proof retains the strict inequality and performs no floor division.
The existing overlap theorem converts this threshold into weight at least
three. `partial_bounds` at `Distance566Packing.lean:53` states that result
without a source lower-bound hypothesis.

## Upper witness, Pauli bridge, and trust boundary

`Distance566.lean:71` proves that the first X witness is nontrivial.
Its syndrome vanishes, and it pairs to one with an opposite cycle.
That pairing rules out X-stabilizer membership.
The finite weight check at `:74` counts physical positions in `Fin 566`.
The existential theorem at `:79` supplies the required upper witness.

`Distance566Pauli.lean:11` passes both sector lower bounds through QECLean's
existing `chainWeight_lower_bound_transfers`.
This includes mixed Pauli logicals, rather than only pure X and Z operators.
The upper theorem at `:20` uses the existing nontrivial-chain correspondence
and physical-weight identity for `chainXOperator`.
The lower and upper theorems refer to the same homological stabilizer group.

I inspected all four Python scripts and their tests.
The coordinate generator preserves the stored X witness, constructs paired
quotient bases, and emits data plus separate finite checks.
The compact emitter requires every target coordinate in both sectors and
rechecks the strict threshold after pruning.
The sparse-set validator independently reconstructs row combinations,
syndromes, detector coordinates, and integer loads.
The small tests cover malformed supports, row-index range, nonuniform integer
rounding, incorrect class witnesses, the low-cycle census, and pruning.

The numerical search uses floating-point pricing, but its result enters Lean
only as explicit finite certificate data.
Neither floating-point scores, numerical rank output, nor solver output
discharges a Lean proposition.
No SAT/UNSAT result, parser correctness axiom, custom axiom, `sorry`,
`native_decide`, unsafe declaration, or external proof primitive appears in
the new sources.

The restricted pilot record contains 72 families and records 32 samples for
each coordinate and endpoint-sector pair. Its retained family bounds are
three or four. The documentation correctly avoids an impossibility claim.
The information-set and structural results remain numerical evidence.
They do not imply a stronger kernel lower bound or exact distance twenty.

## Evidence inspected and limitations

All fifteen modules in `proof-modules.txt` have successful results in
`module-results.json`. Its extra entry is the existing `Input.LogicalWitness`
dependency. Each module's recorded wall time, RSS, and zero exit status match
a retained successful compilation log.
The final Pauli log includes successful compilation of both the Pauli module
and the current focused audit.

The audit contains fourteen guarded axiom checks and two finite controls.
The controls accept a correct row combination and reject an incorrect one.
The guards include coverage, both lower bounds, both Pauli capstones, and
row-combination soundness. Their dependency closures include the finite
certificate checks. The permitted coding-theory axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The retained Python log records 81 passing tests, successful Ruff checks,
and `ALL_BYTE_REGENERATION_AND_PYTHON_CHECKS_OK`.
The corresponding job script regenerates and byte-compares all ten generated
modules, checks shell syntax, and runs both sparse-set validations.
The source and artifact hash manifests agree with the reviewed snapshot.

The sanitized scheduler record reports one CPU and an 8 GiB allocation limit.
The private job scripts use bounded detached Slurm allocations and one Lean
thread. The final configuration observation reports zero permitted swap.
The maximum final module RSS is 6,225,880 KiB, as reported.
Failed development records have nonzero proof or preflight exits rather than
OOM or timeout states. The record correctly distinguishes sampled scheduler
RSS from process RSS and identifies the use of retained dependency artifacts.

I did not rerun Lean, pytest, generators, numerical searches, or the sparse-set
validator. My independent execution consisted of file/hash comparisons,
literal-data parsing, range and threshold inspection, and log comparisons.
Successful compilation, regeneration, and axiom-guard execution remain the
implementer's recorded evidence, not a second kernel replay by this reviewer.
No new concern requires a cluster rerun.

The checks are standalone module compilations with retained dependencies.
They are not a cold build or a full-project build after umbrella integration.
The parent still needs to integrate the shared umbrella and main audit and
run the appropriate integrated checks. The JSON-to-Lean input association
also remains an external provenance boundary, supported here by exact raw
hashes and row-by-row literal comparison.

## Optional polish

Low priority, `replay.sh:9`: add a preflight check of the recorded source
hashes before replay. The current instructions require pinned sources, and
the present snapshot matches them. An automated preflight can make a future
replay fail clearly if it uses edited sources or a different manifest.

Low priority, `Distance566Audit.lean:6`: update the introductory comment to
mention the partial lower bounds and Pauli results. Its current text mentions
only coordinates and the upper witness, although its actual guards cover
the expanded scope correctly.

Only this report was written during review. I did not alter implementation,
other evidence, root documentation, shared integration files, dependency
pins, cluster configuration, jobs, or the QECLean PR checkout.
No agents were spawned and no commits, pushes, or external messages occurred.
