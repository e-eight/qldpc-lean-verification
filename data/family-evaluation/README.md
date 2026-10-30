# Normalized bicycle family verification

The normalized family `GB(1+x,1+x^a,m)` now has symbolic logical coverage, ranks, and lattice distance bounds for every positive cyclic length `m` and natural step `a`.
The normalization adapter handles independent monomial offsets and a cyclic unit as the first binomial difference.
The submitted matrices and stored logical witnesses are checked in Lean.
No per-instance rank or coverage certificate is needed for these applications.

| Application | Input | Normalized `(m,a)` | Both ranks | Exact parameters |
| --- | --- | --- | --- | --- |
| `Bicycle362` | Submitted `362-2-19` | `(181,19)` | 180 | `[[362,2,19]]` |
| `Bicycle262Lattice` | Submitted `262-2-15` | `(131,20)` | 130 | `[[262,2,15]]` |
| `Bicycle562Family` | Submitted `562-2-23` | `(281,101)` | 280 | `[[562,2,23]]` |
| `BicycleEven16Family` | Local `gb-8-3.json` | `(8,3)` | 7 | `[[16,2,4]]` |
| `BicycleEvenStep16` | Local `gb-8-2.json` | `(8,2)` | 7 | `[[16,2,3]]` |

The project inventory is six submitted instances and two additional construction regressions.
The 262-qubit lattice result agrees with the earlier independent weighted packing proof.
The even-step-three family application is proved to use exactly the earlier `EvenBicycle16` matrices.
Neither local fixture is claimed to match the challenge's `16-2-4` entry.

## Construction and trust boundary

The mathematical guide is [Arnault, Gaborit, and Saussay, (2,2)-GB Codes: Classification and Comparison with weight-4 Surface Codes](https://arxiv.org/html/2507.21237v1), especially Proposition II.6 and Theorem II.7 with Corollary II.8.
The preceding lattice route follows [Wang and Pryadko, Distance Bounds for Generalized Bicycle Codes](https://arxiv.org/html/2203.17216).
Their hypotheses and statements remain distinct from the scope of the formal theorems here.

`Bicycle/Normalized.lean` defines the incidence matrix and square-face matrix symbolically.
A horizontal period loop and a mixed horizontal/vertical loop give an identity pairing with two winding detectors.
Structural incidence rank and the existing linear-algebra coverage theorem prove complete logical coordinates, both ranks `m-1`, and two encoded qubits.
The coverage theorem is also exposed for the QECLean homological code.
The dual side is obtained through an axis swap and vertex inversion.
The distance theorem requires a lower bound on the L1 norm of nonzero integer solutions of `u+a*v = 0 mod m`.
This proof does not require a separate formalization of planar filling.

`Bicycle/Normalization.lean` proves weight-preserving qubit reindexing under monomial shifts and multiplication by a cyclic unit.
`Bicycle.Match` accepts submitted matrices and surjective canonical row labels.
It transfers ranks, logical predicates, and distance bounds.
`Input/BicycleRecognition.lean` turns checked four-point supports into row equalities.
`Input/LogicalWitness.lean` certifies a stored logical by an odd pairing with an opposite cycle.
`Lattice/FiniteBound.lean` turns a finite integer exclusion into the universal lattice lower bound.

The standard-library-only generator `scripts/gen_bicycle_family.py` emits four Lean files per application.
The current emitter requires two cyclic blocks in the stored row order, four distinct positions per check, a unit first difference, and equal X and Z witness weights matching the claimed distance.
Lean independently checks supports, row coverage, witness syndromes, odd pairings, weights, and lattice exclusion.
Python preflight is outside the trusted proof.
Input SHA256 values and byte-for-byte regeneration tests connect committed matrices to their source JSON.
All final results use only `propext`, `Classical.choice`, and `Quot.sound`.
They do not depend on `native_decide` or `sorryAx`.

The mathematical normalized model includes either parity of `m` and `a`.
The submitted-binomial adapter requires the first difference to be invertible modulo `m`.
Connected pairs with neither individual difference a unit, disconnected components, and open-boundary modifications remain future work.
The current interface does not claim the paper's full classification theorem.

## Review and regressions

A subagent reviewed the preceding commit `de930ad92c5ee2a4246f91db577a336b74afccd7` and found no substantive mistake.
The reviewer warned that naive dual carry and vertical-parity coordinates can become dependent for even steps.
`Bicycle.Regressions.even_step_old_coordinates_fail` proves this failure on a nontrivial weight-three X logical in the even-step fixture.
The family proof uses the proved axis swap instead.
`Bicycle.Regressions.previous_even_code_eq` proves exact equality with the earlier even-step-three example's CSS matrices.

## Build and replay

All twenty-eight changed or new build targets had their compiled module outputs cleared before the sequential source rebuild.
This includes the package root, which imports all applications and regressions.
Other project outputs and dependency caches were retained.
The build and all four guarded audits pass: 67 main targets, 34 family targets, 12 winding targets, and 9 bicycle targets.
These counts overlap across audit files; the main audit has 67 unique targets.
The retained `Arithmetic562.shortest_vector_witness` guard requires no axioms.

The detached systemd run took 224.21 seconds.
It enforced a 5 GiB memory cap, a 128 MiB swap cap, one CPU of aggregate bandwidth, one Lean thread, and a 600-second runtime limit.
Maximum child-process RSS was 4,970,568 KiB, including shared mappings.
The journal reports a rounded charged-memory peak of 1.8 GiB and 221.292 seconds of CPU time.
Process RSS and charged cgroup memory have different scopes.
These measurements do not describe a cold dependency build.
No cluster job was submitted.

With the pinned toolchain and dependency cache ready, run this exact target sequence from the project root in a detached, memory-limited allocation:

```bash
bash data/family-evaluation/replay.sh
```

`replay.sh` preserves the measured worker script byte for byte.
It does not clear outputs or impose resource limits itself.
The measured run used the deleted-output target list and limits recorded in `evaluation.json`.
`build-and-audit.json` preserves the worker result, including its transient script path.
`build-and-audit.log` contains the full output; `guarded-audits.log` extracts the audit output.
`resource-journal.log` records the service's CPU time and rounded charged-memory peak.
`proof-source-sha256.txt` identifies the active proof, manifest, and toolchain files.
`evaluation.json` records exact inputs, source hashes, dependency pins, scope, and validation.

All 40 Python tests pass, including regeneration of the twenty emitted Lean files and rejection of malformed or unattainable claims.
Ruff and shell syntax checks pass.
The archived Lean proof retains its original source and audit hashes.
Earlier milestone records retain their historical measurement and source identities.

Published logs replace local paths and the hostname with descriptive placeholders.
Exact raw records remain under ignored `.local/proof-records/family-evaluation/` storage.
Publication metadata preserves their original digests.
