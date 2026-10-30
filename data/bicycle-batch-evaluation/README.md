# Bicycle batch and joint connectivity

These records describe the submitted-instance batch and structural connectivity milestone before complete joint-step logical coverage.
The later coverage and distance results are recorded in [`../joint-evaluation/`](../joint-evaluation/).
The source identities and measurements below retain their original scope.

The existing normalized family theorem verifies thirteen additional submitted inputs.
Each proof gives both exact stabilizer ranks, two encoded qubits, and both exact distances.
Together with the three earlier bicycle applications and three surface proofs, the project verifies nineteen submitted instances.
The two earlier exact-distance construction regressions remain separate from the submitted inventory.

| Submitted input | Normalized `(m,a)` | Both ranks | Both distances |
| --- | --- | --- | --- |
| `4-2-2` | `(2,1)` | 1 | 2 |
| `58-2-7` | `(29,8)` | 28 | 7 |
| `82-2-9` | `(41,9)` | 40 | 9 |
| `100-2-10` | `(50,9)` | 49 | 10 |
| `110-2-10` | `(55,10)` | 54 | 10 |
| `122-2-11` | `(61,11)` | 60 | 11 |
| `170-2-13` | `(85,13)` | 84 | 13 |
| `226-2-15` | `(113,15)` | 112 | 15 |
| `278-2-16` | `(139,30)` | 138 | 16 |
| `298-2-17` | `(149,34)` | 148 | 17 |
| `346-2-18` | `(173,51)` | 172 | 18 |
| `422-2-20` | `(211,20)` | 210 | 20 |
| `454-2-21` | `(227,61)` | 226 | 21 |

The local scan found sixteen entries matching the current cyclic two-block row convention.
All sixteen have a unit first binomial difference and now have family proofs.
This scan does not classify other row orderings or every possible bicycle representation.
All thirteen additional source JSON files match the challenge revision pinned in the Python CI workflow.
`instances.json` records their input hashes, normalization data, parameters, and theorem names.

## Proof scope

The generator and the family theorem are unchanged from the preceding milestone.
Each application has four generated modules for matrix data, sparse row recognition, finite lattice separation, and the final parameters.
Ranks and complete logical coverage follow symbolically from the shared theorem.
Lean checks original matrix supports, row coverage, stored witness syndromes, odd pairings, weights, and lattice separation.
No numerical rank certificate or per-instance coverage certificate is needed.
The JSON parser is outside the trusted proof.
Regeneration tests reproduce all generated files byte for byte.

`Lattice/Connectivity.lean` proves that connected binary incidence matrices have rank exactly the vertex count minus one.
It also proves that two cyclic steps jointly connect every vertex when `gcd(s,t,m)=1`.
The proof uses integer coefficients whose combination of the steps is one modulo `m`.
A function invariant under both steps is therefore constant.

`Bicycle/Connected.lean` defines `GB(1+x^s,1+x^t,m)` without requiring either step to be a unit.
Its square faces prove commutation.
Connectivity and the dual permutation prove both ranks `m-1` and two encoded qubits.
The corresponding QECLean homological code has first homology of dimension two.
The model recovers the existing normalized matrices when `s=1`.
At cyclic length 6, steps 2 and 3 test the case where both steps are nonunits.
Steps 2 and 4 admit a nonconstant invariant function, which tests the connectivity hypothesis.

The broader connectivity result currently proves structure, ranks, and dimension.
It does not yet supply complete winding coordinates or a distance theorem for jointly generating nonunit pairs.
The submitted-input emitter still requires a unit first difference.
The next mathematical step is logical coverage and distance for the broader connected model.
Disconnected component decomposition and boundary modifications remain later work.

## Build and replay

The instance batch built fifty-two new modules and the changed package root sequentially, with earlier family and dependency caches retained.
It then passed five guarded audits, including 106 unique main targets and 39 focused batch targets.
The run took 358.46 seconds under a 5 GiB memory cap and a 128 MiB swap cap.
Maximum child-process RSS was 4,722,368 KiB.
The journal reports a rounded charged-memory peak of 1.6 GiB and 352.969 seconds of CPU time.
The later connectivity replay rebuilds its two new source modules and the changed root, then runs all six audits.
That replay passed in 37.69 seconds with maximum child-process RSS of 3,832,408 KiB.
Its journal reports a rounded charged-memory peak of 632.6 MiB and 37.477 seconds of CPU time.
The final main audit has 118 unique targets.
The focused audits have 39 batch targets, 12 connectivity targets, 34 family targets, 12 winding targets, and 9 bicycle targets.
The focused target sets overlap with the main audit.
Exact measurements and guard lists are in `evaluation.json`.
All capstones use only Lean's standard axioms.

Both runs use detached systemd services with one CPU of aggregate bandwidth and one Lean thread.
The record distinguishes maximum child-process RSS from the journal's rounded charged cgroup memory peak.
Other project outputs and dependency caches remain warm.
These measurements do not describe a cold dependency build.
No cluster job was submitted.

With the pinned toolchain and dependency cache ready, run the following command from the project root in a detached, memory-limited allocation:

```bash
bash data/bicycle-batch-evaluation/replay.sh
```

The replay script imposes no resource limits itself and does not clear compiled outputs.
It lists the batch, connectivity, root, and audit targets in sequential order.
`batch-replay.sh` preserves the first measured worker script byte for byte.
`connectivity-replay.sh` preserves the final measured worker script byte for byte.
The two snapshots under `batch-snapshot/` preserve the root and main audit before connectivity integration.
All other batch-phase proof files are unchanged in the final tree.
`batch-proof-source-sha256.txt` identifies that phase, and `proof-source-sha256.txt` identifies the final active sources.
The result JSON, build output, extracted audits, and resource journals retain separate identities for each phase.

All fifty-three Python tests pass, including regeneration of seventy-two Lean files for eighteen family applications.
Ruff and shell syntax checks pass.
The archived proof retains its original source and audit hashes.
Earlier milestone records retain their historical source and measurement identities.

Published logs replace local paths and the hostname with descriptive placeholders.
Exact raw records remain under ignored `.local/proof-records/bicycle-batch-evaluation/` storage.
Publication metadata preserves their original digests.
