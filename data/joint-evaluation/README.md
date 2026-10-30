# Joint-step logical coverage and distance

The bicycle family `GB(1+x^s,1+x^t,m)` now has complete logical coverage when `m>0` and `gcd(s,t,m)=1`.
Neither step needs to be a unit modulo `m`.
Both CSS sides satisfy the lattice lower bound for the original relation `s*u+t*v = 0 mod m`.
A matrix recognition theorem combines that bound with exact-weight logical witnesses to prove exact parameters.
The existing rank and dimension results remain unchanged.

| Construction regression | Both ranks | Encoded dimension | Both exact distances |
| --- | --- | --- | --- |
| `GB(1+x^2,1+x^3,6)` | 5 | 2 | 2 |
| `GB(1+x^6,1+x^10,15)` | 14 | 2 | 3 |
| Degenerate one-vertex, zero-step model | 0 | 2 | 1 |

These examples have parameters `[[12,2,2]]`, `[[30,2,3]]`, and `[[2,2,1]]`.
They are defined directly in Lean through the canonical matrix construction.
They are separate from submitted challenge entries.
The submitted-instance inventory remains nineteen.
Together with the two earlier sixteen-qubit constructions, the project has four exact-distance bicycle construction regressions and one degenerate edge-case regression.

## Logical coordinates

The preceding lattice route follows [Arnault, Gaborit, and Saussay](https://arxiv.org/html/2507.21237v1).
The jointly generating extension uses adapted logical coordinates and the existing linear-algebra coverage theorem.
It does not assert the paper's full classification theorem.

When `g=gcd(s,t)>0`, the factor `g` is invertible modulo `m`.
Write `a=s/g` and `b=t/g`, and choose Bézout coefficients with `a*p+b*q=1`.
The vertex potential uses multiplication by the inverse of `g` modulo `m`.
The adapted coordinates are the period carry and the transverse quantity `q*u-p*v`, reduced modulo two.
The closed walks with displacements `(m*p,m*q)` and `(b,-a)` have coordinate pairs `(1,0)` and `(0,1)`.
Their binary chains and the structural rank bound give complete logical coordinates.
When `s=t=0`, joint coprimality forces `m=1`, and a separate valid basis handles this branch.

`Bicycle/PeriodBasis.lean` constructs the primitive step data, potential, carry, and labels.
`Bicycle/SignedPaths.lean` constructs walks with any signed displacement in the original directions.
`Bicycle/JointCoverage.lean` proves the identity pairing and complete coverage.
It also exposes the certificate for QECLean's homological code and proves that zero-displacement closed walks are boundaries.
The dual permutation transfers the lattice bound to the other CSS side.

The distance proof keeps the original edge directions and L1 norm `|u|+|v|`.
It does not treat a longer path as a single physical edge.
For any nonzero integer solution of `s*u+t*v = 0 mod m`, a certified lower norm bound supplies the distance lower bound.
`Lattice/JointFiniteBound.lean` proves such bounds from finite exclusions.
`Bicycle/JointMatch.lean` transfers ranks and bounds through a qubit equivalence and surjective row maps.
Its parameter theorem also requires exact-weight logical witnesses for the matching upper bounds.

## Regressions and trust boundary

The twelve-qubit example tests jointly generating steps that are both nonunits.
The thirty-qubit example also tests a common integer factor of two and an odd cyclic length.
The one-vertex example tests the zero-gcd branch.
`BicycleJoint12.naive_coordinates_miss` proves that a nontrivial weight-five logical has zero naive carry and vertical-parity coordinates.
The adapted coordinates avoid this dependence.

All generic coverage data are constructed from the family hypotheses.
No per-instance rank or logical-coverage certificate is required.
The concrete examples use kernel evaluation only for finite lattice exclusions, witness syndromes, odd pairings, and weights.
Their normative definitions are the committed Lean source, with no JSON parser or external numerical verdict in the proof.
All twenty-three new guarded capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
They do not depend on `native_decide` or `sorryAx`.

The submitted-input Python emitter retains its unit-first restriction.
The general matrix interface accepts arbitrary proved recognition maps.
Disconnected component decomposition and boundary modifications remain future work.
This milestone supplies the generic two-sided bound and an exact-parameter theorem with explicit arithmetic and upper-witness hypotheses.
It does not prove a closed distance formula for every jointly generating step pair.

## Build and replay

The compiled outputs for six new proof modules and the changed root were cleared before the sequential source rebuild.
Other project outputs and external dependency caches were retained.
The root imports all new examples and their dependencies.
The build and all seven guarded audits pass.
The main audit has 141 unique targets.
The focused audits have 23 joint-step targets, 12 connectivity targets, 39 batch targets, 34 family targets, 12 winding targets, and 9 bicycle targets.
The focused target sets overlap with the main audit.

The detached systemd run took 65.34 seconds.
It enforced a 5 GiB memory cap, a 128 MiB swap cap, one CPU of aggregate bandwidth, one Lean thread, and a 300-second runtime limit.
Maximum child-process RSS was 4,064,732 KiB, including shared mappings.
The journal reports a rounded charged-memory peak of 886.2 MiB and 64.346 seconds of CPU time.
Process RSS and charged cgroup memory have different scopes.
These measurements do not describe a cold dependency build.
No cluster job was submitted.

With the pinned toolchain and dependency cache ready, run the exact worker sequence from the project root in a detached, memory-limited allocation:

```bash
bash data/joint-evaluation/replay.sh
```

`replay.sh` preserves the measured worker script byte for byte.
It imposes no resource limits and does not clear outputs itself.
`build-and-audit.json` preserves the worker result, including its transient script path.
`build-and-audit.log` contains the full output, and `guarded-audits.log` extracts the audit output.
`resource-journal.log` records CPU time and the rounded charged-memory peak.
`proof-source-sha256.txt` identifies all active proof, manifest, and toolchain files.
`evaluation.json` records the exact hypotheses, theorem names, examples, source identities, and measurements.

All fifty-three Python tests pass, as do Ruff and shell syntax checks.
The archived proof retains its original source and audit hashes.
Earlier milestone records retain their historical source identities and measurement scopes.
Published logs replace local paths and the hostname with descriptive placeholders.
Exact raw records remain under ignored `.local/proof-records/joint-evaluation/` storage.
Publication metadata preserves their original digests.
