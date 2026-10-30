# Cyclic component decomposition and a four-qubit logical space

For any positive cyclic length `m`, let `c=gcd(s,t,m)`.
Lean now proves that `GB(1+x^s,1+x^t,m)` splits into `c` identical connected components.
Each component has cyclic length `m/c` and steps `s/c,t/c`.
Both original stabilizer ranks are `m-c`, and the encoded dimension is `2c`.
Complete logical coverage and both distances transfer through the decomposition.

The concrete construction `GB(1+x^4,1+x^6,12)` is two copies of the previously verified `GB(1+x^2,1+x^3,6)`.
It has 24 physical qubits, both ranks 10, four encoded qubits, and both exact distances 2.
`BicycleComponents24.parameters` proves `[[24,4,2]]`.
The example is defined directly in Lean and is separate from submitted challenge entries.
The submitted-instance inventory remains nineteen.

## Decomposition and coverage

`Bicycle/CyclicComponents.lean` constructs the vertex bijection `(r,v) ↦ r+c*v` modulo `c*l`, for positive `c,l`.
The qubit bijection retains each edge's block and component.
For steps `c*a,c*b`, Lean proves that both check matrices become independent blocks of the length-`l` code with steps `a,b`.
The same bijection preserves Hamming weight and logical predicates.

`Components.lean` proves the kernel and row-space descriptions of a block matrix.
It also constructs a coverage certificate for `c` copies of any certificate with `k` logical coordinates.
The new certificate has `c*k` coordinates, with component-supported detectors and witnesses.
Its proof uses an identity pairing and a product dimension bound.
It does not enumerate nonzero logical classes.
`CoverageTransport.lean` transports the certificate through a qubit equivalence.

`Bicycle/ComponentBounds.lean` applies these results to the cyclic decomposition.
Connected components have ranks `l-1`, so both global ranks are `c*(l-1)` and the encoded dimension is `2c`.
Complete coverage is also exposed for QECLean's homological code in this factorized model.
Both lattice lower bounds transfer from the component with the original edge weights preserved.

`Bicycle/GcdComponents.lean` takes `c=gcd(s,t,m)` and proves that the reduced steps jointly generate modulo `m/c`.
It proves both ranks `m-c`, encoded dimension `2c`, and a complete coverage certificate for every positive `m`.
The factorization is valid for zero steps as well.
When both steps are zero, `c=m` and each component has one vertex.

## Exact distance and the concrete target

`ComponentDistance.lean` proves exact distance equivalence for a nonempty product of identical components.
A nontrivial global logical has a nontrivial restriction to at least one component.
The weight of a restriction is at most the global weight.
A component logical extends by zero with its weight unchanged.
These facts establish equality of the global and component distances.
The nonempty-component hypothesis is explicit.

`Bicycle/ComponentParameters.lean` transfers this equivalence to both CSS distances of recognized matrix pairs.
Its general parameter theorem also accepts a component lattice bound and matching global upper witnesses.
The exact-distance equivalence itself requires no numerical search or fresh witness enumeration.

`BicycleComponents24.lean` proves both block-matrix identities and reuses both exact distances from `BicycleJoint12.parameters`.
It supplies four complete logical coordinates and proves that a particular nontrivial logical is detected.
Lean also proves that global block parity misses this logical.
The example checks exact recovery of the earlier code in the single-component case.
A separate zero-step structural regression checks the component count, zero stabilizer rank, and full encoded dimension.

An independent Python calculation compared every global check row with its component image.
It also enumerated both 14-dimensional binary kernels modulo the stabilizer spaces.
The result confirms ranks 10 and 10, encoded dimension 4, and both exact distances 2.
`independent-check.json` records this numerical cross-check.
It is outside the trusted Lean proof.

## Build and trust boundary

The compiled outputs for eight new proof modules and the changed root were cleared before the sequential source rebuild.
Other project outputs and dependency caches were retained.
The build and all eight guarded audits pass.
The main audit has 181 unique targets, including forty new component targets.
The focused audits overlap with the main audit.
Every new guarded result uses only a subset of `propext`, `Classical.choice`, and `Quot.sound`.
No capstone depends on `native_decide` or `sorryAx`.

The detached systemd run took 76.34 seconds.
It enforced a 5 GiB memory cap, a 128 MiB swap cap, one CPU of aggregate bandwidth, one Lean thread, and a 300-second runtime limit.
Maximum child-process RSS was 3,895,816 KiB, including shared mappings.
The journal reports a rounded charged-memory peak of 697.6 MiB and 75.510 seconds of CPU time.
Process RSS and charged cgroup memory have different scopes.
These measurements do not describe a cold dependency build.
No cluster job was submitted.

With the pinned toolchain and dependency cache ready, run the measured worker sequence from the project root in a detached, memory-limited allocation:

```bash
bash data/components-evaluation/replay.sh
```

`replay.sh` preserves the measured worker script byte for byte.
It imposes no resource limits and does not clear outputs itself.
`evaluation.json` records proof hypotheses, theorem names, source identities, exact commands, and measurements.
The build result, full log, extracted audit output, resource journal, and source hashes retain separate identities.
All fifty-three Python tests pass, as do Ruff and shell syntax checks.
The archived proof retains its original source and audit hashes.
Earlier records retain their historical source identities and measurement scopes.

The current Python input emitter still requires a unit first difference.
The general matrix interface accepts any proved qubit and surjective row maps.
Boundary modifications and recognition of further submitted layouts remain future work.
Published logs replace local paths and the hostname with descriptive placeholders.
Exact raw records remain under ignored `.local/proof-records/components-evaluation/` storage.
Publication metadata preserves their original digests.
