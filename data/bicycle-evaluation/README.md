# Bicycle lattice proof

The submitted `562-2-23` matrices now have a kernel-checked lattice proof.
`QldpcVerification.Bicycle562.parameters` proves two encoded qubits and `d_X = d_Z = 23`.
The separate `rankX` and `rankZ` theorems prove both stabilizer ranks equal 280.
The full package rebuild and all twenty-two guarded axiom audits pass.
The nine focused bicycle guards also pass.
The coding-theory capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
The closed norm-23 lattice witness uses no axioms.

The proof follows the graph interpretation in [Wang and Pryadko, Section 3.5](https://www.mdpi.com/2073-8994/14/7/1348).
The input binomials have offsets `(158,165)` and `(135,280)` in the cyclic group of order 281.
Lean matches every original X and Z row to its graph-incidence formula.
The two incidence graphs have steps `(7,145)` and `(145,7)`.
Cyclic translation reduces commutation to 281 checked base cases.

`Lattice/IncidenceRank.lean` proves a generic rank lower bound for connected binary incidence matrices.
A vector in the transpose kernel must have equal values at each edge's endpoints.
The cyclic periodicity lemma and `241*7 = 1 mod 281` force that vector to be constant.
Rank-nullity then gives rank at least 280 on each side.
Paired block logicals and the existing coverage theorem prove two logical coordinates and make both ranks exact.
The final input contains no pivot certificates or numerical rank checks.

`Lattice/Trail.lean` extracts a detected closed trail from a finite binary cycle with nonzero edge-label sum.
The proof permits parallel edges and loops and does not enumerate binary chains.
`Lattice/Displacement.lean` lifts that trail to a nonzero integer pair and bounds its L1 norm by the original cycle's weight.
Its cyclic closure gives `7*u + 145*v = 0 mod 281`, with the coordinates swapped on the other CSS side.
`Arithmetic562.norm_ge_23` excludes all nonzero relations with L1 norm at most 22.
A finite exclusion on `[-22,22]^2` supplies the bound for arbitrary integers.
`Arithmetic562.shortest_vector_witness` accepts `(9,-14)` with norm 23.
The original stored X and Z witnesses give the matching upper bounds.

The generic graph bridge assumes nonzero direction parity.
The concrete coverage certificate proves that every nontrivial logical in this instance satisfies that hypothesis.
Other quotients can require different logical coordinates.
This result does not yet give a general code-equivalence or distance-equality theorem for every weight-four bicycle code.
The mathematical statements concern the generated matrices, with input hashes and byte-for-byte regeneration tests connecting them to JSON.
JSON parsing and the Python rank preflight remain outside the formal proof.

The final sequential build and audit took 280.09 seconds with the dependency cache retained.
Detached systemd services enforced `MemoryMax=5G`, `MemorySwapMax=512M`, and one CPU of aggregate bandwidth.
The final service had a 1200-second runtime and CPU limit.
The maximum child-process RSS was 8,331,048 KiB.
RSS includes shared mappings and differs from the cgroup's charged-memory peak.
The resource journal records a 5 GiB charged-memory peak and a 318 MiB swap peak.
These are warm replay measurements, not a cold-build benchmark.

The first combined finite check reached its own cgroup cap and stopped.
Numerical rank evaluation was then replaced by the structural theorem.
The cluster SSH session expired before this milestone, so the result has no independent cluster replay yet.
The final local proof and audit passed under the enforced memory budget.
An address-space limit was unsuitable because Lean maps a large compiled dependency cache.
Use a cgroup limit for bounded local replay.

From the repository root, with the pinned toolchain under `.tools/` and the dependency cache ready, use:

```bash
systemd-run --user --collect --unit=qldpc-bicycle \
  --property=MemoryMax=5G --property=MemorySwapMax=512M \
  --property=CPUQuota=100% --property=Nice=10 \
  --property=RuntimeMaxSec=1200 \
  --property=StandardOutput=append:/tmp/qldpc-bicycle.log \
  --property=StandardError=inherit --working-directory="$PWD" \
  env LEAN_NUM_THREADS=1 \
  PATH="$PWD/.tools/lean-4.30.0-rc2-linux/bin:$PATH" \
  bash -c 'lake -d lean build QldpcVerification.Bicycle562 &&
    lake -d lean env lean lean/QldpcVerification/BicycleAudit.lean'
```

`build-and-audit.json` records the complete sequential build command used for all five instances and both audits.
`build-and-audit.log` preserves its output.
`evaluation.json` records theorem statements, hashes, dependency revisions, resource measurements, and the proof's scope.
The earlier cluster evaluations retain their original measurement scopes and source identities.
This milestone completes the requested bicycle proof.
The next action is the project stocktake with the user.

Published logs are sanitized copies. Descriptive run labels replace scheduler IDs.
Hostnames, login details, accounts, partitions, and workspace paths remain only in the ignored `.local/cluster/records/` directory.
Proof-source hashes, theorem statements, outcomes, and resource measurements are preserved.
The `publication` field in the JSON records identifies this treatment and retains the original log digests.
