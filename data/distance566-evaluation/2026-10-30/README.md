# Distance completion pilot for the literal 566 matrices

This record separates kernel proofs from numerical search.
The distance-twenty completion remains open.
The pinned challenge revision is `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.
The input hashes match the earlier [removal certificate](../../removal566-evaluation/).
No regenerated geometry replaces either submitted matrix.

## Kernel scope

`Distance566.lean` constructs paired X/Z logical coordinates for all eighteen encoded qubits.
Both `CoverageCertificate` values identify zero coordinates with stabilizers and detect every nontrivial logical class.
`X_upper_witness` proves that the first X coordinate is a nontrivial logical of weight twenty.
The generator places the submitted X witness first.
The finite checks establish its syndrome, weight, and pairing with an opposite cycle.

`Distance566Certificates.lean` proves soundness of packed row-combination checks.
It uses QECLean's `F2Mask` support and explicit finite row indices.
Each accepted representative differs from its base by actual stabilizer rows.
The packing modules combine these memberships with capacities and strict integer thresholds.
The guarded audit covers the resulting dependency closures.

`Distance566.partial_bounds` proves unconditional `d_X >= 3` and `d_Z >= 3` for the target.
`Distance566.pauli_lower` applies the bound to every nontrivial Pauli logical through QECLean's CSS bridge.
`Distance566.pauli_upper_witness` supplies a nontrivial Pauli of weight twenty.
Thus the kernel-proved overall bounds are `3 <= d <= 20`.
There is no source lower bound of twenty and no unconditional target bound of fourteen.
No exact distance for the 566 code is established.

## Numerical experiments

The complete packing pilot samples thirty-two representatives for each of eighteen coordinates, on both sides of both endpoints.
An independent sparse-set validator checks all seventy-two families, row combinations, syndromes, coordinates, and integer capacities.
Every sector has complete coordinate coverage.
Individual family bounds are three or four, with a minimum of three in each sector.
None satisfies `19 * cap < totalWeight`.
These restricted families do not establish impossibility of better packing certificates.
The compact export retains explicit row witnesses and equal natural weights.

The information-set pilot finds low-weight classes spanning all eighteen coordinates in each endpoint and sector.
These candidates are numerical upper witnesses only.
The complete weight-at-most-three census finds 54 X cycles and 35 Z cycles for the target.
Every listed cycle is numerically a stabilizer.
Thus a classical kernel-distance argument cannot directly give the quantum distance bound.

At sampled cuts, interleaving the two qubit blocks gives trellis state dimensions up to 45 and 63.
The literal ordering gives larger dimensions.
These measurements concern two orders and do not exclude better orders or searches that prune by weight.
No SAT or UNSAT solver result is trusted or used in a proof.

## Reproduction and resources

Run computation and all Lean commands inside detached, bounded Slurm allocations.
Use the pinned Lean, Mathlib, and QECLean revisions from `lean/`.
Use one Lean thread and the private cluster configuration described in `scripts/cluster/README.md`.
The recorded jobs use one CPU and an 8 GiB memory limit.
Their wall limits range from five to twenty minutes.
The final configuration inspection reports an 8 GiB cgroup memory limit and a zero swap limit.
Operational identifiers, connection details, workspace paths, and raw logs remain under ignored local storage.

All fifteen new Lean modules pass, including fourteen guarded dependency checks and two finite controls.
The coding-theory capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
The two literal input range gates use no axioms.
All 81 Python tests, Ruff, shell syntax, and byte regeneration of the ten generated modules pass.
The peak measured process RSS in the final module replay is 6,225,880 KiB.
This replay uses retained project artifacts and pinned dependency caches.
It is not a cold full-project build.
The sanitized scheduler and module records retain their distinct measurement scopes.
Development failures concern Python style preflight, proof elaboration, or blocked kernel reduction.
No job exhausts its memory or wall limit.
The parser, generators, numerical rank calculations, and searches remain outside the Lean kernel.

With the pinned challenge checkout available as `QLDPC_REPO`, run these commands inside an allocation:

```bash
uv run --locked python scripts/distance566.py coordinates \
  --upstream "$QLDPC_REPO" --out RUN/coordinates --lean-root lean/QldpcVerification
uv run --locked python scripts/distance566.py packing \
  --upstream "$QLDPC_REPO" --out RUN/packing --samples 32 --seconds 650 --seed 56620
uv run --locked python scripts/distance566_packproof.py \
  --upstream "$QLDPC_REPO" --packing data/distance566-evaluation/2026-10-30/packing.json.gz \
  --out RUN/compact.json --lean-root lean/QldpcVerification
uv run --locked python scripts/distance566_ris.py \
  --upstream "$QLDPC_REPO" --out RUN/information-sets.json --trials 64 --seconds 90
uv run --locked python scripts/distance566.py structure \
  --upstream "$QLDPC_REPO" --out RUN/structure
bash data/distance566-evaluation/2026-10-30/replay.sh
```

`RUN` denotes a new output directory that you create for the experiment.
The Lean replay requires the baseline project and pinned dependencies already built.
The proof-module list contains only this task's additions.
Do not run numerical searches or Lean replay on a login node.
