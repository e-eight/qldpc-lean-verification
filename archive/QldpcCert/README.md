# Archived QldpcCert proof

This independent proof remains an archived reference implementation.
New development uses [`../../lean/`](../../lean/README.md) and depends directly on QECLean.
The archive is outside the active package's imports and default build.
The proof sources retain their recorded hashes.
See [`../../RECOMMENDATIONS.md`](../../RECOMMENDATIONS.md) for the current plan.
Mathlib is pinned at
`v4.36.0-rc2` (toolchain `leanprover/lean4:v4.36.0-rc2`) and uses the prebuilt
Mathlib cache.

## Build

    export PATH="$HOME/.elan/bin:$PATH"
    lake build                 # specification and checker library only
    lake build QldpcCert.Surface225  # includes the expensive finite kernel checks
    lake env lean QldpcCert/KernelAudit.lean  # rejects any extra axiom
    lake env lean <file>.lean  # check one file

The default target excludes `Surface225`. A successful default build does not
establish the concrete distance theorem. The kernel build needs the pinned
Lean toolchain and the Mathlib cache.

The Slurm batch script is [`kernel.sbatch`](kernel.sbatch).
It requests four CPUs, 32 GB of memory, and two hours by default.
Submit it with `bash scripts/cluster/submit.sh --archive` from the repository root.
The helper reads private scheduler settings from `.local/cluster.env`.
See [`../../scripts/cluster/README.md`](../../scripts/cluster/README.md) for configuration details.
The pinned Lean installation belongs at `tools/lean/` beneath the submission directory.
The script records source hashes, elapsed time, peak memory, and the final axiom
report. It uses the cluster's certificate bundle for the Mathlib cache download.
When the matching cache is complete, set `QLDPC_FETCH_CACHE=0` to skip its scan.
The successful run used two CPUs and 16 GB through Slurm command-line overrides.

## Files

| File | Role |
|---|---|
| `QldpcCert/Spec.lean` | **The statement to trust.** CSS code over 𝔽₂, nontrivial logicals, `DistX d`, `DistZ d` |
| `QldpcCert/Certificates.lean` | General lemmas, proved once for every code: kernel ⟂ row space, double counting, rank lower bounds from pivot certificates, rank–nullity, the k = 1 packing theorem, and the X↔Z swap |
| `QldpcCert/Bits.lean` | Verified bitmask operations, arithmetic bit tests, weights, and disjointness |
| `QldpcCert/Sparse.lean` | Sparse row decoding, parity counts, commutation, and kernel membership |
| `QldpcCert/SparseRank.lean` | Rank certificates through sparse columns and the original transform matrix |
| `QldpcCert/Surface225Data.lean` | Generated from `codes/225-1-15.json` by `../../scripts/gen_lean_instance.py`: bitmask data and certificates |
| `QldpcCert/Surface225Support.lean` | Generated row supports and supports of the selected pivot columns |
| `QldpcCert/Surface225.lean` | `Surface225.distance : code.DistX 15 ∧ code.DistZ 15` |
| `QldpcCert/KernelAudit.lean` | Fails if the distance theorem uses any extra axiom |

## What `Surface225.distance` rests on

The full kernel build succeeded on the Slurm cluster on 2026-10-28
local time. The instance check took 240.50 seconds and peaked at 4,145,924 KiB
of memory. `#print axioms Surface225.distance` reports:

    [propext, Classical.choice, Quot.sound]

Every finite certificate check uses kernel evaluation. The theorem has no
`native_decide` axiom and no `sorryAx`. The specification and correspondence
between the generated matrices and the source JSON still need review.
Lean also checks that every sparse support equals its original matrix row.

To reproduce the data, run this command from the repository root:

    uv run --locked python scripts/gen_lean_instance.py 225-1-15 Surface225 archive/QldpcCert/QldpcCert/Surface225Data.lean archive/QldpcCert/QldpcCert/Surface225Support.lean

Compare both outputs with the committed files. See `../../CHECKS_AND_RESULTS.md`
section 10 and `../../data/kernel-evaluation/kernel-build.log` for the result.
