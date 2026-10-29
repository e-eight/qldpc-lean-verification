# Archived Lean reference

`QldpcCert/` contains the independent Lean 4.36 packing proof for the submitted `225-1-15` code.
Its proof sources, manifest, and toolchain file retain their recorded hashes.
Its README and Slurm entry point use the new archive path.

The archive is outside the active package's imports and default build.
New development belongs in [`../lean/`](../lean/README.md), which depends directly on QECLean.
The earlier proof records remain in [`../data/kernel-evaluation/`](../data/kernel-evaluation/).

Earlier commands and logs refer to the package as `lean/QldpcCert`.
Its current location is `archive/QldpcCert`.
The namespace `QldpcCert` and the theorem `Surface225.distance` remain unchanged.
