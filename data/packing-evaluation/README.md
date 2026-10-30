# Finite coverage and weighted packing evaluation

The evaluation uses Lean 4.30.0-rc2 and the pinned QECLean and Mathlib dependencies in `lean/lake-manifest.json`.
`Bicycle262.parameters` proves two encoded qubits and both exact distances of 15 for the submitted matrices.
The generic coverage theorem uses paired witnesses and a dimension bound for any finite logical dimension.
The current bicycle generator accepts cyclic two-block codes with two encoded qubits.

`bicycle262-checks-cluster.log` records successful cluster run `packing-finite-checks`.
It independently replays `QldpcVerification.Input.Bicycle262Checks`.
It does not contain the final coding-theory capstone or its axiom audit.
The measured build took 13:08.16 and reached 6,212,504 KiB of maximum process RSS.
The whole allocation took 20:07 and Slurm reported 13,074,464 KiB, including dependency provisioning and cache work.
These measurements have different scopes.

The full replay passed as detached cluster run `packing-full-replay`.
Its targets include the original surface code, the bicycle proof, and the additional `529-1-23` and `961-1-31` surface codes.
Its allocation reserves two CPUs and 48 GiB.
The job also passed thirteen guarded axiom checks.
Every guarded theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
Both additional surface parameter theorems prove one encoded qubit and exact X and Z distances of 23 and 31, respectively.
The timed build took 4:58.47 and reported 6,752,660 KiB of maximum process RSS.
The full allocation took 5:35 and Slurm reported 11,764,172 KiB.
The earlier cold run, `packing-cold-build`, was stopped to reuse the compiled QECLean dependency cache.
Both QECLean checkouts were unmodified at the pinned commit before this transfer.
This full build is a warm dependency replay, not an independent cold rebuild of QECLean.

`full-build-and-audit.log` contains the successful full build and audit.
`evaluation.json` records the statements, input hashes, dependency revisions, measurements, and proof-source hashes.
`proof-source-sha256.txt` and `cluster-source-check.log` connect all thirty proof, manifest, and toolchain files to the cluster run.
`slurm-accounting.txt` records final states for the successful checks and the superseded cold build.
`python-checks.json` records thirteen passing regression tests and the final Ruff results.

The surface generator now supplies explicit inverse row maps.
Lean checks their right-inverse equations and every submitted support equality.
The earlier local finite-set completeness attempt exhausted memory and the OS killed Emacs.
Further large evaluations run in Slurm.
Detachment protects a job from terminal termination but does not enforce a memory limit.

The mathematical statements concern the committed generated matrices.
Input SHA256 hashes and byte-for-byte regeneration tests connect them to the
[upstream qldpc-challenge JSON files](https://github.com/unitaryfoundation/qldpc-challenge/tree/8c87413d16b78cdd934b7b7a8592cddc81ae6eed/codes).
The JSON parser and numerical search remain outside the formal proof.
Historical evaluations in the other data directories retain their original sources, theorem names, and measurement scopes.

Published logs are sanitized copies. Descriptive run labels replace scheduler IDs.
Hostnames, login details, accounts, partitions, and workspace paths remain only in the ignored `.local/cluster/records/` directory.
Proof-source hashes, theorem statements, outcomes, and resource measurements are preserved.
The `publication` field in the JSON records identifies this treatment and retains the original log digests.
