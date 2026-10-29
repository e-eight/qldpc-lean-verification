# Current Lean proof records

These records cover the main package in `lean/`, named `QldpcVerification`.
`build.log` records its successful build after clearing the project's build outputs.
The pinned dependency cache was retained.
`kernel-audit.log` records five guarded capstones with only the three standard axioms.
`surface225.json` records the theorem, dependency pins, current source hashes, and archive integrity results.

The earlier integration records in [`../qeclean-evaluation/`](../qeclean-evaluation/) retain their earlier theorem names and proof-source paths.
The independent Lean 4.36 proof records remain in [`../kernel-evaluation/`](../kernel-evaluation/).
Their package now lives in `archive/QldpcCert` with unchanged proof-source hashes.
The active package imports no archived modules.

Published logs are sanitized copies. Descriptive run labels replace scheduler IDs.
Hostnames, login details, accounts, partitions, and workspace paths remain only in the ignored `.local/cluster/records/` directory.
Proof-source hashes, theorem statements, outcomes, and resource measurements are preserved.
The `publication` field in the JSON records identifies this treatment and retains the original log digests.
