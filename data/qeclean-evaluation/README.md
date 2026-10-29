# QECLean proof records

`surface225-qeclean.json` records the theorem, dependency pins, source hashes, and test results.
`build.log` records the successful package build.
`kernel-audit.log` records five capstones with only the three standard axioms.
The two timing logs record successful local module rechecks after dependency compilation.

The timing wrapper runs each command in a fresh Python process.
It records elapsed time with `time.perf_counter()` and child-process RSS with Linux `resource.getrusage(RUSAGE_CHILDREN)`.
The measurements exclude dependency setup and do not measure aggregate memory across concurrent processes.
The exact commands appear in the JSON record.

`provisioning.log` belongs to the failed cluster dependency setup.
It is not evidence of a successful cluster proof.
The home file quota was exceeded during that run.
The incomplete toolchain and package cache from this task were removed.
The final Lean proof and audit passed locally.

These records preserve theorem names and proof-source paths from before package consolidation.
The former `lean/QecBridge` package is now the main package in `lean/`.
Its namespace changed from `QecBridge` to `QldpcVerification`.
The earlier `lean/QldpcCert` package now lives in `archive/QldpcCert`.
See [`../lean-evaluation/`](../lean-evaluation/) for current build and audit records.

Published logs are sanitized copies. Descriptive run labels replace scheduler IDs.
Hostnames, login details, accounts, partitions, and workspace paths remain only in the ignored `.local/cluster/records/` directory.
Proof-source hashes, theorem statements, outcomes, and resource measurements are preserved.
The `publication` field in the JSON records identifies this treatment and retains the original log digests.
