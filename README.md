# Lean verification of qLDPC codes

This project proves claims about codes in the sibling
[qldpc-challenge](https://github.com/unitaryfoundation/qldpc-challenge) repository.
It groups codes by construction and accepts proved bounds when exact distance is out of reach.
The longer-term aim is to formalize reusable packing and construction theorems.

The active development path builds on [QECLean](https://github.com/Stavan-Jain/QECLean).
The main Lean package lives in [`lean/`](lean/README.md) as `QldpcVerification`.
The independent proof remains an archived reference in [`archive/QldpcCert/`](archive/QldpcCert/README.md).

## Proved results

The submitted `codes/225-1-15.json` has two independently constructed Lean proofs.
Both state distance through the kernels and row spaces of the submitted matrices.
The active matrix specification is `lean/QldpcVerification/Input/MatrixSpec.lean`.

| Proof | Result | Lean version |
|---|---|---|
| `QldpcVerification.Surface225.parameters` | Stabilizer ranks 112 and 112, one encoded qubit, `d_X = d_Z = 15` | 4.30.0-rc2 |
| `QldpcVerification.Bicycle262.parameters` | Two encoded qubits, `d_X = d_Z = 15` by weighted packing and finite coverage certificates | 4.30.0-rc2 |
| `QldpcVerification.Surface529.parameters` | One encoded qubit, `d_X = d_Z = 23` | 4.30.0-rc2 |
| `QldpcVerification.Surface961.parameters` | One encoded qubit, `d_X = d_Z = 31` | 4.30.0-rc2 |
| `QldpcVerification.Bicycle562.parameters` | Two encoded qubits, `d_X = d_Z = 23` by the lattice bound | 4.30.0-rc2 |
| `QldpcVerification.Bicycle362.parameters` | Both ranks 180, two encoded qubits, `d_X = d_Z = 19` by the normalized family theorem | 4.30.0-rc2 |
| `Surface225.distance` | `d_X = d_Z = 15` by a packing certificate | 4.36.0-rc2 |

The QECLean proof matches every submitted check support to a canonical surface-code face.
It proves that a 90-degree rotation preserves kernels, row spaces, logical operators, and Hamming weight.
It then applies QECLean's parametric distance and rank theorems.
It does not use the independent packing proof.
The shared `RotatedSurfaceMatch.parameters` theorem also accepts the submitted `529-1-23` and `961-1-31` matrices.
Their finite certificates use explicit inverse row maps to establish complete canonical face coverage.

The weighted packing proof for `262-2-15` checks matrix commutation, rank certificates, paired logical witnesses, every representative, and weighted overlap caps.
A generic theorem proves that the certified detector classes detect every nontrivial logical.
This theorem works for any logical dimension `k`, the number of encoded qubits.
The current bicycle input generator accepts cyclic two-block codes with `k = 2`.

The `562-2-23` proof uses the lattice congruence `7*u + 145*v = 0 mod 281`.
Lean derives the ranks from connected incidence graphs, lifts a detected binary cycle to an integer displacement, and excludes shorter nonzero displacements.
It checks both stored weight-23 logical witnesses for the upper bounds.
This proof uses no numerical pivot certificate or orbit packing.
The separate theorems `Bicycle562.rankX` and `Bicycle562.rankZ` prove both stabilizer ranks equal 280.

The lattice bridge now also uses period-aware winding coordinates, following
[Arnault, Gaborit, and Saussay](https://arxiv.org/html/2507.21237v1).
Both the submitted `562-2-23` proof and the construction `GB(1+x,1+x^3,8)` pass this bridge.
`EvenBicycle16.parameters` proves the latter has two encoded qubits and both exact distances of 4.
Lean also proves that its raw block parities miss a logical operator while its winding coordinate detects it.
This construction regression is separate from the challenge's `16-2-4` JSON entry.
The later parametric family proof also verifies the submitted `362-2-19` matrices.
The verified submitted-instance count is now six.
The current records are in [`data/family-evaluation/`](data/family-evaluation/).
Earlier winding records remain in [`data/winding-evaluation/`](data/winding-evaluation/).

`Bicycle/Normalized.lean` constructs complete logical coverage for `GB(1+x,1+x^a,m)` at every positive cyclic length.
Closed walks supply paired winding witnesses for either parity of `m` and `a`.
The theorem proves both ranks equal `m-1`, two encoded qubits, and both lattice distance lower bounds.
An explicit axis swap and cyclic inversion transfer the result to the dual side.
`Bicycle/Normalization.lean` proves that monomial offsets and a unit first step preserve ranks, logical operators, and weight.
Sparse row recognition then connects the submitted matrices to the family.

The same route supplies new lattice proofs for `262-2-15` and `562-2-23`.
It also reproduces the earlier `[[16,2,4]]` matrices and verifies an even-step `[[16,2,3]]` construction regression.
The latter rejects the naive dual coordinate choice identified during subagent review.
These construction regressions remain separate from challenge leaderboard inputs.

The completed axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.
These results do not depend on `native_decide` or `sorryAx`.
The logs, source hashes, dependency revisions, and measurements are in
[`data/bicycle-evaluation/`](data/bicycle-evaluation/), [`data/packing-evaluation/`](data/packing-evaluation/), and [`data/lean-evaluation/`](data/lean-evaluation/).
Earlier records remain in [`data/qeclean-evaluation/`](data/qeclean-evaluation/) and
[`data/kernel-evaluation/`](data/kernel-evaluation/), with their recorded proof-source identities.

Lean proves statements about the committed generated matrices.
Regeneration tests and a SHA256 hash connect these matrices to the original JSON.
The JSON parser is outside the formal proof.
These results do not change the challenge board's certification status.

## Python environment

Use Python 3.13 and [uv](https://docs.astral.sh/uv/) for the default environment.
`pyproject.toml` declares the dependencies, and `uv.lock` pins their versions.
Ruff defines the Python style and lint rules.

Place `qldpc-challenge` next to this repository, or set `QLDPC_REPO` to its path.
The scripts read its `verify/gf2.py` source.
They use this project's environment rather than the sibling environment.

```bash
uv sync --locked
uv run --locked ruff check .
uv run --locked ruff format --check .
uv run --locked pytest
uv run --locked python scripts/line_check.py 225-1-15
```

The regression tests reproduce the audited Lean input byte for byte.
They also reject malformed support data and exercise exact rational packing arithmetic.
The Python workflow runs these checks against a pinned challenge checkout.

The optional search accelerator requires a C++17 compiler.
Build it into this project's `.build/` directory:

```bash
uv run --locked --group search python scripts/build_fast_backend.py
uv run --locked python scripts/class_search.py --help
```

This command reads the sibling C++ source and writes no files into its `verify/` directory.
Rebuild the accelerator after changing the Python minor version or its source.
Search results remain numerical evidence until a Lean proof accepts the certificate.

Generate another supported binomial instance with the family emitter:

```bash
uv run --locked python scripts/gen_bicycle_family.py \
  ../qldpc-challenge/codes/362-2-19.json --name Bicycle362
```

The current emitter requires cyclic row order and a unit first binomial difference.
It emits sparse row recognition, stored-witness checks, and a finite lattice separation certificate.
Ranks and complete logical coverage follow from the shared theorem.

## Build the QECLean proof

The main package pins QECLean at `fed020a7e6be12825196cbee7bbc1ba56554158c`.
Its Mathlib revision is `a3fde5017d59fa3cef8d4d24999f6b9b71b89a3b`.
QECLean uses the Apache-2.0 license.
The package imports the required surface-code modules and leaves upstream source unchanged.

Use Slurm for the full build on this machine's behalf.
Stage the repository in a cluster scratch workspace, then submit from that workspace's root:

```bash
bash scripts/cluster/submit.sh --cpus-per-task=2 --mem=48G
```

The script installs the pinned toolchain, fetches dependencies, builds the package, and runs the guarded axiom audit.
It writes raw logs under the ignored `.local/cluster/logs/` directory and survives loss of the local terminal or Emacs session.
Account, partition, SSH details, and site paths belong in the ignored `.local/cluster.env` file.
See [`scripts/cluster/README.md`](scripts/cluster/README.md) for the template and submission instructions.

On a machine with sufficient memory, the equivalent commands use Lean's `elan` toolchain manager:

```bash
cd lean
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean QldpcVerification/KernelAudit.lean
```

Do not run these large evaluations in an unbounded local session.
If local evaluation is necessary, use a detached process with an enforced memory limit.

The build includes the concrete instances by default.
The guarded audit fails if the capstone theorem's axiom list changes.
The sibling checkout is needed for regeneration, but not for this Lean build.
The active package imports no archived modules.
New theory uses QECLean's definitions, while matrix recognition stays in ordinary input modules.
See [`lean/README.md`](lean/README.md) for the proof layout and regeneration commands.

Before the package consolidation, local warm rechecks took 11.50 seconds for row matching and 3.93 seconds for the final proof module.
Their maximum child-process RSS values were 4.34 GiB and 3.74 GiB.
These measurements exclude dependency setup and are not cold-build benchmarks.
The independent proof's earlier cluster run took 240.50 seconds and about 3.95 GiB for its instance.

The submission helper is [`scripts/cluster/submit.sh`](scripts/cluster/submit.sh).
Stage the project in the scratch workspace recorded in your local configuration and submit from that project root.
The attempted home-directory setup exceeded the file quota while unpacking dependencies.
Its incomplete toolchain and package cache were removed.
The earlier successful kernel-proof workspace remains intact.

Run large certificate evaluations in Slurm.
A local surface recognition attempt exhausted memory and the OS killed the Emacs session.
Detaching a process protects it from shell termination but does not limit its memory use.
The independent cluster replay of the bicycle finite checks took 13:08 and used about 5.92 GiB of maximum process RSS.
The complete allocation, including dependency setup, reached about 12.47 GiB according to Slurm.
These measurements describe different scopes and do not give the aggregate memory use of a cold build.
The earlier full build and thirteen guarded audits passed in cluster run `packing-full-replay`.
Its timed build took 4:58.47 with a warm dependency cache.
Maximum process RSS was about 6.44 GiB, while Slurm reported about 11.22 GiB for the allocation.
Both additional surface instances use the shared theorem and passed the same audit.

## Research path

[`RECOMMENDATIONS.md`](RECOMMENDATIONS.md) gives the current plan and the relevant prior work.
A reusable weighted overlap bound exists in `lean/QldpcVerification/Overlap.lean`.
`Coverage.lean` discharges class coverage through paired witnesses and a rank bound.
The complete `262-2-15` proof applies this method on both CSS sides.
`RotatedSurface.lean` supplies a shared adapter for additional surface sizes.
The submitted `529-1-23` and `961-1-31` instances now pass that adapter.
The lattice-based instance proof for `562-2-23` now passes the kernel.
The winding-coordinate extension also passes the existing proof and an even-length construction regression.
The normalized unit-step family now has shared coverage, rank, normalization, and lattice-bound theorems.
Further extensions include connected binomial codes without an individual unit step and formal definitions of the user's boundary operations.

Saved Python experiments include packing certificates and partial bounds for several code families.
They are historical results for the recorded challenge snapshots, not a fresh audit of the live board.
[`CHECKS_AND_RESULTS.md`](CHECKS_AND_RESULTS.md) records their commands and limits.
[`CERTIFICATES.md`](CERTIFICATES.md) explains the packing method.

This repository does not edit or publish changes to the challenge verifier or board.
