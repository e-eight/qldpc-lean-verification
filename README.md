# Lean verification of qLDPC codes

This project proves claims about codes in the upstream
[qldpc-challenge](https://github.com/unitaryfoundation/qldpc-challenge) repository.
It groups codes by construction and accepts proved bounds when exact distance is out of reach.
The longer-term aim is reusable packing and construction theorems.

The active package, `QldpcVerification` in [lean/](lean/README.md), builds on [QECLean](https://github.com/Stavan-Jain/QECLean).
The independent Lean 4.36 proof remains an [archived reference](archive/QldpcCert/README.md).

[RECOMMENDATIONS.md](RECOMMENDATIONS.md) gives research priorities and literature guidance.
[CHECKS_AND_RESULTS.md](CHECKS_AND_RESULTS.md) preserves dated experiments, proof milestones, and resource measurements.
[CERTIFICATES.md](CERTIFICATES.md) defines the packing method and its checker interface.

## Proved results

Nineteen submitted instances have exact ranks, encoded dimension, and both exact CSS distances.
They comprise three surface codes and sixteen bicycle codes from the recorded challenge snapshots.

| Proof | Submitted result |
| --- | --- |
| `Surface225.parameters` | `[[225,1,15]]`, both ranks 112, through QECLean's surface theorem |
| `Surface529.parameters` | `[[529,1,23]]` through the shared surface adapter |
| `Surface961.parameters` | `[[961,1,31]]` through the shared surface adapter |
| `Bicycle262.parameters` | `[[262,2,15]]` through weighted packing and finite coverage |
| `Bicycle562.parameters` | `[[562,2,23]]`, both ranks 280, through the lattice bound |
| `Bicycle362.parameters` | `[[362,2,19]]`, both ranks 180, through the family theorem |
| [Thirteen further bicycle instances](data/bicycle-batch-evaluation/README.md) | Exact ranks and distances through the same family theorem |

The active theorem names have prefix `QldpcVerification` and use Lean 4.30.0-rc2.
`225-1-15` also has an independent archived packing proof on Lean 4.36.0-rc2.
Alternate lattice proofs recover `262-2-15` and `562-2-23`.

The generic coverage and weighted overlap theorems support any finite number `k` of encoded qubits.
For positive `m`, the cyclic family `GB(1+x^s,1+x^t,m)` has `c=gcd(s,t,m)` identical connected components.
Both ranks are `m-c`, the encoded dimension is `2c`, and both distances equal their corresponding component distances.
Connected components have complete logical coverage and lattice lower bounds with the original physical edge weights.
The lattice-based parameter theorem combines a separation bound with matching upper witnesses.

Five cyclic construction regressions have exact parameters `[[16,2,4]]`, `[[16,2,3]]`, `[[12,2,2]]`, `[[30,2,3]]`, and `[[24,4,2]]`.
A separate degenerate model has parameters `[[2,2,1]]`.
These constructions do not increase the submitted-instance count.
The [component record](data/components-evaluation/) preserves that milestone's inventory, theorem scope, hashes, and replay commands.
Earlier [packing records](data/packing-evaluation/) cover the finite certificates and additional surface proofs.

The elementary qubit-removal pilot now proves concrete logical lifts, preserved encoded dimension, and asymmetric distance bounds.
Its three small operations preserve, decrease, or increase exact distance, with all minima checked in Lean.
The [lifting record](data/lifting-evaluation/) includes exact criteria, independent review, source hashes, and bounded replay evidence.
These examples do not increase the submitted-instance count.

The completed axiom audits use only subsets of `propext`, `Classical.choice`, and `Quot.sound`.
No audited result depends on `native_decide` or `sorryAx`.
Lean proves statements about the committed generated matrices.
Regeneration tests and input hashes connect those matrices to the JSON files; the parser remains outside the formal proof.
These results do not change the challenge board's certification status.

## Python environment

Use Python 3.13 and [uv](https://docs.astral.sh/uv/) for the default environment.
`pyproject.toml` declares dependencies, `uv.lock` pins versions, and Ruff defines the Python style.
Clone the upstream [qldpc-challenge repository](https://github.com/unitaryfoundation/qldpc-challenge).
The scripts default to `../qldpc-challenge`; set `QLDPC_REPO` to use another path.
They read its `verify/gf2.py` source and use this project's environment.

```bash
uv sync --locked
uv run --locked ruff check .
uv run --locked ruff format --check .
uv run --locked pytest
uv run --locked python scripts/line_check.py 225-1-15
```

The tests reproduce the audited generated inputs and reject malformed certificates and unsupported generator inputs.
CI checks out a pinned revision of the upstream repository.
An optional accelerator needs a C++17 compiler and builds into this project's `.build/` directory:

```bash
uv run --locked --group search python scripts/build_fast_backend.py
uv run --locked python scripts/class_search.py --help
```

Rebuild the accelerator after changing its source or the Python minor version.
The build reads the upstream `verify/gf2_fast.cpp` source and does not write into the source repository's `verify/` directory.
Search results remain numerical evidence until Lean accepts a certificate.

The two bicycle generators have distinct roles.
`scripts/gen_orbit_instance.py` emits explicit weighted packing certificates for cyclic two-block inputs with `k=2`.
`scripts/gen_bicycle_family.py` emits recognition and lattice obligations for the shared theorem.
The latter requires cyclic row order and a unit first binomial difference:

```bash
uv run --locked python scripts/gen_bicycle_family.py \
  ../qldpc-challenge/codes/362-2-19.json --name Bicycle362
```

The corrected candidate screen uses exact integer inequalities and reports unsupported non-CSS entries separately:

```bash
uv run --locked python scripts/candidates.py --output-dir /tmp/qldpc-candidate-screening
```

Passing the screen does not supply a packing certificate or prove a reported distance.
The [dated screen and historical comparison](data/candidate-screening-2026-10-30/) preserve separate input identities.

## Build the QECLean proof

The package pins QECLean at `fed020a7e6be12825196cbee7bbc1ba56554158c`, under Apache-2.0.
Mathlib is pinned at `a3fde5017d59fa3cef8d4d24999f6b9b71b89a3b`.
The active package leaves upstream sources unchanged and imports no archived modules.
Regeneration reads input JSON files from upstream qldpc-challenge.
The Lean build uses the committed generated matrices.

For a full build, stage the repository in a cluster scratch workspace and submit from that workspace's root:

```bash
bash scripts/cluster/submit.sh --cpus-per-task=2 --mem=48G
```

The helper installs the pinned toolchain, fetches dependencies, builds the package, and runs the main guarded axiom audit.
Keep account, partition, SSH details, and site paths in the ignored `.local/cluster.env` file.
Raw logs also stay under `.local/`.
See [scripts/cluster/README.md](scripts/cluster/README.md) for configuration and submission instructions.

Run local Lean evaluations in a detached allocation with enforced memory and swap limits.
Detachment alone does not limit memory use.
With sufficient resources and the pinned `elan` toolchain, the build and main audit commands are:

```bash
cd lean
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean QldpcVerification/KernelAudit.lean
```

The latest component replay used a 5 GiB memory cap and a 128 MiB swap cap with dependency caches retained.
Historical measurements and their scopes are in [CHECKS_AND_RESULTS.md](CHECKS_AND_RESULTS.md).
See [lean/README.md](lean/README.md) for proof layout and regeneration commands.

## Next research milestone

Investigate applicability of the lifting theorem to the submitted `566-18-20` grafting reduction.
The elementary pilot and its small-example tests are complete.
The next obligations are recognizing actual matrix transformations and finding useful reference bounds or stronger preservation conditions.
The [research plan](RECOMMENDATIONS.md#logical-lifting-pilot-and-next-application) distinguishes this investigation from a proof of distance 20.
