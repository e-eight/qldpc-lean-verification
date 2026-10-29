# qLDPC Lean verification

`QldpcVerification` is the main Lean package for this project.
It depends directly on QECLean and uses its definitions for generic coding theory.
The matrix input modules connect submitted check matrices to QECLean's constructions.

| File | Purpose |
|---|---|
| `QldpcVerification/Input/MatrixSpec.lean` | Matrix-level statements for the submitted CSS code |
| `QldpcVerification/Input/Surface225Support.lean` | Generated X and Z check supports from the submitted JSON |
| `QldpcVerification/Input/Surface225Labels.lean` | Generated QECLean face labels for the original rows |
| `QldpcVerification/Input/Surface225Match.lean` | Kernel proofs of every row match and both row maps' surjectivity |
| `QldpcVerification/Transport.lean` | Qubit reindexing preserves weight, dot products, kernels, and row spaces |
| `QldpcVerification/Surface225.lean` | QECLean rank and distance results applied to the submitted matrices |
| `QldpcVerification/Overlap.lean` | Weighted counting and conditional X/Z bounds over QECLean's homological code model |
| `QldpcVerification/Coverage.lean` | Paired witnesses and a rank bound prove complete detection for any logical dimension |
| `QldpcVerification/Input/Homological.lean` | The submitted CSS matrices define a QECLean homological code |
| `QldpcVerification/Input/SparseCertificates.lean` | Soundness of the finite matrix, pairing, class, and weighted-cap checks |
| `QldpcVerification/Input/Bicycle262Data.lean` | Generated supports, rank certificates, witnesses, and weighted representatives |
| `QldpcVerification/Input/Bicycle262Checks.lean` | Kernel evaluation of every finite bicycle certificate |
| `QldpcVerification/Bicycle262.lean` | Two encoded qubits and both exact distances of 15 |
| `QldpcVerification/RotatedSurface.lean` | A shared recognition theorem for the QECLean surface family |
| `QldpcVerification/Input/Surface{529,961}{Labels,Support,Lookup,Match}.lean` | Submitted matrices, canonical face labels, inverse row maps, and kernel recognition proofs |
| `QldpcVerification/Surface529.lean` | One encoded qubit and both exact distances of 23 |
| `QldpcVerification/Surface961.lean` | One encoded qubit and both exact distances of 31 |
| `QldpcVerification/Lattice/Trail.lean` | A detected binary cycle contains a detected closed trail |
| `QldpcVerification/Lattice/Displacement.lean` | A detected trail gives a nonzero lattice relation whose L1 norm is at most its length |
| `QldpcVerification/Lattice/IncidenceRank.lean` | Connected incidence matrices have rank at least the vertex count minus one |
| `QldpcVerification/Lattice/Arithmetic562.lean` | The lattice congruence has minimum nonzero L1 norm 23 |
| `QldpcVerification/Input/Bicycle562Geometry.lean` | Original row recognition, cyclic commutation, connectivity, and logical coordinate identities |
| `QldpcVerification/Bicycle562.lean` | Both ranks 280, two encoded qubits, and both exact distances of 23 |
| `QldpcVerification/BicycleAudit.lean` | Focused guarded audit for the bicycle proof and its generic dependencies |
| `QldpcVerification/CertificateControls.lean` | Negative controls for malformed finite certificates |
| `QldpcVerification/KernelAudit.lean` | Guarded axiom audits for the instance and generic capstones |

The surface-code theorem is `QldpcVerification.Surface225.parameters`.
It proves both stabilizer ranks equal 112, one encoded qubit, and `d_X = d_Z = 15`.
The rotation sends QECLean vertex `(x,y)` to submitted index `(14-x)*15+y`.
The input matrices keep the original order of all 224 submitted rows.
The shared recognition theorem also accepts the original matrices of `529-1-23` and `961-1-31`.
Their qubit maps use the same rotation at board sizes 23 and 31.
Kernel proofs of explicit right inverses establish complete canonical face coverage.

The overlap theorems use natural multiplicities and the strict threshold `(D-1)*cap < total`.
`CoverageCertificate` proves detection from a finite identity pairing matrix and a rank bound.
Its rank-nullity argument identifies the vectors with zero coordinates as exactly the boundaries.
It also proves that equal coordinates identify the same logical class.
No enumeration of all `2^k - 1` nonzero classes is needed.

`Bicycle262.parameters` proves both distances of 15 and two encoded qubits for the submitted matrices.
Its two detector families have `(total, cap)` values `(3930,258)` and `(131,9)` on each CSS side.
Each value satisfies the strict threshold for distance 15.
Lean checks every expanded representative, including its class, rather than assuming that translations preserve the class.
The stored weight-15 witnesses supply the upper bounds.
All twenty-two guarded audits pass.
The coding-theory capstones depend only on `[propext, Classical.choice, Quot.sound]`.
The closed shortest-vector witness uses no axioms.

`Bicycle562.parameters` proves two encoded qubits and both distances of 23.
The separate `rankX` and `rankZ` theorems prove both ranks equal 280.
Its incidence graphs have steps `(7,145)` and `(145,7)` in `ZMod 281`.
An invertible step of size 7 proves connectivity and supplies the rank bound.
The existing coverage theorem then detects every nontrivial logical through a block parity.
The lattice theorem turns that parity into a nonzero integer displacement and applies the checked minimum norm of 23.
The stored X and Z witnesses supply the matching upper bounds.

This graph bridge proves a lower bound for cycles with nonzero direction parity.
The concrete coverage certificate proves that this hypothesis holds for every nontrivial logical in this instance.
It does not yet give a general equivalence theorem for every weight-four bicycle code.
In particular, other quotients can require different logical coordinates.

## Build

`lean-toolchain` pins Lean 4.30.0-rc2.
The Lake configuration and manifest pin QECLean and Mathlib.
QECLean's commit is `fed020a7e6be12825196cbee7bbc1ba56554158c`, under Apache-2.0.
Its source remains an external dependency.

For the full replay, stage this project in a cluster scratch workspace.
Submit from that workspace's repository root:

```bash
bash scripts/cluster/submit.sh --cpus-per-task=2 --mem=48G
```

The helper reads account and partition settings from the ignored `.local/cluster.env` file.
See [`../scripts/cluster/README.md`](../scripts/cluster/README.md) for local configuration and private log locations.
The batch script builds all targets and runs the axiom audit.
The job survives loss of the local terminal or Emacs session.

With `elan` installed on a machine with sufficient memory, these commands run from the `lean/` directory:

```bash
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean QldpcVerification/KernelAudit.lean
```

If local evaluation is necessary, detach the process and enforce a memory limit.
Do not use an unbounded foreground process for the large kernel checks on the current machine.

The default build includes the concrete instance proofs and the generic theorems.
The first build also compiles the imported QECLean modules.
The pinned upstream modules and several sparse-checker proofs emit style warnings.
The bicycle coordinate proof also emits a nonfatal exponentiation-threshold warning during elaboration.
Its completed proof still passes the kernel and axiom audit.
The guarded audit covers the dependency closure of the listed capstones.
Use Slurm for large kernel evaluations, because they can exceed the local memory budget.
The cluster script runs independently of the local terminal or Emacs session.
Detachment alone does not enforce a memory limit.

The package builds from its own sources and committed input data.
It imports no archived modules and does not require the sibling challenge checkout for this build.
Build logs, audits, and source hashes are in [`../data/packing-evaluation/`](../data/packing-evaluation/).
The earlier surface-only records remain in [`../data/lean-evaluation/`](../data/lean-evaluation/).
The full cluster replay used a warm dependency cache and took 4:58.47 for the timed build.
The entire build and audit allocation took 5:35.
Slurm reported 11,764,172 KiB, while the timed build reported 6,752,660 KiB of maximum process RSS.
These measurements have different scopes.

## Regenerate the submitted input

Run the following command from the repository root.
The source checkout defaults to `../qldpc-challenge`.
If it lives elsewhere, substitute the full path to its JSON file.

```bash
uv run --locked python scripts/gen_qeclean_surface.py \
  ../qldpc-challenge/codes/225-1-15.json \
  lean/QldpcVerification/Input/Surface225Labels.lean \
  --supports lean/QldpcVerification/Input/Surface225Support.lean
uv run --locked pytest
```

The generator uses only the Python standard library.
It emits the submitted supports and their canonical face labels.
The tests reproduce both files and the archived certificate data.

The original JSON SHA256 is
`7a180b0f143d672013952e2f24fa12664e20fe7b03f993994076194e4b28bebe`.
Lean evaluates the row matches with `decide +kernel`.
The Python parser contributes no axioms, and formal JSON parsing remains outside the proof.

Generate the bicycle certificate from the repository root:

```bash
uv run --locked python scripts/gen_orbit_instance.py 262-2-15 \
  QldpcVerification.Bicycle262Data \
  lean/QldpcVerification/Input/Bicycle262Data.lean \
  --checks lean/QldpcVerification/Input/Bicycle262Checks.lean
```

The generator rebuilds class labels from the matrices and emits integer weights.
Lean checks the output independently.
The generator currently accepts cyclic two-block instances with two encoded qubits.
The generic Lean coverage and overlap theorems allow any finite logical dimension.

Generate the lattice instance's matrices and witness checks from the repository root:

```bash
uv run --locked python scripts/gen_bicycle_lattice.py
```

The emitter preserves both original row orders.
Lean proves the structural ranks and commutation separately from the emitted witness checks.
The JSON parser and the Python rank preflight remain outside the formal proof.
The input contains no numerical rank certificate.

For an additional surface instance, supply its odd board size and inverse row maps:

```bash
uv run --locked python scripts/gen_qeclean_surface.py \
  ../qldpc-challenge/codes/529-1-23.json \
  lean/QldpcVerification/Input/Surface529Labels.lean --size 23 \
  --supports lean/QldpcVerification/Input/Surface529Support.lean \
  --lookup lean/QldpcVerification/Input/Surface529Lookup.lean \
  --match lean/QldpcVerification/Input/Surface529Match.lean \
  --instance lean/QldpcVerification/Surface529.lean
```

The inverse maps give an explicit submitted row for each canonical face.
Lean proves the right-inverse equations and every support equality.
This avoids a repeated search through all submitted rows.

## Archived proof

The independent Lean 4.36 package lives in [`../archive/QldpcCert/`](../archive/QldpcCert/README.md).
Its proof sources retain their audited hashes.
The older `QecBridge` package name appears only in historical records.
New development uses this package and the `QldpcVerification` namespace.
