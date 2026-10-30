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
| `QldpcVerification/Lattice/Winding.lean` | Integer period carries, winding coordinates, zero-lift boundaries, and a coverage-certified lattice bound |
| `QldpcVerification/Lattice/IncidenceRank.lean` | Connected incidence matrices have rank at least the vertex count minus one |
| `QldpcVerification/Lattice/Connectivity.lean` | Exact connected incidence rank and connectivity from two joint cyclic generators |
| `QldpcVerification/Lattice/Arithmetic562.lean` | The lattice congruence has minimum nonzero L1 norm 23 |
| `QldpcVerification/Input/Bicycle562Geometry.lean` | Original row recognition, cyclic commutation, connectivity, and logical coordinate identities |
| `QldpcVerification/Bicycle562.lean` | Both ranks 280, two encoded qubits, and both exact distances of 23 |
| `QldpcVerification/Input/Bicycle562Winding.lean` | Period-aware integer lifts for both submitted incidence graphs |
| `QldpcVerification/EvenBicycle16.lean` | An even-cyclic-length construction regression with parameters `[[16,2,4]]` |
| `QldpcVerification/WindingAudit.lean` | Twelve guarded audits for winding results and both bicycle regressions |
| `QldpcVerification/Bicycle/Walks.lean` | Closed-walk composition and transport of chains and displacement |
| `QldpcVerification/Bicycle/Normalized.lean` | Parametric paired winding witnesses, QECLean coverage, ranks, and two-sided lattice lower bounds |
| `QldpcVerification/Bicycle/Normalization.lean` | Monomial shifts, cyclic unit permutations, and transfer to submitted matrices |
| `QldpcVerification/Input/BicycleRecognition.lean` | Sparse four-point row recognition without dense matrix evaluation |
| `QldpcVerification/Input/LogicalWitness.lean` | Opposite-cycle pairings certify stored logical witnesses |
| `QldpcVerification/Lattice/FiniteBound.lean` | A checked finite window proves a lattice bound for arbitrary integers |
| `QldpcVerification/Bicycle362.lean` | The submitted `[[362,2,19]]` instance via the shared family theorem |
| `QldpcVerification/Bicycle262Lattice.lean` | A lattice proof independent of the existing packing proof |
| `QldpcVerification/Bicycle562Family.lean` | The 562-qubit matrices through the parametric normalization route |
| `QldpcVerification/Bicycle{4,58,82,100,110,122,170,226,278,298,346,422,454}.lean` | Thirteen additional submitted instances through the existing family theorem |
| `QldpcVerification/BatchAudit.lean` | Thirty-nine guards for the thirteen additional instances |
| `QldpcVerification/ConnectivityAudit.lean` | Twelve guards for joint connectivity, ranks, homology dimension, and regressions |
| `QldpcVerification/Bicycle/Connected.lean` | Ranks, encoded dimension, and QECLean homology dimension under joint coprimality |
| `QldpcVerification/Bicycle/PeriodBasis.lean` | Primitive integer steps, Bézout coefficients, and adapted winding labels |
| `QldpcVerification/Bicycle/SignedPaths.lean` | Closed walks with prescribed signed displacement in the original directions |
| `QldpcVerification/Bicycle/JointCoverage.lean` | Complete joint-step coverage, zero-displacement boundaries, and both lattice lower bounds |
| `QldpcVerification/Bicycle/JointMatch.lean` | Matrix recognition, rank transfer, and exact parameters for jointly generating steps |
| `QldpcVerification/Bicycle/JointExamples.lean` | Exact `[[12,2,2]]` and `[[30,2,3]]` nonunit regressions and a degenerate edge case |
| `QldpcVerification/Lattice/JointFiniteBound.lean` | Finite lattice exclusion with both original step coefficients |
| `QldpcVerification/JointAudit.lean` | Twenty-three guards for joint-step coverage, bounds, transport, and examples |
| `QldpcVerification/Components.lean` | Product submodules, block matrices, arbitrary-k coverage, and component weight bounds |
| `QldpcVerification/CoverageTransport.lean` | Transport complete logical coordinates through a qubit equivalence |
| `QldpcVerification/ComponentDistance.lean` | Exact distance of a nonempty product of identical components |
| `QldpcVerification/Bicycle/CyclicComponents.lean` | Explicit cyclic vertex and edge decomposition and both block-matrix identities |
| `QldpcVerification/Bicycle/ComponentBounds.lean` | Component coverage, ranks, encoded dimension, and both lattice lower bounds |
| `QldpcVerification/Bicycle/ComponentParameters.lean` | Matrix parameter transfer and exact equality of component and global distances |
| `QldpcVerification/Bicycle/GcdComponents.lean` | Gcd component count, reduced connectivity, ranks `m-c`, and `2c` logical coordinates |
| `QldpcVerification/BicycleComponents24.lean` | The two-component `[[24,4,2]]` construction regression |
| `QldpcVerification/ComponentAudit.lean` | Forty guards for decomposition, coverage, distance transfer, and regressions |
| `QldpcVerification/QubitRemoval.lean` | Concrete qubit-removal normal form, logical lifts, ranks, physical weights, and exact side-distance criteria |
| `QldpcVerification/QubitRemovalExamples.lean` | Kernel-checked preserving, losing, and increasing small operations |
| `QldpcVerification/QubitRemovalAudit.lean` | Seventy guards covering the qubit-removal pilot |
| `QldpcVerification/BicycleEven{16Family,Step16}.lean` | Even-length step-three and step-two construction regressions |
| `QldpcVerification/Bicycle/Regressions.lean` | Exact recovery of the earlier even example and an even-step detector counterexample |
| `QldpcVerification/FamilyAudit.lean` | Thirty-four guarded targets for the normalized family, recognition, applications, and regressions |
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
The main audit contains 181 unique guarded targets, including every submitted-instance capstone and the generic family results.
The coding-theory capstones depend only on `[propext, Classical.choice, Quot.sound]`.
The closed shortest-vector witness uses no axioms.

`Bicycle562.parameters` proves two encoded qubits and both distances of 23.
The separate `rankX` and `rankZ` theorems prove both ranks equal 280.
Its incidence graphs have steps `(7,145)` and `(145,7)` in `ZMod 281`.
An invertible step of size 7 proves connectivity and supplies the rank bound.
The existing coverage theorem detects every nontrivial logical through a block parity.
An odd-period migration theorem transfers this detection to winding coordinates.
The generalized lattice theorem then gives a nonzero integer displacement and applies the checked minimum norm of 23.
The stored X and Z witnesses supply the matching upper bounds.

The winding bridge follows [Arnault, Gaborit, and Saussay, Theorem II.7 and Corollary II.8](https://arxiv.org/html/2507.21237v1).
For each edge, a signed integer lift records its displacement, a vertex potential difference, and a carry across a lattice period.
Closed walks of zero displacement have zero winding coordinates.
Complete detector coverage then proves that their binary chains are boundaries.
The lower bound accepts any checked labels with this zero-displacement property.

`EvenBicycle16` defines `GB(1+x,1+x^3,8)` directly, with cyclic length 8 and 16 physical qubits.
Its coverage certificates prove two encoded qubits, both ranks 7, and both exact distances of 4.
Its `raw_parity_misses_logical` theorem proves that the eight-edge horizontal loop is nontrivial despite having zero raw block parities.
The winding coordinate detects that loop.
This regression is separate from the challenge's `16-2-4` JSON, for which no equivalence is claimed here.

The generic winding bridge works for positive cyclic lengths of either parity.
That bridge takes complete logical coverage, incidence recognition, and a lattice separation bound as explicit inputs.
The implementation uses certified linear algebra for the zero-lift-to-boundary step rather than formalizing the paper's planar filling argument.

`Bicycle/Normalized.lean` now constructs coverage symbolically for every positive cyclic length and every natural second step.
The full horizontal loop has winding coordinates `(1,0)`.
The horizontal path closed by a reverse vertical edge has coordinates `(0,1)`.
Both identities follow from signed integer displacement, without a parity restriction.
The paired witnesses and structural incidence rank prove complete coverage and both ranks equal `m-1`.
The `complex` construction uses QECLean's `HomologicalCode`, and `complex_coverage` identifies its logical classes.

The dual proof swaps the two edge blocks and negates cyclic vertex indices.
This permutation preserves weight and transfers both cycle and boundary spaces.
It handles even second steps without reusing the dependent naive dual detectors.
`Bicycle.Regressions.even_step_old_coordinates_fail` proves the corresponding failure on a nontrivial weight-three logical.

`Bicycle/Normalization.lean` handles monomial offsets and multiplication by a unit modulo the cyclic length.
The generic theorem accepts arbitrary surjective row labels and a qubit equivalence.
The current emitter recognizes submitted rows in cyclic order, through four-point supports and distinctness checks.
It evaluates no dense matrix equality and emits no rank or coverage certificate.
The resulting input route verifies `362-2-19`, `262-2-15`, and `562-2-23`.
It also reproduces the earlier even example's matrices exactly and verifies `GB(1+x,1+x^2,8)` as `[[16,2,3]]`.
Connected cases where neither binomial difference is a unit remain outside this normalization interface.

The later batch accepts thirteen additional submitted codes without changes to the family theorem or emitter.
Their data, row recognition, arithmetic, and parameter modules are generated in the same four-file layout.
All sixteen inputs matching the current cyclic row convention in the recorded upstream qldpc-challenge revision now have exact proofs.
The three surface proofs bring the submitted-instance inventory to nineteen.

The broader `Bicycle/Connected.lean` keeps both steps `s` and `t` explicit.
The condition `Nat.gcd (Nat.gcd s t) m = 1` supplies an integer combination of the steps equal to one modulo `m`.
Functions invariant along every edge are therefore constant.
The exact incidence-rank theorem and the dual permutation give both ranks `m-1` and two encoded qubits.
The QECLean homological code has first homology of dimension two.
The steps 2 and 3 at cyclic length 6 exercise the case where both steps are nonunits.
The steps 2 and 4 at length 6 admit a nonconstant invariant function, which tests the connectivity hypothesis.
The general model recovers the existing normalized matrices when `s=1`.

`PeriodBasis.lean` removes the common integer factor of the two steps, which is a unit modulo the cyclic length.
For the resulting coprime integers `a,b`, Bézout coefficients satisfy `a*p+b*q=1`.
The adapted labels record the period carry and the transverse quantity `q*u-p*v` modulo two.
The closed walks with displacements `(m*p,m*q)` and `(b,-a)` have coordinate pairs `(1,0)` and `(0,1)`.
`JointCoverage.lean` uses their identity pairing and the structural rank bound to prove complete coverage.
This coverage is also exposed for QECLean's homological code.
Zero-displacement closed walks are boundaries, and both CSS sides satisfy the lattice distance bound.

The lattice condition remains `s*u+t*v = 0 mod m`, with L1 norm `|u|+|v|` in the original edge directions.
The proof changes logical coordinates without replacing edges by longer paths in the distance calculation.
`Connected.Match.parameters` accepts a lattice separation bound and exact-weight logical witnesses for the submitted matrices.
The canonical examples have exact parameters `[[12,2,2]]` at `(m,s,t)=(6,2,3)` and `[[30,2,3]]` at `(15,6,10)`.
The latter exercises a common integer factor that remains invertible modulo `m`.
The degenerate `(1,0,0)` example has parameters `[[2,2,1]]` and tests the zero-gcd branch.
Lean also proves that naive carry and vertical parity miss a logical in the twelve-qubit example.
The existing Python emitter retains its unit-first restriction, while the general matrix interface accepts any proved recognition maps.

The disconnected family is handled by `Bicycle/CyclicComponents.lean` and its component theorems.
For positive `c,l` and steps `c*a,c*b`, the vertex map is `(r,v) ↦ r+c*v` modulo `c*l`.
The corresponding qubit map preserves the two edge blocks and Hamming weight.
Both matrices become independent blocks of the length-`l` code with steps `a,b`.
If the reduced steps jointly generate, both ranks are `c*(l-1)` and the encoded dimension is `2c`.

`GcdComponents.lean` specializes the factorization to `c=gcd(s,t,m)` and proves that the reduced steps jointly generate.
It proves both ranks `m-c`, encoded dimension `2c`, and complete logical coverage for every positive original cyclic length.
The coverage certificate is also available for QECLean's homological code in the factorized model.
`Components.coverage` combines certificates with any number `k` of logical coordinates into a certificate with `c*k` coordinates.
The construction uses component-supported detectors and witnesses without enumerating logical classes.

`ComponentDistance.lean` proves exact distance equivalence for a nonempty product of identical components.
Logical operators restrict to components, and a component witness extends with zero support elsewhere without changing its weight.
The bicycle matrix theorems transfer this result to both CSS distances.
`BicycleComponents24.parameters` reuses both distances of the existing `BicycleJoint12` code and proves `[[24,4,2]]`.
`BicycleComponents24.ranks` proves both ranks 10.
Its matrix identities prove that it is two copies of that construction.
Four-coordinate detection, failure of global block parity, the single-component case, and zero-step structure also pass.
This construction is separate from submitted challenge entries.
The component mathematics follows established direct-sum results.
See the [prior-work correspondence](../RECOMMENDATIONS.md#component-decomposition-and-logical-coordinates) for exact statements and the scope of this formalization.

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
It imports no archived modules and does not require upstream qldpc-challenge sources for this build.
Current component records are in [`../data/components-evaluation/`](../data/components-evaluation/).
Earlier joint-step coverage and distance records remain in [`../data/joint-evaluation/`](../data/joint-evaluation/).
Earlier batch and connectivity records remain in [`../data/bicycle-batch-evaluation/`](../data/bicycle-batch-evaluation/).
Earlier family logs, audits, and source hashes remain in [`../data/family-evaluation/`](../data/family-evaluation/).
The earlier winding records remain in [`../data/winding-evaluation/`](../data/winding-evaluation/).
The earlier four-instance records remain in [`../data/packing-evaluation/`](../data/packing-evaluation/).
The earlier surface-only records remain in [`../data/lean-evaluation/`](../data/lean-evaluation/).
The full cluster replay used a warm dependency cache and took 4:58.47 for the timed build.
The entire build and audit allocation took 5:35.
Slurm reported 11,764,172 KiB, while the timed build reported 6,752,660 KiB of maximum process RSS.
These measurements have different scopes.

## Regenerate the submitted input

Run the following command from the repository root.
Clone [upstream qldpc-challenge](https://github.com/unitaryfoundation/qldpc-challenge) to obtain the input JSON files.
The commands below use `../qldpc-challenge` as the source path.
For another clone location, substitute the full path to its JSON file.

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
With `--checks`, the generator derives the imported module from the output path relative to this project's `lean/` directory.
Absolute paths and paths relative to the current directory are accepted.
If the output is outside `lean/`, supply `--data-module QldpcVerification.Input.Bicycle262Data` to specify its eventual Lean module.
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

Generate a complete family application from the repository root:

```bash
uv run --locked python scripts/gen_bicycle_family.py \
  ../qldpc-challenge/codes/362-2-19.json --name Bicycle362
```

The emitter writes data, sparse recognition, arithmetic, and capstone modules beneath `lean/QldpcVerification/`.
`--output-root` selects another output directory for regeneration comparisons.
The generator uses only the Python standard library.
It requires reciprocal binomial checks in cyclic row order, a unit first difference, and equally weighted X and Z witnesses.
Lean independently checks the emitted support, syndrome, pairing, weight, and lattice obligations.
The parser and its numerical preflight are outside the formal proof.

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
