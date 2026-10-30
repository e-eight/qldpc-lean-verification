# Recommendations after the QECLean proof

Updated 2026-10-30.
The QECLean adapter proves the original `225-1-15` matrices' ranks and distances.
Finite coverage certificates also complete a weighted packing proof for `262-2-15` on both CSS sides.
The structural lattice proof now verifies `562-2-23`, including both ranks of 280 and both distances of 23.
The normalized bicycle family now supplies coverage, ranks, and two encoded qubits symbolically.
Its normalization adapter verifies `362-2-19` and gives alternate proofs for `262-2-15` and `562-2-23`.
The inventory is nineteen submitted instances and five exact-distance construction regressions, plus a degenerate one-vertex test.
The broader joint-connectivity family now has complete logical coverage, ranks, and both lattice distance lower bounds.
Disconnected component decomposition now gives both ranks `m-c`, encoded dimension `2c`, and exact transfer of component distance, where `c=gcd(s,t,m)`.
The axiom audit contains only Lean's three standard axioms.
The project can now extend an existing QEC foundation and retain its independent packing proof as a reference.

## Foundation and scope

Use [QECLean](https://github.com/Stavan-Jain/QECLean/tree/fed020a7e6be12825196cbee7bbc1ba56554158c)
for stabilizer algebra, homological codes, logical correspondence, and existing family theorems.
Pin the dependency, import the required modules, and keep application certificates here.
Avoid a separate implementation of the Pauli and stabilizer framework.

Keep `lean/QldpcVerification/Input/MatrixSpec.lean` as the short statement of the submitted matrix claims.
The adapter already proves that its logical predicates agree with QECLean's cycle and boundary predicates.
This interface separates recognition of a submitted code from the reusable theorem for its family.

The first acceptance test is complete.
Every X and Z row of `225-1-15` matches a QECLean face after a qubit rotation.
Both ranks equal 112, the rank formula gives one encoded qubit, and `d_X = d_Z = 15`.
The complete theorem is `QldpcVerification.Surface225.parameters`.
The proof uses QECLean's family results rather than the older instance's packing theorem.

The main package is `QldpcVerification` in `lean/`, on QECLean's Lean 4.30 toolchain.
The audited Lean 4.36 package now lives in `archive/QldpcCert`.
Its proof sources retain their audited hashes.
The main package imports no archive code and has no separate bridge library.
Keep submitted matrix specifications and equivalence proofs in its `Input/` modules.
Use QECLean's definitions directly for new generic theory.

## Completed milestone: finite coverage and a higher-k instance

`lean/QldpcVerification/Overlap.lean` proves weighted support counting and pairing invariance within a class.
`Coverage.lean` now discharges the coverage requirement through finite linear-algebra certificates.
`Input/Homological.lean` connects submitted CSS matrices to QECLean's homological model.

A code's logical dimension is the number of encoded qubits, usually called `k`.
The generic theorem accepts `k` detector vectors, `k` dual witnesses, and a dimension bound.
Lean proves that their identity pairing matrix gives complete logical coordinates.
It then proves that a cycle is a boundary exactly when every coordinate is zero.
Every nontrivial logical therefore pairs oddly with at least one detector.

For each detector, a finite family supplies the weighted lower bound.
Natural multiplicities represent rational weights after clearing denominators.
The complete `262-2-15` application proves these facts in Lean:

1. Each representative lies in the required cycle space.
2. Representatives assigned to one class differ by a boundary.
3. The total multiplicity through each qubit is at most the stated cap `C`.
4. The selected classes detect every nontrivial logical on the side being bounded.

If a detected family has total multiplicity `N`, double counting gives `N ≤ C * weight`.
For an integer target `D`, use the strict threshold `N > (D - 1) * C`.
This retains the ceiling in examples such as `ceil(113/8) = 15`.
Use exact integers or fractions throughout certificate construction and checking.

The two families on each side have `(total, cap)` values `(3930,258)` and `(131,9)`.
Both pass the strict threshold for distance 15.
The certificate also proves two encoded qubits and accepts the stored weight-15 logical witnesses.
The theorem `QldpcVerification.Bicycle262.parameters` gives both exact distances.

The generic interface works for any finite `k` and avoids enumerating all nonzero logical classes.
The current input generator supports cyclic two-block codes with `k = 2`.
For this case, it chooses two distinct classes that reach the target and exports paired witnesses.
Saved Python class labels, orbit assumptions, and reported bounds remain outside the trusted proof.
Lean independently checks every expanded representative and identifies its class from the certified coordinates.
An optimized theorem for orbit generators can later replace this expansion when certificate size becomes a bottleneck.

## Prior work that changes the plan

The basic arbitrary-k overlap argument and its ceiling already occur in
[Audoux and Couvreur, On tensor products of CSS Codes, Corollary 2.11 and Remarks 2.12–2.13](https://arxiv.org/html/1512.07081v3).
The relevant hypotheses concern families representing the required dual homology classes.
The tensor-product theorem has additional hypotheses, which must remain explicit when that theorem is used.
Formalization and certificate checking are useful contributions without claiming this bound as new mathematics.

[Jochym-O'Connor, Kubica, and Yoder's disjointness framework](https://arxiv.org/abs/1710.07256)
provides a related support-counting language.
[Bostanci and Kubica, The disjointness of stabilizer codes](https://arxiv.org/abs/2108.04738)
relate weighted representatives to a linear program in Theorem 5.
Their Proposition 8 also supports the use of pure CSS representatives in the corresponding pure logical class.
Keep the class-specific values, since replacing them with one global minimum can weaken a useful bound.

A full disjointness linear program has exponentially many candidate representatives.
Search a restricted family, then export a finite rational certificate for Lean.
A failed search proves no lower bound beyond the certificates that actually pass.
It also does not establish that the code lacks a stronger packing.

For reported exact targets `D_X,D_Z`, the packing screen must retain integer rounding.
The necessary conditions are `(D_X-1)*D_Z < n` and `(D_Z-1)*D_X < n`.
Passing them does not construct a certificate or validate either reported target.
The old product-ratio exclusion was too strong.
See [CERTIFICATES.md](CERTIFICATES.md#ceiling-when-exactness-is-possible) for the derivation and scope.
Do not spend large search budgets on a certificate route that cannot reach the target.

### Component decomposition and logical coordinates

The component milestone formalizes mathematics with explicit prior coverage.
The following sources identify the closest statements and their relation to this project's results.

| Lean result | Prior statement | Correspondence and scope |
| --- | --- | --- |
| Cyclic block decomposition and exact component distance | [Wang and Pryadko (2022), Statement 4, published Section 3.1](https://www.mdpi.com/2073-8994/14/7/1348), also [preprint Section III-A, page 4](https://arxiv.org/pdf/2203.17216v1) | If `a(x)=a0(x^c)`, `b(x)=b0(x^c)`, and `m=c*l`, the code splits into `c` identical independent GB blocks, with `k=c*k0` and `d=d0`. Taking `c=gcd(s,t,m)` for binomials is a specialization; the reduced connectivity follows from the integer gcd calculation. |
| Both ranks `m-c` and encoded dimension `2c` | [Panteleev and Kalachev (2021), Section 4.3, Proposition 1, equation (14), page 11](https://quantum-journal.org/papers/q-2021-11-22-585/pdf/) | For binary GB codes, `k=2*deg(gcd(a,b,x^m-1))`. Its proof computes both CSS check-matrix ranks. The binomial gcd has degree `c`, giving our formulas without an odd-length assumption. |
| Product homology, additive dimension, and exact distance | [Audoux and Couvreur, Proposition 1.10](https://arxiv.org/html/1512.07081v3) | For based chain complexes, homology splits over a direct sum, dimensions add, and distance is the minimum of the component distances. Identical nonempty copies recover our equality. The statement also applies to the dual complex. |
| Unit exponent substitutions and independent monomial shifts | [Arnault, Gaborit, and Saussay (2025), Proposition II.6](https://arxiv.org/html/2507.21237v1) | These preserve the code parameters through Hamming isometries. The opening of Section VII also states reduction to components with `gcd(s,t,m)=1`; it does not give the full component-count and permutation formula there. |

Audoux and Couvreur's proof of Proposition 1.10 uses the same restriction and zero-extension argument as the Lean distance theorem.
Their following remark also explains why an algebraic direct-sum splitting can change distance if the chosen basis does not respect the splitting.
Our explicit qubit permutation and Hamming-weight proofs supply that required basis compatibility.
Here a direct sum means independent physical code blocks, whose logical counts add.
It is a different construction from the homological tensor-product codes studied elsewhere in that paper.

The arbitrary-k coverage construction has standard dual-basis foundations.
[Hatcher, Algebraic Topology, Section 3.1, pages 198–199](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf)
identifies cohomology over a field with the dual of homology.
[Audoux and Couvreur, Theorem 2.8](https://arxiv.org/html/1512.07081v3)
also uses paired logical bases with identity pairing.
Extending each detector and witness by zero in its own component gives `c*k` independent paired coordinates.
This last construction is a direct linear-algebra consequence of those principles.
Our `CoverageCertificate` interface packages the finite witnesses, pairing, and dimension bound for Lean to check.

For logical coordinates beyond binomial GB codes,
[Davenport, Blue, and Chuang (2026), Section 4.2.2, Theorem 4.3, and Section 4.2.3](https://arxiv.org/pdf/2606.05044)
construct explicit logical quotient bases, including even circulant sizes and repeated polynomial factors.
Their Chinese remainder theorem components are algebraic factors, not physical connected components.
Their basis construction is useful guidance for broader certificates; it does not by itself supply a qubit permutation or preserve Hamming weight.

These matches support attribution of the component mathematics and its certificate construction.
The project's contribution is the Lean proof, explicit matrix recognition and qubit transport, reusable certificate interfaces, and checked applications.
This search does not establish historical priority or a first formalization claim.

## Family adapters and concrete targets

The shared `RotatedSurfaceMatch.parameters` theorem now accepts `529-1-23` and `961-1-31`.
Every original row matches a canonical face under an explicit qubit map.
Inverse row maps prove that both submitted row families cover all canonical faces.
The upstream theorem then gives one encoded qubit and both exact distances of 23 and 31, respectively.
A shared formula for the row maps can eventually replace repeated finite recognition proofs.

Treat toric variants separately.
QECLean's standard L-by-L toric construction uses `2*L^2` qubits.
The board's rotated toric construction can use `L^2` qubits.
The name and parameters alone do not establish code equivalence.
For `256-2-16`, prove an appropriate equivalence or use the general packing certificate route.

For weight-four generalized bicycle codes, investigate the lattice description in
[Wang and Pryadko, Distance Bounds for Generalized Bicycle Codes, Section 3.5](https://www.mdpi.com/2073-8994/14/7/1348).
It can offer a structural proof when orbit packing leaves a gap.
The concrete target `562-2-23` has cyclic length 281 and binomial supports
`x^158(1+x^7)` and `x^135(1+x^145)`.
After proving the normalization and code equivalence, the relevant lattice congruence is
`7*u + 145*v = 0 mod 281`.

Lean now proves that the integer pair `(9,-14)` has L1 norm 23 and satisfies that congruence.
It also excludes every nonzero solution with L1 norm at most 22.
The generic closed-trail extraction and displacement lower-bound theorems pass the kernel.
The submitted row recognition, both exact ranks, and the final code-distance theorem also pass.
The ranks use a connected-incidence theorem and the inverse `241*7 = 1 mod 281` rather than numerical pivot checks.
The complete theorem is `QldpcVerification.Bicycle562.parameters`.
It proves two encoded qubits and both exact distances of 23.
The separate rank theorems prove ranks 280 and 280.
Current status and compute limits are in `data/bicycle-evaluation/README.md`.

[Arnault, Gaborit, and Saussay, (2,2)-GB Codes: Classification and Comparison with weight-4 Surface Codes](https://arxiv.org/html/2507.21237v1)
give a more direct guide for generalizing this proof.
Proposition II.6 supplies normalization transformations.
Theorem II.7 and Corollary II.8 give the shortest-Manhattan-vector lower bound under explicit size and coprimality hypotheses.
Lemma III.2 and Corollary III.3 connect zero lifted displacement to square-face boundaries for simple cycles.
Their even-length constructions also show why odd-period detector arguments must not become a restriction of the general interface.

`Lattice/Winding.lean` now supplies the period-aware bridge.
An integer lift separates each edge's step into a vertex potential difference and a multiple of the cyclic period.
The winding labels record that carry and the vertical step modulo two.
Lean proves that zero-displacement closed walks have zero labels.
The existing coverage theorem then identifies the associated binary chains as boundaries.
This proof uses certified linear algebra instead of a separate formalization of planar filling.

The submitted `562-2-23` proof now uses those winding labels on both sides.
`EvenBicycle16.parameters` also proves `[[16,2,4]]` for the construction `GB(1+x,1+x^3,8)`.
Both ranks equal 7, and Lean proves that raw block parities miss a logical which the winding coordinate detects.
This construction regression is separate from the challenge's `16-2-4` JSON entry.
That milestone verified five submitted instances, plus this additional construction.
Its historical records are in `data/winding-evaluation/`.

The generic lift admits even and odd positive cyclic lengths.
The next family-level milestone is now complete for `GB(1+x,1+x^a,m)` with any positive `m` and natural `a`.
`Bicycle/Normalized.lean` constructs paired winding witnesses, proves complete coverage, and proves both ranks equal `m-1`.
Its QECLean homological code has two logical coordinates.
The distance theorem needs only a lower bound for nonzero solutions of `u+a*v = 0 mod m`.
The paper's separate planar filling argument is not needed for this proof through linear algebra.

`Bicycle/Normalization.lean` proves weight-preserving equivalence under independent monomial shifts and multiplication of cyclic indices by a unit.
`Bicycle.Match` transfers ranks, logical operators, and distance to submitted matrices through surjective row maps.
This covers binomial pairs whose first difference is a cyclic unit.
Connected pairs in which neither individual difference is a unit remain outside this normalization adapter.
For example, differences 2 and 3 jointly generate the cyclic group of length 6, but neither difference is invertible.

The generator `scripts/gen_bicycle_family.py` recognizes the current two-block cyclic row order and emits sparse row checks, logical witnesses, and a finite lattice exclusion.
Lean checks every emitted claim.
No per-instance rank or coverage certificate is needed.
The generator currently requires four distinct positions per row and equal stored X and Z witness weights matching the claimed distance.
The mathematical row interface allows arbitrary surjective row labels; recognizing more input orders is a separate generator extension.

The new `Bicycle362.parameters` proves `[[362,2,19]]`, with both ranks 180.
`Bicycle262Lattice.parameters` independently recovers `[[262,2,15]]`, agreeing with the earlier weighted packing proof.
`Bicycle562Family.parameters` recovers `[[562,2,23]]` through shared family coverage.
The even-length `[[16,2,4]]` regression is proved to use exactly the earlier construction's matrices.
An even-length, even-step regression `GB(1+x,1+x^2,8)` proves `[[16,2,3]]`.
Lean also proves that naive dual winding coordinates miss a logical in that example.
The family theorem instead transfers the proved primal coordinates through an axis swap and vertex inversion.
Neither construction regression is counted as another submitted instance.
The initial family records remain in `data/family-evaluation/`.

The current theorem and emitter also accept all thirteen remaining entries that match the recorded checkout's cyclic row convention.
The batch adds `4-2-2`, `58-2-7`, `82-2-9`, `100-2-10`, `110-2-10`, `122-2-11`, `170-2-13`, `226-2-15`, `278-2-16`, `298-2-17`, `346-2-18`, `422-2-20`, and `454-2-21`.
Every instance has both exact ranks, two encoded qubits, and both exact distances.
The sixteen matching bicycle entries and the three surface entries give nineteen submitted instances.
The scan concerns the current row convention and recorded checkout, rather than all possible bicycle representations.

`Lattice/Connectivity.lean` now proves exact connected incidence rank and connectivity from `gcd(s,t,m)=1`.
`Bicycle/Connected.lean` uses these results to prove both ranks `m-1` and two encoded qubits for `GB(1+x^s,1+x^t,m)`.
Its QECLean homology also has dimension two.
The steps 2 and 3 at cyclic length 6 supply a regression where neither step is a unit.
The steps 2 and 4 at length 6 admit a nonconstant invariant function, which tests the need for the hypothesis.
The broader model recovers the normalized matrices at `s=1`.
These structural results retain their original records in `data/bicycle-batch-evaluation/`.

`Bicycle/PeriodBasis.lean` and `Bicycle/JointCoverage.lean` now complete logical coverage under joint coprimality.
After removing the common integer factor, primitive steps `a,b` admit Bézout coefficients with `a*p+b*q=1`.
The adapted labels are the period carry and the transverse quantity `q*u-p*v` modulo two.
Closed walks with displacements `(m*p,m*q)` and `(b,-a)` give the identity pairing.
The rank bound then proves complete logical coordinates for every positive cyclic length and either parity of the steps.
The same coverage is available for QECLean's homological code.

Zero-displacement closed walks are boundaries.
The distance theorem keeps the original lattice relation `s*u+t*v = 0 mod m` and the original L1 norm `|u|+|v|`.
The change of logical coordinates does not replace the physical edges or their weights.
`Connected.Match.parameters` transfers the ranks and both bounds to recognized matrices and accepts exact-weight upper witnesses.
`Lattice/JointFiniteBound.lean` turns finite exclusions into the required integer lattice bounds for either pair of steps.

The nonunit examples at `(m,s,t)=(6,2,3)` and `(15,6,10)` have exact parameters `[[12,2,2]]` and `[[30,2,3]]`.
The latter tests a common integer factor that remains a unit modulo the cyclic length.
The one-vertex, zero-step model has parameters `[[2,2,1]]` and tests the zero-gcd branch.
Lean also proves that naive carry and vertical parity miss a logical in the twelve-qubit example.
These examples are construction regressions, so the submitted-instance inventory remains nineteen.
The current Python emitter retains its unit-first restriction.
The general matrix interface accepts any proved qubit and surjective row maps.
Those records remain in `data/joint-evaluation/`.

The disconnected extension is also complete.
The vertex map `(r,v) ↦ r+c*v` separates `GB(1+x^(c*a),1+x^(c*b),c*l)` into `c` identical component codes.
Lean proves the corresponding qubit bijection and both block-matrix equalities.
Taking `c=gcd(s,t,m)` proves that the reduced code has jointly generating steps.
Both ranks equal `m-c`, and the encoded dimension is `2c`.
Product certificates give complete logical coordinates for every component.
The reusable `Components.coverage` theorem takes `c` copies of an arbitrary-k certificate and produces `c*k` coordinates.
The QECLean homological code also receives this coverage.

The exact-distance theorem uses a nonempty product of identical components.
Every global nontrivial logical has a nontrivial restriction to a component.
A component witness extends by zero with its weight unchanged.
Both CSS distances therefore equal their corresponding component distances.
The `GB(1+x^4,1+x^6,12)` construction is proved to be two copies of the existing `[[12,2,2]]` code.
Its exact parameters are `[[24,4,2]]`, with both ranks 10 and four complete logical coordinates.
Lean also checks the single-component case, zero-step structure, and a logical missed by global block parity.
The submitted-instance count remains nineteen.
Current records are in `data/components-evaluation/`.

### Boundary construction, grafting, and merges

The user's `722-8-20` and `566-18-20` entries require distinct construction proofs.
The first uses open boundaries and directional condensation.
The second uses lattice grafting and qubit removal.
Its construction note describes stabilizer row operations, CNOT fan-out, and deletion of a disentangled qubit.
These operations preserve encoded dimension under the stated pivot conditions, but CNOT gates can change logical Hamming weights.
The earlier description of this reduction as a merge was too broad.
The qubit-permutation distance theorem does not apply to the CNOT reduction.

[Liang, Eberhardt, and Chen, Planar quantum low-density parity-check codes with open boundaries, Sections III.1–III.2](https://arxiv.org/html/2504.08887v4)
provides the closest construction guide.
First retain the bulk checks supported within the patch.
Then find local operators near the boundary that commute with those checks.
Choose commuting boundary checks, and complete the corners to eliminate unwanted local logical operators.
Truncating the bulk checks alone does not establish that this completion is sufficient.
Section III.5 gives the lattice-grafting procedure and explicitly includes a separate distance check before accepting each removal.
It does not prove that arbitrary grafting preserves distance.

[Liang, Yang, Iosue, and Chen, Operator algebra and algorithmic construction of boundaries and defects, Theorem 10 and Section 4](https://arxiv.org/html/2410.11942v5)
develops the boundary-operator and completion framework in more detail.
Its algorithms can guide certificate generation.
Lean can first check the finite resulting matrices and certificates without formalizing the entire anyon classification algorithm.
This is an implementation choice, not an additional distance theorem from the paper.

[Eberhardt, Pereira, and Steffan, Pruning qLDPC codes, Theorem 1 and Proposition 1](https://arxiv.org/html/2412.04181v1)
does give exact distance preservation for a restricted construction.
It requires separate univariate polynomials `A(x)` and `B(y)` dividing their respective cyclic moduli.
The resulting open code has half the periodic code's logical dimension.
Applying it to a mixed-variable target requires a proved equivalence satisfying those hypotheses.
[Delfosse, Iyer, and Poulin, Theorem 3.2 and Section 4](https://arxiv.org/html/1606.07116v1)
provides relative-homology tools for genuine surface codes with mixed boundaries.
Using that surface-code theorem for a BB construction also requires an appropriate identification.

[Cowtan and Burton, CSS code surgery as a universal construction](https://arxiv.org/html/2301.13738v6)
guides actual merges along shared logical operators.
Definitions 3.4 and 5.1 specify basis-preserving maps and pushouts, while Lemma 5.4 fixes physical bases up to qubit and check permutations.
The separation hypothesis in Definition 5.12 controls which logical operators lie in the interface.
Lemma 6.7 gives one distance bound under an additional logical-dimension condition.
Definition 6.8 retains a separate distance hypothesis for the other side.
Appendices F and G show that merges can lower distance and introduce extra logical classes.
A merge proof must therefore establish its dimension and distance hypotheses explicitly.

Use limited certification of small concrete examples to prepare the logical-lifting investigation.
Check commutation, encoded dimension, paired logical coordinates, and upper witnesses for those examples.
The recorded `722-8-20` witnesses give only `d_X ≤ 23` and `d_Z ≤ 20`.
For `566-18-20`, they give only `d_X ≤ 20` and `d_Z ≤ 21`.
These are upper bounds, not proofs of distance 20.
Prove generic boundary and grafting operations with explicit hypotheses, then seek finite certificates or structural arguments for lower bounds.
The final matrices can receive direct certificates even when the historical sequence of grafting moves is unavailable.

## Other routes and stopping rules

Keep solver-proof replay as a separate route for codes without a useful structural certificate.
A solver's numerical verdict and a randomized search are not kernel proofs.
A checked propositional proof also needs a Lean theorem connecting its encoding to CSS logical operators.

[Lean-QEC](https://arxiv.org/abs/2605.16523) supplies useful encoding ideas.
Its reported computation route has a different trust boundary from this project's kernel-only requirement.
[lrat-catcher](https://arxiv.org/abs/2607.00815) describes a kernel-checking variant.
Inspect and pin that variant before use, and audit the final coding-theory theorem's axioms.
Do not infer soundness of the QEC encoding from soundness of the propositional checker alone.

For generic upper bounds, consider algebraic cleaning and correctable-region partitions.
[Baspin and Krishna](https://quantum-journal.org/papers/q-2022-05-13-711/) provide a route through graph structure.
The [Bravyi–Poulin–Terhal tradeoff](https://arxiv.org/abs/0909.5200) requires geometric locality hypotheses.
It does not apply to every sparse check matrix.
These upper bounds can guide certificate searches and expose impossible targets.

The finite coverage, higher-k instance, and additional surface milestones are complete.
The bicycle lattice milestone is also complete.
The winding-coordinate extension and its even-length regression are complete.
Parametric coverage, unit-step normalization, and the three submitted lattice applications are also complete.
The thirteen-instance batch and joint-connectivity rank and dimension milestone are complete.
Logical coverage and both lattice distance bounds under joint coprimality are also complete.
The small nonunit examples pass exact distance and rank proofs.
Disconnected component decomposition, arbitrary-k product coverage, and exact distance transfer are also complete.
The next main milestone is logical-lifting research for an elementary qubit-removal operation.
Limited certification of small examples prepares that work.
The new investigation has not started.
The remaining directions are:

1. Construct concrete logical lifts, prove nontriviality and weight bounds, and test preservation hypotheses on small preserving and distance-losing examples.
2. Apply useful boundary and grafting criteria to the user's entries, or use direct certification where lifting is insufficient.
3. Extend input recognition for additional cyclic layouts when concrete submitted targets need it.
4. Add a kernel-checked solver proof route where structural methods remain insufficient.

Use bounded experiments to discover certificates.
Preserve every validated lighter logical as evidence.
A partial Lean bound remains a successful result when a stronger claim exceeds the available method or compute budget.

## Reproducibility and compute

Use `uv.lock`, Ruff, and the regeneration tests for all Python work.
The optional C++ accelerator builds into `.build/` from the sibling source.
It does not alter the challenge verifier.
The 61 current tests cover certificate data, exact packing arithmetic, rounded candidate screening, class coverage, tooling, and cluster configuration.
They reproduce the additional surface inputs and the bicycle data and checker propositions.
The family generator tests reproduce all seventy-two generated Lean modules for eighteen applications and reject malformed rows, witnesses, parameter claims, and unattainable lattice targets.
Six tests exercise local configuration, submission arguments, and the initial download through fake tools without contacting a cluster.
Lean also rejects six deliberately malformed certificates in `CertificateControls.lean`.

Before consolidation, the QECLean adapter's local warm rechecks took 11.50 seconds for row matching and 3.93 seconds for the final proof module.
The maximum child-process RSS values were about 4.34 GiB and 3.74 GiB.
Dependency compilation and cache downloads are excluded.
These values do not establish a cold-build speed comparison with the original kernel pilot.

Use the ignored `.local/cluster.env` file for cluster connection, scheduler, and scratch settings.
The tracked submission helper and configuration template are documented in `scripts/cluster/README.md`.
Keep toolchains, packages, and caches in the configured scratch workspace.
The first QECLean provisioning run hit the home-directory file quota, rather than the allocation's memory limit.
Its incomplete package and toolchain files were removed, which reduced the home file count below the quota.
The earlier successful Lean 4.36 workspace and its proof logs remain intact.

The bicycle finite checks passed an independent scratch-based cluster run.
The measured build took 13:08 and reached 6,212,504 KiB of maximum process RSS.
The complete allocation reached 13,074,464 KiB according to Slurm, including setup and cache work.
Do not treat these two measurements as interchangeable.
Use detached Slurm jobs for further large kernel evaluations.
A local surface recognition attempt exhausted memory and the OS killed Emacs.
If a local experiment is necessary, enforce a memory limit as well as detaching it from the session.
The earlier full build and all thirteen guarded axiom audits pass in cluster run `packing-full-replay`.
The timed build took 4:58.47 with the compiled dependency cache retained.
Its maximum process RSS was 6,752,660 KiB, while Slurm reported 11,764,172 KiB for the allocation.
These are warm replay measurements, not a cold dependency benchmark.

The lattice milestone also passes a sequential local rebuild and all twenty-two guarded audits.
Detached systemd services enforced `MemoryMax=5G` and `MemorySwapMax=512M`.
The final build and audit took 280.09 seconds with the dependency cache retained.
Replacing numerical rank evaluation with a connected-incidence proof made this run feasible within the enforced budget.
The cluster SSH connection expired before this milestone, so this result has no independent cluster replay yet.

The later winding extension passes a changed-module source rebuild and all thirty-three main guarded audits.
Its twelve focused winding guards and nine focused bicycle guards also pass.
The sequential rebuild and audits took 38.52 seconds with a 5 GiB memory cap and a 128 MiB swap cap.
Maximum child-process RSS was 3,862,012 KiB, while the rounded cgroup memory peak was 672.4 MiB.
The dependency caches and unchanged project modules were retained.
These measurements do not describe a cold dependency build.
Those historical records are in `data/winding-evaluation/`.

The family milestone passes a source rebuild of all twenty-eight changed or new build targets, including the package root.
Its 67 main guarded targets, 34 focused family guards, 12 winding guards, and 9 bicycle guards all pass.
The sequential source rebuild and four audits took 224.21 seconds under a 5 GiB memory cap and a 128 MiB swap cap.
Maximum child-process RSS was 4,970,568 KiB; the journal reports a rounded charged-memory peak of 1.8 GiB.
The dependency caches and other project modules were retained, so this is not a cold dependency benchmark.
No cluster job was submitted.
Those records remain in `data/family-evaluation/`.

The later thirteen-instance batch passes all fifty-three sequential build targets and five guarded audits.
It took 358.46 seconds under the same 5 GiB memory cap and 128 MiB swap cap.
Maximum child-process RSS was 4,722,368 KiB.
The journal reports a rounded charged-memory peak of 1.6 GiB.
The generic family and dependency caches were retained.
The connectivity integration rebuilt its two new modules and the root from cleared outputs, then passed all six audits in 37.69 seconds.
Maximum child-process RSS was 3,832,408 KiB, while the journal reports a rounded charged-memory peak of 632.6 MiB.
The integrated main audit contains 118 unique targets.
The focused audits contain 39 batch targets, 12 connectivity targets, 34 family targets, 12 winding targets, and 9 bicycle targets.
These focused counts overlap with the main audit.
Those batch and connectivity records remain in `data/bicycle-batch-evaluation/`.

The joint-coverage milestone passes a source rebuild of six new modules and the changed root, followed by all seven guarded audits.
The main audit contains 141 unique targets, including 23 new joint-step targets.
The run took 65.34 seconds under a 5 GiB memory cap and a 128 MiB swap cap.
Maximum child-process RSS was 4,064,732 KiB.
The journal reports a rounded charged-memory peak of 886.2 MiB and 64.346 seconds of CPU time.
Existing project outputs and dependency caches were retained.
This is not a cold dependency benchmark, and no cluster job was submitted.
Those source hashes, exact commands, and scope remain in `data/joint-evaluation/`.

The component milestone passes a source rebuild of eight new modules and the changed root, followed by all eight guarded audits.
The main audit contains 181 unique targets, including forty new component targets.
The run took 76.34 seconds under a 5 GiB memory cap and a 128 MiB swap cap.
Maximum child-process RSS was 3,895,816 KiB.
The journal reports a rounded charged-memory peak of 697.6 MiB and 75.510 seconds of CPU time.
Other project outputs and dependency caches were retained, and no cluster job was submitted.
The `[[24,4,2]]` example also passed an independent enumeration of both binary kernels modulo stabilizers.
Current records are in `data/components-evaluation/`.

Historical board counts and numerical experiments remain in `CHECKS_AND_RESULTS.md`.
They refer to their recorded snapshots and are not current claims about the live leaderboard.
