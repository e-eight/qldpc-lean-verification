# Research plan and prior work

Updated 2026-10-30.
The QECLean foundation, arbitrary-k coverage, weighted packing, and cyclic bicycle component milestones are complete.
See [README.md](README.md#proved-results) for the current inventory and [CHECKS_AND_RESULTS.md](CHECKS_AND_RESULTS.md) for dated evidence.
This file states research priorities, mathematical hypotheses, and limits of the available methods.

## Next milestone: logical lifting

Investigate one elementary qubit-removal operation before attempting a general boundary theorem.
Limited certification of small examples with QECLean will prepare this investigation.
No new logical-lifting proof work has started.

A proposed sufficient criterion compares old and new logical operators directly.
For every nontrivial new logical `x'`, construct a nontrivial old logical `x` with `weight(x) ≤ weight(x')`.
An old lower bound `D` then transfers to the new code.
An explicit new witness of weight `D` proves exact distance on that side.
Apply the criterion separately to the X and Z logical spaces.
For overall quantum distance `D`, lower bounds on both sides and one weight-`D` logical witness suffice.
This criterion is a research route, not an implemented Lean theorem.

The useful work is deriving those lifts from checkable hypotheses about a concrete boundary operation.
A theorem that merely assumes all the desired lifts exist leaves that task unresolved.
Pruning can change encoded dimension, so the criterion does not require a bijection between the full logical spaces.
CNOT operations can change physical weights while still preserving minimum logical weight in a particular construction.
A weaker proved weight bound can also supply a useful partial distance result.

Use the following pilot sequence:

1. Write the matrix form of a single qubit-removal move and its pivot conditions.
2. Construct logical lifts, prove nontriviality, and derive weight changes on each CSS side.
3. Test candidate preservation hypotheses on small preserving and distance-losing examples, with QECLean certificates for their concrete claims.
4. Apply useful criteria to larger submitted matrices; use direct certificates where lifting remains insufficient.

The submitted `722-8-20` and `566-18-20` entries remain targets, not proved distance-20 instances.
A transfer argument still needs a proved bound for its reference code.
Numerical search stability supplies no such lower bound.

## Foundation and existing interfaces

Use [QECLean](https://github.com/Stavan-Jain/QECLean/tree/fed020a7e6be12825196cbee7bbc1ba56554158c)
for stabilizer algebra, homological codes, logical correspondence, and existing family theorems.
Keep the pinned dependency and application certificates here.
The active package in `lean/` imports no code from the independently audited `archive/QldpcCert` package.

`Input/MatrixSpec.lean` states the submitted matrix claims.
`Input/Homological.lean` proves agreement with QECLean's cycle and boundary predicates.
New generic theory uses QECLean's definitions; input recognition connects those results to submitted matrices.

`Overlap.lean` provides weighted support counting.
`Coverage.lean` constructs complete logical coordinates from paired witnesses and a dimension bound for any finite `k`.
`Components.lean` combines certificates across independent components, and `CoverageTransport.lean` transfers them through qubit permutations.
The mathematical packing setup and the finite checker obligations belong in [CERTIFICATES.md](CERTIFICATES.md).

The packing emitter `scripts/gen_orbit_instance.py` currently supports cyclic two-block codes with `k=2`.
The family emitter `scripts/gen_bicycle_family.py` requires cyclic row order and a unit first difference.
The general matrix interfaces accept proved qubit equivalences and surjective row maps beyond those emitter restrictions.
Extend automatic recognition when a concrete submitted target needs it.

## Prior work that guides the proofs

The arbitrary-k overlap argument and its integer ceiling occur in
[Audoux and Couvreur, Corollary 2.11 and Remarks 2.12–2.13](https://arxiv.org/html/1512.07081v3).
Their tensor-product theorem has additional hypotheses that must remain explicit.
Formalization and certificate checking do not establish newness of the underlying bound.

[Jochym-O'Connor, Kubica, and Yoder's disjointness framework](https://arxiv.org/abs/1710.07256)
provides a related support-counting language.
[Bostanci and Kubica, Theorem 5](https://arxiv.org/abs/2108.04738) relates weighted representatives to a linear program.
Their Proposition 8 supports pure CSS representatives in the corresponding pure logical class.
Keep class-specific values because a global minimum can weaken the bound.

A full disjointness program has exponentially many candidate representatives.
Search a restricted family and export finite rational certificates for Lean.
A failed search establishes no impossibility result for stronger packing certificates.
Retain the strict integer threshold in [CERTIFICATES.md](CERTIFICATES.md#ceiling-when-exactness-is-possible).
The old product-ratio exclusion dropped rounding and was too strong.
The [corrected numerical screen](data/candidate-screening-2026-10-30/) supplies necessary conditions only, not distance proofs.

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

### Bicycle lattice and normalization guidance

[Wang and Pryadko, Section 3.5](https://www.mdpi.com/2073-8994/14/7/1348)
provides a lattice description for weight-four GB codes.
[Arnault, Gaborit, and Saussay](https://arxiv.org/html/2507.21237v1)
gives normalization transformations in Proposition II.6 and Manhattan-vector bounds in Theorem II.7 and Corollary II.8.
Those distance statements have explicit size and coprimality hypotheses.
Lemma III.2 and Corollary III.3 relate zero lifted displacement to square-face boundaries.

Our winding and joint-connectivity proofs use paired coordinates and finite linear algebra to identify boundaries.
The distance calculation retains the original physical edges and L1 norm.
Neither an algebraic change of coordinates nor normalization alone permits replacement by shorter physical paths.
The theorem covers either parity of the positive cyclic length; emitter limitations are stated separately above.

## Boundary construction, grafting, and merges

The `722-8-20` entry uses open boundaries and directional condensation.
The `566-18-20` entry uses lattice grafting and qubit removal.
Its note describes stabilizer row operations, CNOT fan-out, and deletion of a disentangled qubit.
Under the pivot conditions, these operations preserve commutation and encoded dimension.
They need additional weight arguments for distance.
The existing qubit-permutation theorem does not apply to the CNOT reduction.

[Liang, Eberhardt, and Chen, Sections III.1–III.2](https://arxiv.org/html/2504.08887v4)
provides the closest construction guide.
Retain supported bulk checks, derive commuting boundary operators, and complete the corners to remove unwanted local logical operators.
Bulk truncation alone does not establish sufficient completion.
Section III.5 gives lattice grafting with a separate distance check before accepting each removal.
It does not prove preservation for arbitrary grafting.

[Liang, Yang, Iosue, and Chen, Theorem 10 and Section 4](https://arxiv.org/html/2410.11942v5)
develops boundary operators and completion in more detail.
Its algorithms can guide certificate generation.
Lean can check finite matrices and certificates before a formalization of the entire anyon classification algorithm.
This is an implementation choice, not a distance theorem from the paper.

[Eberhardt, Pereira, and Steffan, Theorem 1 and Proposition 1](https://arxiv.org/html/2412.04181v1)
proves exact distance preservation for a restricted pruning construction.
Separate univariate polynomials `A(x)` and `B(y)` must divide their respective cyclic moduli.
The open code has half the periodic code's logical dimension.
These are sufficient hypotheses of that theorem, not requirements for every possible distance-preserving construction.
A broader argument can use logical lifting or direct packing certificates.

[Delfosse, Iyer, and Poulin, Theorem 3.2 and Section 4](https://arxiv.org/html/1606.07116v1)
provides relative-homology tools for surface codes with mixed boundaries.
Applying that surface-code theorem to a BB construction requires an appropriate identification.
Geometric resemblance alone does not establish it.

[Cowtan and Burton](https://arxiv.org/html/2301.13738v6) guides merges along shared logical operators.
Definitions 3.4 and 5.1 specify basis-preserving maps and pushouts.
Lemma 5.4 fixes physical bases up to qubit and check permutations.
Definition 5.12 imposes a separation condition on logical operators in the interface.
Lemma 6.7 needs an additional logical-dimension condition for its distance bound.
Definition 6.8 retains a separate distance hypothesis for the other side.
Appendices F and G show that merges can lower distance and introduce extra logical classes.
A merge proof must establish its dimension and distance hypotheses explicitly.

| Submitted target | Stored X witness weight | Stored Z witness weight | Encoded dimension claim |
| --- | --- | --- | --- |
| `722-8-20` | 23 | 20 | 8 |
| `566-18-20` | 20 | 21 | 18 |

These are submitted witness weights and dimension claims awaiting their own Lean certificates.
They provide no lower bound of 20.
Final matrices can receive direct certificates even when the historical grafting sequence is unavailable.

## Later directions and stopping conditions

Treat toric variants separately from the surface adapter.
QECLean's standard L-by-L toric code uses `2*L^2` qubits, while the board's rotated variant can use `L^2`.
The submitted `256-2-16` therefore needs an equivalence proof or a suitable packing certificate.

Keep solver-proof replay as a route for codes without useful structural certificates.
A solver's numerical verdict is not a kernel proof.
The propositional encoding also needs a theorem connecting it to CSS logical operators.
[Lean-QEC](https://arxiv.org/abs/2605.16523) supplies encoding ideas, with a different reported trust boundary.
Inspect and pin the kernel-checking variant described by [lrat-catcher](https://arxiv.org/abs/2607.00815) before using it.
Audit the final coding-theory theorem's axioms, not only the propositional checker.

For generic upper bounds, consider algebraic cleaning and correctable-region partitions.
[Baspin and Krishna](https://quantum-journal.org/papers/q-2022-05-13-711/) gives a route through graph structure.
The [Bravyi–Poulin–Terhal tradeoff](https://arxiv.org/abs/0909.5200) requires geometric locality and does not cover every sparse check matrix.
These bounds can guide searches and expose impossible targets under their hypotheses.

Use bounded experiments, preserve lighter logical witnesses, and keep every proved partial bound.
Choose a different route when an explicit obstruction defeats the current certificate method.
Failure of a bounded search alone is not such an obstruction.

## Reproducibility and compute

Use the locked Python environment, Ruff, and regeneration tests described in [README.md](README.md#python-environment).
The numerical candidate screen records its input revision and hashes separately from proof evaluations.
The JSON parser and all certificate searches remain outside Lean.

Run large Lean evaluations in detached, resource-limited allocations.
Use the ignored `.local/cluster.env` configuration and [cluster helper](scripts/cluster/README.md) for Slurm.
Detachment alone does not cap memory use.

[CHECKS_AND_RESULTS.md](CHECKS_AND_RESULTS.md) owns the dated measurements and historical commands.
Each evaluation directory records source hashes, dependency pins, commands, outcomes, and the measurement scope.
The latest [component evaluation](data/components-evaluation/) used retained dependency caches, not a cold build.
Historical board counts and numerical results describe their recorded snapshots.
They are not current claims about the live leaderboard.
