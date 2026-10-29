# Recommendations after the QECLean proof

Updated 2026-10-29.
The QECLean adapter proves the original `225-1-15` matrices' ranks and distances.
Finite coverage certificates also complete a weighted packing proof for `262-2-15` on both CSS sides.
The structural lattice proof now verifies `562-2-23`, including both ranks of 280 and both distances of 23.
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

The unweighted overlap method has a limitation of the form `d_X * d_Z ≤ n` when it proves both exact distances.
This is a limit of the method under the stated class hypotheses.
It is not a general upper bound for arbitrary qLDPC codes.
Do not spend large search budgets on a certificate route that cannot reach the target.

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
The proved `262-2-15` instance supplies a regression target for this bridge.
The `362-2-19` entry supplies another candidate.

For the user's `722-8-20` and `566-18-20` entries, retain only justified bounds until their boundary operations are formalized.
The first uses open boundaries and directional condensation.
The second includes distance-aware merges and removed qubits.
Periodic bicycle theorems and translation arguments do not automatically cover these modifications.
A useful first result is exact structure, encoded dimension, and witnessed upper bounds.

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
Review the results with the user before choosing another target.
The remaining directions for that review are:

1. Extend the lattice adapter to more instances and more general logical coordinates.
2. Formalize the open-boundary operations needed by the user's entries.
3. Add a kernel-checked solver proof route where structural methods remain insufficient.

Use bounded experiments to discover certificates.
Preserve every validated lighter logical as evidence.
A partial Lean bound remains a successful result when a stronger claim exceeds the available method or compute budget.

## Reproducibility and compute

Use `uv.lock`, Ruff, and the regeneration tests for all Python work.
The optional C++ accelerator builds into `.build/` from the sibling source.
It does not alter the challenge verifier.
The nineteen current tests cover data stability, malformed inputs, weighted arithmetic, ceiling behavior, logical-class coverage, and local scheduler configuration.
They reproduce the additional surface inputs and the bicycle data and checker propositions.
Four tests exercise local configuration and submission arguments through a fake scheduler without contacting a cluster.
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

Historical board counts and numerical experiments remain in `CHECKS_AND_RESULTS.md`.
They refer to their recorded snapshots and are not current claims about the live leaderboard.
