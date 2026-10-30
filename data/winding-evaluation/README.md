# Period-aware bicycle winding proof

The winding bridge passes the submitted `562-2-23` proof and the even-cyclic-length construction `GB(1+x,1+x^3,8)`.
The submitted matrices retain two encoded qubits, both ranks 280, and both exact distances of 23.
The construction regression has 16 physical qubits, two encoded qubits, both ranks 7, and both exact distances of 4.
It is separate from the challenge's `16-2-4` JSON, for which this milestone proves no equivalence.
The inventory remains five verified submitted instances, plus this additional construction regression.

The mathematical guide is [Arnault, Gaborit, and Saussay, (2,2)-GB Codes: Classification and Comparison with weight-4 Surface Codes](https://arxiv.org/html/2507.21237v1).
Theorem II.7 and Corollary II.8 give the lattice distance bound under their stated size and coprimality hypotheses.
Lemma III.2 and Corollary III.3 connect zero lifted displacement to square-face boundaries for simple cycles.
The even regression is the `r = 2` case of the second family in Proposition IV.1.

`Lattice/Winding.lean` constructs the integer lift symbolically for any positive cyclic length.
Each oriented edge satisfies an integer identity:

```text
a * horizontal_step + b * vertical_step
  = potential(target) - potential(source) + period * carry
```

The two winding labels are the carry and the vertical step, reduced modulo two.
Lean proves that a closed walk with zero displacement has zero labels.
A complete logical-coverage certificate then proves that the walk's binary chain is a boundary.
This supplies the zero-lift-to-boundary implication through certified linear algebra rather than a separate planar filling proof.

The generalized distance theorem accepts any checked labels with this zero-displacement property.
A detected trail gives a nonzero integer relation with L1 norm at most the original chain's weight.
The lattice separation bound supplies the lower distance bound.
The existing stored witnesses give the matching upper bounds for `562-2-23`.
Its odd-period migration theorem transfers the original block-parity coverage to the new winding labels.

The even construction supplies paired winding witnesses and uses the structural incidence-rank theorem.
Its finite lattice exclusion checks only `[-3,3]^2`.
Lean proves that the eight-edge horizontal loop is nontrivial despite having both raw block parities zero.
The first winding coordinate detects that loop.
This theorem is `EvenBicycle16.raw_parity_misses_logical`.
Both CSS sides also have zero-displacement-to-stabilizer theorems.

Incidence recognition, complete logical coverage, and lattice separation remain explicit proof obligations.
This milestone does not yet construct coverage certificates parametrically or normalize arbitrary binomial input matrices automatically.
It therefore does not yet formalize the paper's full unconditional family theorem.
The next mathematical step is to discharge those obligations uniformly for a normalized family.

The five changed or new module outputs were cleared before the sequential source rebuild.
Other project modules and the external dependency caches were retained.
The complete package build, 33 main guarded audits, 12 focused winding guards, and 9 focused bicycle guards pass.
The new results use only `propext`, `Classical.choice`, and `Quot.sound`.
The retained closed norm-23 witness remains axiom-free.

The rebuild and audits took 38.52 seconds in a detached systemd service.
The service enforced `MemoryMax=5G`, `MemorySwapMax=128M`, one CPU of aggregate bandwidth, and a 300-second runtime limit.
Maximum child-process RSS was 3,862,012 KiB, including shared mappings.
The journal reports a rounded charged-memory peak of 672.4 MiB.
These are different measurement scopes and do not describe a cold dependency build.
No cluster job was submitted.

For replay with the pinned toolchain and dependency cache ready, run the following commands in a detached, memory-limited allocation:

```bash
lake -d lean build QldpcVerification
lake -d lean env lean lean/QldpcVerification/WindingAudit.lean
lake -d lean env lean lean/QldpcVerification/BicycleAudit.lean
lake -d lean env lean lean/QldpcVerification/KernelAudit.lean
```

`build-and-audit.json` records the exact sequential command used for the measurement.
`build-and-audit.log` contains its output, and `guarded-audits.log` extracts the audit output.
`evaluation.json` records the proof scope, input identity, dependency revisions, results, and measurements.
`proof-source-sha256.txt` identifies all 43 proof, manifest, and toolchain files.
The Python suite also passes all 27 tests, with Ruff and shell syntax checks passing.

Published logs replace local paths and the hostname with descriptive placeholders.
Exact logs remain under ignored `.local/proof-records/winding-evaluation/` storage.
The publication metadata preserves their original digests.
