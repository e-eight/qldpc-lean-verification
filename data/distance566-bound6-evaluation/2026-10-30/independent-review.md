# Independent review of the additive bound-six proof

## Verdict and reviewed snapshot

No blocking mathematical findings. The standalone evidence supports the
unconditional literal-target bounds `d_X >= 6`, `d_Z >= 6`, and an unchanged
nontrivial Pauli witness of weight twenty. Thus the overall bounds are
`6 <= d <= 20`. Exact distance twenty remains open.

The standalone modules and corrected focused audit passed. Combined package
validation remains separate and pending at this review snapshot. Its first
attempts stopped before compilation on private cached-package configuration.
This report does not claim a successful combined run.

I reviewed all 79 generated input modules, five theory/audit modules, the
exporter and tests, compact data, and the available execution evidence.
The frozen 124-entry source manifest matches current bytes and has SHA256:

```text
27875b80d70dd9e8daec469e4aeda5f4beb6a331621872a31dc47aa4f6d876f4
```

The compact certificate SHA256 is
`77c943fdc42dce81207f80e007942a0a794fba1f21efac4cdf3f585837b5e800`.
The final focused audit SHA256 is
`e2e455e2191b4efe7145f83f9eddf1eeed3ccddc40e9f013722bea2515769ffe`.
These replace the preliminary audit hashes.

## Evidence inventory label: resolved

The former `proof_inventory_sha256` field correctly identified
`proof-modules.txt`, the ordered list of 84 modules:
`c58fb506366ba2f519d66ee13044c2912fa6ed80699d5af128dcc7e69b283336`.
The separate `proof-artifacts-sha256.txt` has digest
`bb088f294fe1ff70a7b0df1fd3ca1cb26b88dc871e2b96b4a3a7c69bf3dbe871`.

The initial review interpreted the unlabeled inventory field as referring to
the artifact inventory. That interpretation is corrected here. Neither file
had incorrect bytes.

The public record now explicitly pairs `proof_modules_path` with
`proof_modules_sha256`, and `proof_artifacts_path` with
`proof_artifacts_sha256`. I verified both paths and both complete digests.
The private producer computes these fields from the intended separate files.
The low-severity labeling ambiguity is resolved. No proof source, test, or
compiled artifact needed correction.

All 84 artifact entries agree with `module-results.json`. Each module's
successful step also records the exact current source digest and compiler
command. The mathematical verdict is unchanged.

## Literal target and complete logical coverage

The proof refers throughout to `Removal566.Stage12.code`, built from the
previously checked literal target matrices. Its ranks are 274 and 274, giving
eighteen encoded qubits. No source-578 distance hypothesis enters the new
lower bounds.

I compared both cached row-mask tables with every original literal matrix row.
Both tables preserve all 274 row positions. Their checks refer directly to
`Removal566.Stage12.hx` and `.hz`, rather than a reconstructed matrix model.
The detector masks, raw supports, and separately paired witness masks match
the compact certificate. That certificate preserves the independently
reviewed exploration's two coverage objects.

`Distance566WeightedCoverage.lean:45` uses Z detectors and paired X witnesses
for primal coverage. Its dual coverage at `:59` uses X detectors and paired
Z witnesses. The syndrome orientations and identity-pairing indices are
correct. The selected X and Z detector bases need not pair to the identity
with each other.

The existing coverage theorem combines paired cycle witnesses, boundary
orthogonality, and the actual rank bound. Its coordinate kernel is exactly
the stabilizer space. The result therefore detects every nontrivial logical
class, including sums of basis classes.

I inspected all 108 coordinate-check leaves, their eighteen-way aggregations,
both complete pairing checks, and the six support/mask range gates.
Every index zero through seventeen occurs exactly once in each required
aggregation. Physical masks and supports refer to all 566 actual positions.

## Generic soundness, no-wrap gates, and finite family checks

`WeightedPackingCertificates.lean:37` projects a weighted representative to
its mask and natural multiplicity. It does not replace the multiplicity with
a row count or expand it into repeated representatives.
The class checker correctly ignores the weight only for membership purposes.

The row-table checker at `WeightedPackingCertificates.lean:54` compares every
cached mask with the actual row's support mask. The soundness theorem at `:72`
uses those equalities to reduce packed XOR checks to the existing original-row
span theorem. Neither zero syndrome nor matching logical coordinates alone
substitutes for stabilizer membership.

The decoder uses `Fin.ofNat`, but `rangeCheck` at `:17` checks every raw row
index and physical mask. The no-wrap theorem at `:30` proves that a checked
raw row index retains its value after conversion. Every family has concrete
range checks and an aggregate range theorem. Both aggregates and all
coordinate/support range facts are covered by the focused audit.
Masks and weights use unbounded natural numbers, so machine-word overflow is
not an assumption.

I parsed all 36 generated family data/check pairs and compared every literal
entry with `compact.json.gz`. The 734 X-detector and 732 Z-detector entries
retain their original supports, row witnesses, and natural weights from the
exploration export. Every representative reconstructs from its base and the
indicated literal rows. All raw indices and masks satisfy their bounds.

There are 201 row-check blocks, each containing at most eight representatives.
Every block enters its family's range and class aggregation.
Each family has nine capacity chunks. Their explicit concatenation equality
covers positions zero through 565 exactly once. Across all families there are
324 such chunks. A missing chunk cannot silently establish a global cap.

I independently recomputed the retained families' integer loads, maximum
capacities, total weights, and strict inequalities. Every family satisfies
`5 * cap < totalWeight`. Each also has a separate kernel-evaluated threshold
theorem. This preserves the ceiling needed for six without division in the
Lean lower-bound argument.

The final sector aggregators include all eighteen families in matching
detector order for class membership, range, capacity, and threshold.
X-family differences use HX rows, while Z-family differences use HZ rows.
`Distance566WeightedPacking.lean:27` correctly uses Z families to bound X
logicals, and `:40` uses X families to bound Z logicals.
Both statements quantify over every nontrivial logical vector of Stage12.

`Distance566WeightedPauli.lean:11` applies QECLean's existing CSS bridge to
both lower bounds, including mixed Pauli logicals. The upper capstones reuse
the unchanged, already checked submitted X witness. The lower and upper
claims concern the same literal homological stabilizer group.

## Exporter and tests

I explicitly rechecked the current exporter and test snapshots, rather than
the earlier preliminary versions:

```text
c48698bb07e4cbb6b0d74d03f87ca54db92aaf39129a7a54db1548a324ef3ac5  scripts/emit_distance566_weighted.py
d334f22f307e7628fc33c587ab0ce517d837049fc4c08d3763445e16a44ca03a  tests/test_emit_distance566_weighted.py
```

The exporter pins the exploration artifact, coordinate record, challenge
revision, and literal input. It validates both target sectors before pruning
and validates them again afterward. Pruning deletes entries only while the
exact strict threshold survives. Loads and totals are updated with the actual
natural multiplicities. Bases and independently paired witnesses remain
unchanged. Surviving original-row witnesses remain valid even if the base
itself is removed from a representative list.

The exporter orders compact families by the coverage class list before
emission. Its generated detector and family indices therefore agree.
The current byte-check path uses `read_bytes` and `write_bytes`.
The test at `tests/test_emit_distance566_weighted.py:124` rejects both CRLF
changes and an extra newline. This is stronger than the earlier text-mode
comparison. Tests also cover strict equality rejection, malformed rows and
weights, wrong sectors and pairings, provenance hashes, and basis preservation.

No parser, LP solver, heuristic score, or independent Python validator is
trusted as a Lean proof. The finite checks discharge the obligations.
Restricted-list duals and zero-price observations retain their limited scope.
No source-code lower bound, global pricing optimum, or impossibility of
stronger packing is claimed by the new proof.

## Execution evidence and audit

The public `module-results.json` lists the exact ordered 84-module inventory.
I compared each entry with its retained successful step record.
All source hashes, compiler commands, zero exits, wall times, and RSS values
agree with the current snapshot. All commands pass one Lean thread, `-M7000`,
`autoImplicit=false`, and `maxSynthPendingDepth=3` explicitly.

The corrected focused audit ran with those options and an output `.olean`.
Its raw log is empty and its exit is zero. It checks thirty guarded dependency
targets and nine finite positive/negative controls.
The audited coding-theory dependencies use only subsets of `propext`,
`Classical.choice`, and `Quot.sound`. I found no custom axiom, `sorry`,
`native_decide`, unsafe declaration, or external proof primitive in the new
source snapshot.

The final audit took 95.92 seconds with process RSS of 2,004,592 KiB.
The largest recorded module process RSS is 4,526,196 KiB.
The relevant allocation observations record one CPU of affinity, 8 GiB
effective memory, and zero permitted swap. These are retained-artifact
compilations, not a cold full-project build or a whole-allocation memory
benchmark.

The initial capstone audit failed two expected-message guards, for
`PackingData.xRange` and `.zRange`. The final source corrects their expected
standard-axiom sets. The old and final 124-entry manifests differ only in
the audit file. No mathematical proof body or certificate changed in that
correction. The capstones themselves already passed in the initial allocation.

`python-checks.json` agrees with the retained log: 114 tests passed and one
optional SciPy test skipped in the default locked environment.
All eleven recorded validation steps exit zero, including Ruff, the new
79-module/compact byte check, old coordinate and packing regeneration,
the ten old-module comparisons, and the removal emitter check.
The 36 relevant Python source/configuration hashes match the tested snapshot.
The isolated exploration environment separately covers all 22 search tests.
SciPy need not become a mandatory dependency for the exact validator or
default test collection.

## Preservation, integration boundary, and limits

The old fifteen distance modules, historical evidence, and dependency pins
remain unchanged. The parent's 474-entry preservation manifest matches.
The earlier source and artifact manifests retain their bytes.

Static integration wiring is correct: the package exports the stronger Pauli
capstones, the main audit includes all thirty focused targets for 300 unique
guards, and the parent runner names twelve audits. Its 408-entry preflight
matches the reported source snapshot. Runtime combined validation is outside
this standalone approval and remains pending here.

The finalized public standalone README correctly distinguishes the passed
standalone proof from pending combined validation. I checked its certificate
counts, strict surpluses, audit counts, test scopes, and replay description.
I used the actual fetched execution records and the public
`module-results.json`, `capstone-and-audit-results.json`,
`python-checks.json`, and `standalone-validation.json`, rather than assuming
success from a narrative. The inventory-label clarification above
is resolved through the explicit path-and-digest fields.

I performed static source inspection and lightweight literal/hash checks.
I did not independently rerun Lean, pytest, generation, a solver, or a search.
The successful executions are inspected evidence from Hooke's bounded runs.
No optional source polish is required for the mathematics.
Only this report was written in the public evaluation directory.
Implementation, shared integration, root docs, pins, earlier reviews, and
cluster jobs were untouched by this review.
