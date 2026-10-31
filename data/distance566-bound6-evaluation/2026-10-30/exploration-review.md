# Independent review of the weighted exploration

## Verdict and scope

No blocking mathematical or integration findings.
The selected finite target certificates support threshold six in both sectors
with complete logical coverage. They are suitable inputs for the planned
Lean formalization. This review does not promote the kernel result from
`3 <= d <= 20` or review Hooke's forthcoming proof.

I reviewed the three `distance566_weighted` scripts, their tests, and the
weighted exploration evidence, especially `analysis-v1/lean-ready.json.gz`
and `final-validation-v2/`.
I inspected source, hashes, snapshots, validation logic, and lightweight exact
certificate data. I ran no solver, search, pytest suite, Lean process, or
cluster job. Only this report was written.

## Inputs, row witnesses, and integer arithmetic

Both available literal JSON inputs match the recorded SHA256 hashes and the
pinned challenge revision's input identities. The baseline coordinate digest
also matches the digest in the compact export's final validation record.
The target is the same literal 566-qubit matrix pair used by the earlier proof.
No reconstructed geometry or translation symmetry replaces its checks.

`distance566_weighted.py:34` carries original-row coefficient masks through
elimination. The information-set construction at `:286` augments the physical
matrix with an identity matrix, preserving coefficients in those original
rows. The export at `:407` correctly adjusts every coefficient when it chooses
a lighter base. The adjustment is XOR with the new anchor's coefficient.

The independent validator at `distance566_weighted_verify.py:128` reconstructs
every representative as its base plus actual rows from the detector sector.
It also checks syndrome and logical coordinates separately. Its sparse-set
implementation imports neither the search routines, NumPy, nor an LP solver.

I independently inspected all 36 selected target families in the compact
export using literal row masks. All 2,892 representatives reconstruct exactly
from the recorded original-row indices, which are distinct and in range.
All physical supports are distinct-index sets within the literal qubit range.
The compact export retains 1,443 X-detector representatives and 1,449
Z-detector representatives.

Weights are arbitrary natural multiplicities, rather than unit weights.
The search and full validator accept zero individual weights but require
positive total weight and capacity. The compact export removes zero-weight
entries without changing its loads, total, class membership, or coverage.
Its X-detector weights range from 42 to 502,270, and its Z-detector weights
range from 60 to 518,767.

I recomputed every selected family's integer loads, maximum capacity, total
weight, and ceiling. Each satisfies `5 * cap < totalWeight`.
The strict threshold is correct for lower bound six.
All calculations use unbounded integers. Floating-point LP output proposes
weights, but does not establish any threshold.

## Adaptive coverage and sector orientation

`distance566_weighted.py:195` selects independent class labels in order of
their certified family bounds. It does not require the original coordinate
classes to remain the chosen basis. The rank curves count the span of all
eligible classes at each threshold, rather than the number of successful
families alone.

For each target sector, I checked that the eighteen selected labels are
distinct, nonzero, and have rank eighteen. Their physical bases have the
specified coordinates against the frozen opposite baseline basis and satisfy
the correct syndrome equations.

The two detector bases are selected independently. They need not pair to the
identity with each other. `independent_pairing` at
`distance566_weighted.py:145` instead solves for a separate witness basis in
the opposite cycle space. Its coefficient orientation solves the required
detector-by-witness system, and its explicit pairing check catches a transpose
error.

I checked every selected witness's reconstruction from the opposite baseline
basis, its opposite-sector syndrome, and both complete eighteen-by-eighteen
identity pairing matrices. The X-detector families bound Z logicals and use
X stabilizer rows. The Z-detector families bound X logicals and use Z
stabilizer rows. Those orientations are consistent across the search,
validator, export, and summary.

The existing literal rank proofs give eighteen encoded qubits. Independent
detector classes and paired cycle witnesses therefore supply complete
coverage through the existing coverage theorem. This is coverage of every
nontrivial logical class, including sums of basis classes, not only the saved
eighteen representatives. The new Lean proof must instantiate these facts.

The final validator checks CSS commutation, matrix ranks, the complete frozen
baseline pairing, all family coordinates, all rank curves, and both new
coverage pairings. I inspected that logic without rerunning the complete
validator on the larger search outputs.

## Restricted duals and pricing diagnostics

`exact_dual` at `distance566_weighted.py:75` turns floating prices into a
feasible integer dual for the stored representative list, repairing deficits
by increasing prices. The validator independently checks that feasibility
and the corresponding exact weak-duality inequality.

I checked the selected compact lists' dual dimensions, natural prices,
positive denominators, feasibility, and weak duality. Their total dual prices
are at most nineteen times the denominator, which excludes threshold twenty
for these particular lists. This is not a global obstruction to better
representatives or a theorem about exact code distance.

The report's zero-price construction at
`distance566_weighted_report.py:35` solves the stabilizer restriction on the
priced positions. The resulting representative remains in the same class
while avoiding every positive-price position.
I checked all 36 saved target diagnostics against their selected family,
original rows, and stored prices. Each has price zero and preserves the
family's nonzero class. Their physical weights range from 32 to 144.

Each diagnostic disproves the global extension of that particular stored-list
dual. The README, analysis scopes, and validator output do not generalize
this to all price vectors, all classes, or impossibility of distance twenty.
The proposed experiment of shortening and adding these representatives is
consistent with the measured pricing gap.

The weaker 578-qubit control receives less time, fewer trials, and fewer
classes. The record explicitly avoids interpreting its weaker result as an
effect of removal. The absence of a discovered logical below twenty is also
stated as a search outcome, not a lower-bound proof.

## Source snapshots, validation, and resource claims

All sixteen top-level source-manifest entries and all thirty-five artifact
entries match the reviewed snapshot. Each archived source file matches its
phase's hash manifest. The three baseline files are intentionally staged
separately from the archives. Their hashes match through the mapping in
`commands.json`.

The current three scripts and test file equal the final-v2 snapshot.
Between final-v1 and final-v2, the only archived source change is the solver
option `parallel: "off"` becoming `parallel: False`.
The earlier search snapshots and evidence retain their original bytes.
The final validation records identify the exact certificate and coordinate
digests that they checked.

The record distinguishes the historical warning from the final configuration.
The search snapshots used the string option and recorded one warning.
The final snapshot uses the Boolean option and records zero warnings with
`pytest -W error`. The source intentionally filters SciPy's known warning
about options forwarded to HiGHS. Passing the test run does not mean that
all warning filters were disabled.

The metadata consistently records one requested CPU, one configured solver
thread, 8 GiB memory, zero observed permitted swap, and final CPU affinity of
one. The five allocations report completion and zero exit status.
The focused allocation's 795 seconds, sampled batch RSS of 175,368 KiB, and
search-process RSS of 157,488 KiB have explicitly different scopes.
The per-problem search budgets are soft limits, not allocation wall limits.
The recorded overruns and total process time do not contradict that scope.

The isolated environment pins SciPy, NumPy, pytest, Ruff, and their supporting
packages through hash-locked requirements. The source contains fourteen test
functions expanding to twenty-two cases. Final-v2 records all twenty-two
passing, warning-as-error and Ruff checks, and fresh validation of both full
runs and the compact export. These are inspected execution records, not
tests rerun by this reviewer.

## Default environment and remaining limits

No mandatory SciPy dependency is required for the current default test suite.
`tests/test_distance566_weighted.py:85` skips only the LP optimization test
when SciPy is absent. `optimize_weights` imports SciPy lazily at
`distance566_weighted.py:95`. Other imported helpers and the exact validator
do not require SciPy. NumPy is already a main project dependency.

The expected default scope is twenty-one executable cases and one optional
skip when SciPy is absent. The isolated environment covers all twenty-two.
Running the exploration optimizer itself requires that isolated environment
or an explicit SciPy installation. I found no dependency integration blocker.

No optional polish is required for formalizing the selected target data.
This review does not independently reproduce the timed searches, attest the
scheduler state, rerun the full numerical validator, or inspect the additive
Lean proof. It confirms the reviewed finite target data and its supporting
logic while preserving the distinction between exact numerical validation
and kernel verification.

I did not change source, earlier records, proofs, dependency pins, the PR
workspace, or root documentation. No agents were spawned and no commits,
pushes, external messages, or cluster jobs occurred.
