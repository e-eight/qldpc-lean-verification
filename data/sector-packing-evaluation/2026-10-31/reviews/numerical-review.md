# Independent numerical review — final Z handoff

## Status and ownership

**No blocking findings. The frozen numerical Z continuation gate is approved
for literal Z-sector formalization.** Hooke's explicit final-validation-v2
freeze was received and its source archives, added controls, certificate
identities, and retained execution evidence were inspected. The earlier
test-coverage finding is resolved. No optional polish is required for this gate.

This approves finite numerical evidence, not a new kernel theorem. The X result
remains a 32-of-2,047 pilot; it is not a complete X bound of seven. The literal
emitter, generated Lean inputs, and literal-code application are outside this
review. The existing overall kernel result remains `6 <= d <= 20`.

Reviewed the numerical producer, stdlib validator, tests, experiment contract,
and imported validation primitives. The reviewer authored the separate
literature audit but did not implement the numerical code. No Python, tests,
Lean, solver, or cluster operation was run locally. A separate read-only
Node.js/BigInt calculation independently checked the frozen Z data, under a
25-second timeout and a 256 MiB JavaScript heap cap. Only this report and ignored
review notes were written; implementation, literature, other reviews, and
worker execution records were left unchanged.

## Findings and resolution

**Resolved regression-coverage gap — `tests/test_distance566_sector.py:68`,
`:163`, `:177`, `:186`, `:204`, and `:221`.** Version two adds eight executed
cases. A Bell-padded repetition fixture has nonempty X and Z checks and a
triangular, nonidentity detector basis with the correct paired inverse. Positive
cases pass in both orientations. Negative cases preserve the physical identity
pairing while moving a weak direction into the good prefix, permuting the
suffix without updating references, or breaking the relevant cycle condition.
Additional canonical-basis controls preserve logical pairings while violating
boundary annihilation. These changes exercise the missing conditions rather
than relying on a duplicated-class rejection or an empty opposite matrix.

The source diff adds the fixture, helpers, and tests; the producer and validator
are byte-identical to the reviewed v1 sources. The retained v2 test log reports
28 passes and zero skips. No validation check was weakened to accommodate the
new controls.

**Integration condition, not a defect —
`scripts/distance566_sector_verify.py:350–367` and
`tests/test_distance566_sector.py:308`.** Validation intentionally accepts a
correctly reported partial arithmetic profile and returns successful process
status. The X pilot is intentionally incomplete. Therefore exit zero alone is
not the continuation gate: a complete Z handoff must have the correct side,
`complete_residue_coverage=true`, seven checked nonzero patterns, and
`all_requested_passed=true`. Individual strict-threshold failures cannot be
interpreted as a global obstruction. The actual frozen Z record satisfies all
of these gate fields, including complete coverage and passing thresholds.

## Static checks completed

The producer reads the immutable **unpruned** focused export and analysis
export through the validator's hash-bound input loader. The literal reader
checks the actual 566 input bytes. The canonical X/Z bases are separately
checked as cycles, paired by the identity, and complete by the literal ranks
and encoded dimension. The selected detector basis is checked by canonical
class rank, physical cycle membership, reconstruction of paired witnesses from
the opposite canonical basis, and a physical identity pairing matrix.

Producer good-rank selection uses `6*cap < totalWeight`; it requires the saved
strongest-first prefix. The validator checks each good prefix family's exact
original-row witnesses and positive-weight arithmetic. With source alignment,
it additionally checks the original good-span rank, exact selected coverage,
and positive representative/weight association. A prefix of that rank is thus
not merely assumed from detector ordering.

Reference vectors are XORs of selected paired witnesses in the suffix. Their
canonical coordinates, selected physical pairings, cycle membership, and the
full annihilator rank/orthogonality are checked. Complete mode explicitly
requires dimension three and the ordered list `1,2,3,4,5,6,7`, including sums.
The producer caps the opposite-sector pilot at 32 of 2,047 deterministic
patterns; the validator distinguishes that profile from complete coverage.

Pool entries retain physical support/mask equality, original own-base row
indices/masks, canonical and selected coordinates, nonzero quotient classes,
and every stored provenance. Each physical support appears once; source
alignment reconstructs the complete expected pool from the immutable source,
including originally zero-weight representatives. Physical cycle checks use
the opposite check matrix, whereas row-combination witnesses use the detector's
own stabilizer rows. The orientations are consistent in both code branches.

For every selected residue/pool index, the validator checks quotient
compatibility, canonical compatibility, and **direct physical pairing one**.
It then recomputes all physical loads with sparse sets and unrestricted Python
integers, independently of the producer's bitmask/Fraction implementation.
Weights reject Booleans, fractions, zero, and negative values. Capacities,
ceilings, and the strict threshold are recomputed exactly. Restricted duals
are checked only on all eligible stored columns, including unselected ones;
their scope does not claim global pricing optimality.

The LP is lazily imported and only proposes rounded integer weights. Candidate
selection compares exact ratios; there is no trust in floating-point solver
success for certificate validity. The per-case LP cap and overall soft budget
are separate from the detached allocation's hard resource limits. The optional
SciPy test can be skipped in the default locked environment and must not be
reported as an executed solver test there.

The validator imports stdlib-only validation primitives and the pinned literal
reader, not the producer, NumPy, or SciPy. Its CLI checks certificate provenance
and runs source alignment. The producer's embedded `source_sha256` field is not
itself checked by that CLI: source-to-execution association must come from the
final external source manifest and retained records.

## Source identities inspected

These identify the frozen sources. The archived v1 test has SHA256
`e956a274c265c176778c35ec5a07181f958ca263c879e27e62b386f5614f3110`;
only that file changes in v2.

| Repository-relative path | SHA256 |
| --- | --- |
| `scripts/distance566_sector.py` | `a5c1aa34118a1e941220c6e423df866e5c95032a9bab0a390b745e1ff1063703` |
| `scripts/distance566_sector_verify.py` | `87a71e1cee7b028d1033a3301ac11c481a1bf172d3b8b3ba24fdf7e641a63f0f` |
| `tests/test_distance566_sector.py` | `b98260f3d48331d47efaec67dac7beeb84782dba0a525f6de4071c534a407dbd` |
| `scripts/distance566_weighted_verify.py` | `220628ed3ab94f380ed5679f3cf7ec2891e2621ad2d659791cf28de387f27b98` |
| `scripts/emit_removal566.py` | `235ed81a143a25c3989f7e364197cd60f7a5f5208a95e7131db915161131430a` |

The immutable input hashes match the loader's constants:

| Input | SHA256 |
| --- | --- |
| Literal 566 challenge JSON | `061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be` |
| Original focused export | `c097a4a92565609f73fff4520a494471b4d1204292846e5614877eea2da487e2` |
| Analysis export | `fa54c2e0c13097f3e2433c9a4ca2e36a82763bff02eb0cddfec76a1b0b84fe78` |
| Canonical coordinate file | `171d2327eeda9aedb7a2585332fa2f495ac61aef5859e9cf6f9d8297415f34a6` |

## Independent frozen Z-data calculation

The public certificate and fetched worker certificate are byte-identical, with
SHA256
`d4a006802074810f13b37cc2a47728043a4f3c2a7cf7e3635dccacde11033d8e`.
The independent calculation imported no producer, validator, Python numerical
library, or solver. Large JSON mask integers were recovered without
floating-point rounding and all primal/dual arithmetic used BigInt.

It checked the actual pinned 566 JSON bytes, literal ranks `(274,274)`, matrix
commutation, both canonical cycle bases and their identity pairing, and the
selected basis's full physical inverse pairing. All 64 original X-detector
families and all 9,306 original representatives were reconstructed against
their own original X rows, checked to annihilate Z boundaries, and assigned
canonical classes directly. Their integer loads and 9,306 restricted-list dual
constraints were independently checked. Exactly fifteen qualifying classes
have rank fifteen and equal the asserted prefix.

The fifteen good certificates retain exactly the 1,192 positive source
representatives with their original weights and indices. The smallest strict
surplus `W - 6*cap` is 34. The suffix has dimension three; its canonical basis
is `[261670,203974,142242]`. Its rank, pairing annihilation, and all seven
nonzero sums agree with the exported physical references and selected
coordinates.

All 5,885 distinct pooled supports and all 5,885 own-base provenances were
checked against the unpruned source, including the originally zero-weight
entries. The full pool's physical pairing was compared with quotient
compatibility for every residue: 41,195 comparisons. All 1,527 positive primal
entries pair physically to one with their reference. All 566 loads per case,
the capacity maxima, weight sums, integer ceilings, and strict thresholds
match both the original and fresh validation reports. The 23,540 eligible-pool
dual constraints and exact weak-duality inequalities also hold; this is not a
global pricing or optimality claim.

| Suffix pattern | Canonical class | Positive primal entries | W | cap | ceil(W/cap) | W - 6*cap |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 261670 | 200 | 10443350 | 1000003 | 11 | 4443332 |
| 2 | 203974 | 215 | 11968338 | 1000003 | 12 | 5968320 |
| 3 | 58080 | 217 | 12067879 | 1000004 | 13 | 6067855 |
| 4 | 142242 | 239 | 12027642 | 1000004 | 13 | 6027618 |
| 5 | 120196 | 217 | 12448940 | 1000003 | 13 | 6448922 |
| 6 | 79716 | 221 | 11871849 | 1000004 | 12 | 5871825 |
| 7 | 182594 | 218 | 11567180 | 1000003 | 12 | 5567162 |

The combined numerical Z threshold is seven because the original good
families provide seven; the larger residual values alone do not establish an
eleven-or-higher global Z bound. This calculation preceded the tests-only v2
change; its exact certificate and producer/validator bytes remain unchanged.
The original source version is preserved in the public v1 archive.

## Final execution evidence and chronology

Inspected the public numerical README, aggregate gates, commands, job results,
handoff checks, source inventories, both source archives, original Z records,
and final-validation-v2 records. Public source manifests, resource observations,
frozen-certificate list, and fresh validation reports match their fetched
counterparts. The fresh Z validation report is identical to the original Z
report. The actual logs record twenty initial tests, then twenty-eight v2 tests
with zero skips, successful Ruff check/format, and fresh Z/X validator exits
zero. V2 contains no search command.

GNU time fields agree exactly with retained time files: v2 tests take 6.27 s
(78,496 KiB), Z validation 10.56 s (154,324 KiB), and X validation 12.69 s
(154,320 KiB). The v2 scheduler record is `COMPLETED`, exit `0:0`, 41 s,
sampled batch RSS 229,032 KiB. The earlier Z allocation is `COMPLETED`, exit
`0:0`, 99 s, sampled batch RSS 614,904 KiB; its search command takes 31.56 s,
including setup, versus 24.40 s reported for packing itself. Command RSS and
scheduler samples have different measurement scopes.

Resource observations agree on one CPU affinity, one thread, 8 GiB cgroup
memory and zero cgroup swap. The final job has a fifteen-minute wall limit;
the pilots have twenty-minute limits. Scheduler conclusions are based on the
retained terminal records, not a new cluster query. The isolated SciPy
environment executed the optional solver test; this does not claim that the
default locked project environment executes it or that the full project test
suite was run for this task.

Both archives have six regular source/configuration members, each matching its
versioned manifest. The nine-entry source manifests differ only in the test
hash. The v1 test bytes also match the reviewer's retained pre-update copy.
The certificate headers correctly retain v1 provenance; v2 execution and source
association are separate. These historical headers are not stale-v2 errors.
Both certificate hashes match their before/after v2 checks. The current source
manifest has nine matching entries, and the public numerical artifact inventory
covers all 35 other numerical handoff files and verifies against their bytes.

| Evidence identity | SHA256 |
| --- | --- |
| Current/v2 source manifest | `c3a1933ef1d0627b8d3cdc84245ca6819f09ef413b37e9fa6062a12f3656b83e` |
| V1 source manifest | `689e68153cf1106777c3ead7d4dc7b00d7d7da4fa168de49fc48f696ab80f5c9` |
| V1 source archive | `7f8a0ec32f849e49d47c9b006e4adcf13468d741f343d2078a1d84fe3e632245` |
| V2 source archive | `ae269264a9ee9aedc2f6f5f042a8ed6ff1220272d6352a4a1ac1298fd4dec0eb` |
| Source archive index | `278f1ea7f9cf5b1e2961bda3601126ed9ff5872656df4012f458b20122ef409e` |
| Numerical validation aggregate | `fc16950d48e72c36ec0c92709fb352e1423d8160f9eed6f6253e24e694d135ef` |
| V2 execution record | `c8016587772b36b0b73f9b106df581e91b949f8b0d210604e3dd5eab0c25f83a` |
| Original/fresh Z validation report | `c27bbf16ea613925270e454510685f77dd4455cd58fd8e89e46a0165b5a483a3` |
| Numerical artifact inventory | `a255ac922009c3fcfa320fce87a22dbc5933658fca2f277f241c4d6b18891757` |

## Review limits and continuation

The numerical Z evidence is ready for the parent's literal application. No
independent kernel replay or local Python/solver/test rerun occurred. The
separate BigInt calculation is independent finite data validation, not a
formal proof or a replacement for the Lean membership, coverage, and overlap
obligations. Input parsing and JSON association remain outside Lean's trusted
kernel.

The fresh X validator record confirms only its stated 32-pattern scope. Its
certificate hash and v1 header were inspected, but the X primal certificate
was not independently recalculated in this Z-focused review. No approval of a
full X campaign, complete X bound of seven, or stronger overall distance is
implied. No test-coverage finding remains open for the reviewed Z gate.
