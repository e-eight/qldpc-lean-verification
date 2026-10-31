# Independent exporter and generated-data review

## Verdict and scope

**No blocking findings. The frozen exporter/data handoff is approved for the
remaining generated-module replay and literal Z-sector application work.**
This is not approval of a completed literal distance proof: seven pilot
modules compiled; fifty-two generated modules and the handwritten capstone
remain uncompiled at this handoff. The kernel result remains `6 <= d <= 20`.
No optional polish is required for this continuation gate.

Reviewed both formatted Python files, the compact artifact, all 59 generated
sources, their inventories, the reused finite-check interfaces, and retained
execution records. No local Python, tests, emitter, solver, Lean, cluster job,
or search was run. A separate bounded read-only Node.js/BigInt inspection
checked data associations and arithmetic without importing the implementation.
Only this report and ignored review notes were written.

## Exporter and tests

`emit_distance566_sector.py:439` binds the original certificate to its approved
SHA256, reads the pinned literal/coordinate/unpruned inputs, and validates full
source alignment before compaction. The target gate rejects the opposite side,
partial coverage, and failed thresholds. Revalidation without source alignment
after pruning is appropriate: omission is intentional, while row witnesses,
cycles, coordinates, references, capacities, and all seven cases remain checked.

The deletion loop at `:57` accepts a removal only when the new total remains
strictly greater than six times the new maximum physical load. It preserves
positive natural weights and cannot replace strict seven with strict six.
Retained indices preserve source order. The shared-pool remap at `:111`
retains original entries and records original indices; each case's eligibility
count is recalculated for the reduced pool.

The tests cover the integer boundary, invalid masks/weights including Boolean
values, immutable source hash, unchanged bases/references/provenances/weights,
bad row indices, a changed reference, omission of a sum sector, wrong or partial
target gates, exact regeneration, CRLF corruption, and compact-byte corruption.
The actual cluster log reports 17 passes. Ruff and exact regeneration passed
after the recorded formatting/import cleanup. These are inspected execution
results, not independently rerun tests.

## Compact data and literal association

Independently compared the compact artifact against the approved full Z
certificate. All unchanged top-level data, selected bases, annihilator,
source-family records, and reference/coordinate fields agree exactly. Every
retained good entry is an unchanged source entry. Every compact pool object,
apart from its added original index, equals the corresponding original object.
Every residual weight is unchanged. The remap is injective, ordered, and covers
exactly the pool entries used by the retained cases.

The result contains 1,138 good entries across fifteen families and 222 residual
entries across all seven exhaustive patterns, using 172 distinct pool supports
and 29 mixed bases. Residual counts are `[31,35,32,33,30,28,33]`. All physical
loads and strict thresholds were recomputed with exact integers. The smallest
good surplus `W-6*cap` is 34 and the smallest residual surplus is 8,108.

| Pattern | Retained entries | W | cap | W - 6*cap |
| --- | --- | --- | --- | --- |
| 1 | 31 | 4180238 | 695355 | 8108 |
| 2 | 35 | 4765161 | 778773 | 92523 |
| 3 | 32 | 4613020 | 752387 | 98698 |
| 4 | 33 | 4690920 | 775899 | 35526 |
| 5 | 30 | 4496331 | 741579 | 46857 |
| 6 | 28 | 4242097 | 701694 | 31933 |
| 7 | 33 | 4460488 | 729574 | 83044 |

All generated raw entries were parsed and compared field-for-field with the
compact certificate. Their masks, unchanged weights, row-index lists, and mixed
base indices agree. Each representative was independently reconstructed from
its own base and the actual original X rows. All physical masks are below
`2^566`, all row indices are below 274, and all mixed base indices are below 29.
The 29 base masks equal their sparse supports and annihilate HZ. Each reference
annihilates HX, equals the preserved physical reference, and has selected
pairing pattern `(i+1)*2^15` for `i=0..6`. Good-family bases agree with the
existing selected X masks in positions `0..14`.

The generated source has 180 raw blocks and 1,360 total entries. All per-block
range/class facts, residual base-pair facts, append aggregations, and family
aggregations have complete index lists. The 198 capacity chunks comprise nine
chunks per family, covering physical positions `0..565` exactly, with a final
54-position chunk. Every threshold explicitly uses `(7-1)*cap < totalWeight`.
The complete 59-module list is unique, matches the source inventory, and orders
all internal imports before their consumers.

The mixed pair checks deliberately concern the selected **base**, not an
unrelated class tag. Transfer to the representative needs its checked own-base
row combination and the reference's HX-kernel fact. Both finite inputs are
emitted with the correct orientation. The later handwritten proof must combine
those facts through the approved helper. Physical support conversion uses
`Fin.ofNat`, with explicit raw support, mask, row, and base range gates to
exclude wraparound; those gates must be consumed in the final proof.

No compact-six artifact is loaded as threshold-seven evidence. Existing
weighted-coverage and row-table facts provide the selected basis and actual-row
interface; the new strict-seven family facts are separate. No generated source
uses `sorry`, `sorryAx`, `native_decide`, or a new axiom.

## Execution and preservation evidence

All sixteen published command receipts match their retained raw JSON metrics
and source identities. Each of the seven individual pilot receipts matches
its current source hash, successful exit, explicit `-j1 -M7000
-DautoImplicit=false -DmaxSynthPendingDepth=3` options, output path, and fresh
object digest. All seven fetched object bytes match the published digests.

The source pre/post logs each contain seventeen successful hashes; the
generated pre/post logs each contain fifty-nine. All current source hashes
match, mapping the staged `inputs/codes/566-18-20.json` entry to the identical
local upstream JSON. All 59 generated hashes and all 78 artifact-manifest
entries match. The 621 preserved prior paths also match at review time.

The pilot wrapper took 547.59 seconds; its largest recorded command-process RSS
was 3,330,704 KiB. The retained allocation completed with exit `0:0` in 687
seconds; scheduler-sampled batch RSS was 5,523,612 KiB. The resource record
enforces one CPU affinity, one Lean thread, 8 GiB memory, zero swap, and a
twenty-minute wall limit. These RSS figures have different scopes. Dependencies
and approved project imports were retained artifacts; this was not a cold build.
The contained generation-v1 failure stopped at Ruff before generation/tests.

## Reviewed identities

| File or manifest | SHA256 |
| --- | --- |
| `scripts/emit_distance566_sector.py` | `786f1fc5f0a91a88e10893b89346f447f4d756f492bdfc6ae637f338b1527ed4` |
| `tests/test_emit_distance566_sector.py` | `47dea81cb55c4b2c6e776e6c270e56e1beb800af878a4fd3bb5fe469b8b4af79` |
| Approved full Z certificate | `d4a006802074810f13b37cc2a47728043a4f3c2a7cf7e3635dccacde11033d8e` |
| Compact artifact | `41422a45f3af02da426ce99d35f58f2b7c40a0083a5a44a7832e9dcde18870e2` |
| Source manifest | `7e4b1a386ca1a2cc0331e859fe8c5f3e2d2e77dad333f4469574c1bfb60dd17d` |
| Generated source manifest | `f1d51c2642b6ada5fdf7e7b781bb42b72a7c055a817723396728a8d890a9a6f1` |
| Artifact manifest | `1861ee4e168b94235e664257aebc749fc010e147ab319ee56f6ea3a49cd746d1` |
| Module inventory | `8f70a23a98590f01b74fb02e0b67cf75aa04d37f830d07b2eb462e18d8f3b8f1` |
| Declaration inventory | `94f40cf27a312e83794c2ab575a6849891dc73ff14e4b62c481f530a32bb1122` |
| Pilot artifact inventory | `0dd8ac7745ea9c167e3c1cf935881e65a0486d057166e6092455e350d1ce8be0` |
| Results record | `fe8089953c36f748979439c75aea2a6d77c78391232b0eed0bf0b493394b9faf` |

The manifests and inventories are under `../literal-z/generated/`, relative
to this review directory. Execution conclusions rely on retained records, not
an independent replay or a new scheduler query. Static/data approval does not
assert successful elaboration of the remaining 52 modules, a completed axiom
audit for a target capstone, or a new literal-code theorem. Those remain the
next review gates.

## Follow-up: index-template correction, 2026-10-31

**Static assessment: no blocking finding in the minimal correction.** Corrected
regeneration and Packing compilation receipts are still pending at this review
point. This is approval of the source change for those checks, not a claim that
the corrected aggregate has compiled or that the literal capstone is proved.

The initial review above is preserved verbatim; its pre-append SHA256 is
`5d6654799e48564fbd2ef7a0027a6fe74178f9151dd6bdabaecceb9e76fa14a1`.
Its identities and pilot scope continue to describe that historical snapshot.

Compared the archived v1 emitter and Packing source with current bytes. Each
has exactly one substitution: the generated `goodClass` index changes from
`get ⟨a.val, by omega⟩` to `get (Fin.castAdd 3 a)`, at emitter line 399 and
Packing line 42. Nothing else in either file changes.

For `a : Fin 15`, `Fin.castAdd 3 a` has type `Fin (15+3)` and retains `a.val`.
It therefore selects the same position among the eighteen existing X masks.
The bound comes from the standard finite-index embedding rather than asking
`omega` to discover the opaque list's length. The local pinned Mathlib
`Data/Fin/Embedding.lean` identifies `castAdd` with the corresponding `castLE`
embedding; its injectivity is also recorded in `Data/Fin/SuccPred.lean`.
There is no new hypothesis, detector shift, weight change, or threshold change.
The same fifteen `class_check` facts are used by the aggregate.

The current Packing source SHA256 is
`9744afd66eac8e405ef603f6a32c8d0051a59a21aa4a8460e3fe9a2600bba5a6`.
The initially supplied `53f0f8bc…fc007ae` is the archived v1 Packing identity.
Both the current two-file manifest and the archived/current source copies
agree with the corrected identity. The current emitter SHA256 is
`6640651b4b5446bb386f862042cafe5b9b8557d7148d9d3d7e2c9f38eaa694c2`;
the test source remains
`47dea81cb55c4b2c6e776e6c270e56e1beb800af878a4fd3bb5fe469b8b4af79`.

All other 58 generated modules retain their initial hashes. The compact
artifact retains SHA256
`41422a45f3af02da426ce99d35f58f2b7c40a0083a5a44a7832e9dcde18870e2`.
Accordingly the prior raw-data, reference, provenance, capacity, and deletion
review applies unchanged. All 51 files covered by the old Python-record
artifact inventory also retain their bytes.

The corrective evidence is under `../literal-z/proof/template-v2/`:

| Corrective record | SHA256 |
| --- | --- |
| Two-source manifest | `92d6f990cc6c32d9b61a6bb4de4740e05af5c5e170811d253f1f0b31ea111483` |
| Corrected 59-module manifest | `ceb066e1948071dad4989871bc9f04df9706b0a5d54852e484dd0407fe7f08c4` |
| Byte-delta record | `b13bd66db7278cbca0d9eb705b8da8ef66bee3f4909996cee8fd4222aebfc837` |

Current hashes match those manifests; the byte-delta record explicitly marks
cluster regeneration pending. Future Python-v3 checks must use the corrected
manifest and unchanged canonical compact path, preserving the old manifests
as historical evidence. A later follow-up will bind the actual successful
regeneration/compilation and Python-v3 receipts to their final source hashes.
No local tests, Python, generation, Lean, or solver execution was performed
for this follow-up.

### Subsequent handoff clarification: freeze withdrawn

The parent withdrew the corrective source freeze because regeneration and
manifest publication overlapped. The hashes and comparisons above record the
earlier review observations. Acceptance of a coherent frozen source/manifest
tuple remains pending Gauss's explicit FROZEN notification and a fresh identity
check. The static assessment of `Fin.castAdd 3 a` is unchanged. This follow-up
does not release the Python-v3 gate while that handoff is unresolved.

### Coherent freeze and Packing-v2 receipt: resolved

**The minimal correction is approved with no blocking findings.** Rechecked the
explicit `FROZEN READY` marker, both current source hashes, both source copies,
and all 59 corrected manifest entries. The emitter is `6640651b…aa694c2`, the
Packing source is `9744afd6…bba5a6`, and the corrected manifest is
`ceb066e1…7f08c4`, matching the full identities above. The other 58 modules,
canonical compact, and all 51 old Python-record files remain unchanged.

The parent clarified that its earlier expected Packing hash was a stale v1
read. The corrected manifest already contained the v2 identity. The source
guard stopped that attempted handoff before staging or job submission; the
subsequent atomic manifest copy changed no bytes. The withdrawn-freeze note
above is superseded by this verified coherent handoff.

Inspected the retained `exact-regeneration-v2` receipt: exit zero, 59 modules
checked, emitter source hash `6640651b…aa694c2`, wall time 10.47 seconds. Its
raw output and the byte-scope result agree on all 59 outputs, unchanged other
58 sources, and unchanged compact bytes. The public regeneration record now
reports success; it supersedes the initial byte-delta record's pending field.

The retained `Distance566SectorZPacking` compiler receipt has exit zero and
source SHA256 `9744afd6…bba5a6`. It passes the explicit project options and
`-j1 -M7000`, writes the owned Packing object, and records 90.76 seconds and
2,113,612 KiB process RSS. Its time file agrees; its raw compiler log is empty.
The receipt records output digest
`0d575b99977e0fac3d5a46eb746e5e409944ab7b4253d7d463a79dc3e373ae12`.
That digest is receipt evidence; the object bytes were not independently
inspected in this follow-up, and no local Lean replay occurred.

| Resolved handoff evidence | SHA256 |
| --- | --- |
| `template-v2/FROZEN.json` | `baea334928d09351852e517823c9beff2275ef2560334eb7dc7c57a019178de1` |
| `template-v2/regeneration-check.json` | `0e1e55b3eff6bca6bf560d93394f9be75ed9bb690cbaf8ef485d680df7317b35` |
| Retained Packing-v2 compiler receipt | `681d2ddcab43732d51e65a7f32280b6f78ebf1350edbd5d69b05b13633fe3611` |

This closes the corrected-template/aggregate review gate. The literal capstone
and audit remain separate review work. Python-v3 validation will be reviewed
from the new sibling record after its actual execution handoff is frozen;
the historical 169-pass Python-v2 result is not reassigned to the corrected
source version.
