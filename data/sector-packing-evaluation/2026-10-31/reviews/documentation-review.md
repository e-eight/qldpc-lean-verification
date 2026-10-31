# Independent documentation review

**Current status: documentation and runtime-claim consistency approved.** All
three accuracy findings and both optional polish items are resolved. The final
follow-up below checks the completed-run narratives against published and
retained records. The separately assigned proof/runtime evidence reviews remain
distinct from this documentation review.

## Initial review status and scope

Static review completed against the document hashes below. **No mathematical
claim contradiction found. Three documentation accuracy corrections remain.**
The combined integration run is intentionally documented as in progress;
successful runtime validation is not approved by this report.

Reviewed the four root documents, `lean/README.md`, the new sector-record
README, and its integration README. Checked current-result statements, changed
sections, historical evidence boundaries, local links, source/module/audit
counts, and replay instructions against the frozen sources and public records.
Literal proof correctness remains the separate proof reviewer's responsibility.
No source or documentation implementation was edited, and no tests, Python,
generator, search, Lean, or cluster job was run. Only this report was written.

## Concrete findings

1. **Medium — stale current replay command:**
   [lean/README.md:281](../../../../lean/README.md#build) directs the current
   weighted 566 integration to the historical bound-six runner and twelve
   audits. Its source manifest now mismatches the current package umbrella and
   `KernelAudit.lean`, so that recipe cannot replay the current checkout.
   Point the current recipe to
   `data/sector-packing-evaluation/2026-10-31/integration/replay.sh`, with
   fourteen project audits plus the standalone helper audit. Retain the old
   replay as an explicitly historical checkpoint requiring its original bytes.

2. **Low — optional-test count:**
   [README.md:105](../../../../README.md#python-environment) says the default
   suite skips one optional LP test without SciPy. Both current tests use
   `importorskip`, and the reviewed V3 run records two skips: the sector and
   weighted LP tests. Update the current environment description to two.

3. **Low — repeated prints described as guards:**
   [integration/README.md:32](../integration/README.md#replay-contract) calls
   the historical 179 repetitions "guards." The source has 371 guarded unique
   targets and 550 textual `#print axioms` commands; the additional historical
   repetitions are prints, not additional guards. Describe them as repeated
   axiom prints. The stated 371/550 counts themselves are correct, and every
   unique target has a guarded occurrence.

## Consistency and evidence checks

The current statements agree on `d_X >= 6`, `d_Z >= 7`, and overall
`6 <= d <= 20`. The weight-twenty X witness supplies an upper bound; no document
claims exact distance twenty or treats source lower bounds as established.
The submitted exact-distance inventory stays nineteen: sixteen bicycle and
three surface instances. Historical bound-three and bound-six sections are
identified as earlier checkpoints, rather than contradictory current results.

The new Z certificate uses fifteen good directions and every one of seven
nonzero residual patterns. The mathematical description retains physical
weight, boundary annihilation, complete coordinates, reference pairing, and
the strict inequality `6 * cap < totalWeight`. Stronger residual numerical
values do not become a stronger uniform kernel claim. The X result remains
32 of 2,047 patterns, with 2,015 unchecked; failed greedy disjointness is not
presented as infeasibility. Affine-family scaling is a future bounded pilot,
not an executed campaign or a new kernel result.

The literal public results report 59 generated modules plus a capstone and
focused audit, totaling 61. The documented 33 literal guards/seven controls,
25 generic guards/ten controls, and thirteen helper guards/twelve controls
match static source counts. All 71 new generic/helper/literal axiom targets
appear among the main audit's 371 unique targets. The umbrella exports the
literal Z capstone and retains the weighted Pauli bridge.

The integration runner lists fourteen project audit sources and the separate
helper. Its 428-entry source inventory matches all current entries, contains
all active Lean sources and the exact 347 tested Python snapshot entries, and
has SHA256
`0f6bc39cd6f06b3499dd0164a406dcc0076f596fd7a9c4439266c32bb0fb73e5`.
Static source association is distinct from a completed combined replay. The
new integration README says in progress and makes no completed-runtime claim.

The current and historical Python records are distinguished correctly outside
the optional-test sentence above: V3 tests the corrected emitter/Packing
sources, while the earlier record remains immutable. Historical resource
measurements and the newly reported standalone timings distinguish process RSS
from sampled batch RSS. The standalone literal figures were compared with its
public receipts/summary for documentation consistency; they were not replayed
or independently re-audited here.

All 96 local Markdown links resolve, including checked heading fragments.
External URLs were not fetched or revalidated in this static review. No new
literature search was performed.

## Optional polish

- In root README line 63 and Lean README line 129, say "59 generated modules,
  the capstone, and the focused audit (61 total)." The current phrasing can
  sound as though the audit is additional to 61 application modules.
- In RECOMMENDATIONS line 101, identify the scope as the current 64-class table
  with 57 distinct nonzero quotient labels. This avoids reading "current pool"
  as a claim about arbitrary future representative enrichment.

## Reviewed document identities

These hashes bind this point-in-time review; narratives are outside the frozen
integration source manifest and may change during final result assembly.

| Document | SHA256 |
| --- | --- |
| Root `README.md` | `07c8e4c536b10de5e37b3db34cfe05f26bac85ea293945b88f8ed3b3c6653c62` |
| `RECOMMENDATIONS.md` | `ac66193d3ecf0975044f3f9d196af3fa80ff1f3da87b6503474cc4c91b4b1445` |
| `CHECKS_AND_RESULTS.md` | `9fcc7761f4afb891c204f9486ad479d882ddc5c69156e73bc400bc3dac8a4883` |
| `CERTIFICATES.md` | `c477c94f4d6b81d48699c72f05d0388ee286591bf7a58550add9ab4753ff95c0` |
| `lean/README.md` | `ca871014b9513028bab354a5472a87f0c10f10236da1d28eb5809e592e3a8fda` |
| Sector-record `README.md` | `ac80dfe41625589f20738fd3d8d3a79d3274886c75bce5d38c3dc2e97ae3088e` |
| Integration `README.md` | `6aec249355b41dbe5852d676b0c3b271ada556b172f759e61fb09a851f05d05b` |

Final follow-up should verify the corrections and refreshed document hashes,
then compare any completed integration-runtime claims with the actual frozen
execution record. This report leaves that runtime gate pending.

## Follow-up: all documentation findings resolved

**No remaining static findings.** Re-read and checked all five corrections:

- Lean build instructions now use the current logical-sector runner, fourteen
  project audits, and the standalone helper. The earlier bound-six replay is
  explicitly historical and requires its original source bytes.
- Root README now identifies two optional LP skips when SciPy is absent.
- The integration README distinguishes 550 textual axiom-print commands from
  371 guarded targets, including 179 historical repeated prints.
- Root and Lean READMEs explicitly count 59 generated modules, the capstone,
  and the audit as 61 total.
- RECOMMENDATIONS confines its quotient-label observation to the current
  64-class table with 57 distinct nonzero quotient labels.

The unchanged mathematical statements retain X lower bound six, Z lower bound
seven, overall bounds `6 <= d <= 20`, nineteen exact submitted instances, and
the partial 32-of-2,047 X experiment. Future affine-pairing pilots remain plans.
The integration README still correctly marks combined replay in progress.

All 97 current local Markdown links resolve, including checked heading
fragments. The added historical replay link resolves. All 428 frozen source
entries still match, and their manifest retains SHA256
`0f6bc39cd6f06b3499dd0164a406dcc0076f596fd7a9c4439266c32bb0fb73e5`.
The Python-v3 source inventory retains SHA256
`3cb3c9041d49da85862516b95eb6c639a623849e142075aa5dbe2df2ee135e8d`.
The documentation corrections are outside that integration manifest.

| Current approved document | SHA256 |
| --- | --- |
| Root `README.md` | `6c9f03ea3e88828020cc34417126aa1dc5ad8ecc3aa0d46f54bfcb4f3aa3a41e` |
| `RECOMMENDATIONS.md` | `615ecef7d36a2c7dcc097e241f6cf3232446ef97e0e286c59a189cda1c757270` |
| `CHECKS_AND_RESULTS.md` | `9fcc7761f4afb891c204f9486ad479d882ddc5c69156e73bc400bc3dac8a4883` |
| `CERTIFICATES.md` | `c477c94f4d6b81d48699c72f05d0388ee286591bf7a58550add9ab4753ff95c0` |
| `lean/README.md` | `8b5e9745af7b7d4c718bbcced39e6bdef856fda4bc2f6cfd0d4c28910bb0a369` |
| Sector-record `README.md` | `ac80dfe41625589f20738fd3d8d3a79d3274886c75bce5d38c3dc2e97ae3088e` |
| Integration `README.md` | `6b7d40959e9e34952c6b19a6e52c1665257d06b71ccee08b3324ce9901ecd171` |

This is static approval of these document bytes, not a combined-runtime
approval. No tests or proof/search commands were rerun; no external links were
fetched. Only this review report was updated. A later follow-up should bind
completed runtime claims and refreshed narratives to the actual final record.

## Final follow-up: completed-run narratives approved

**No remaining documentation findings.** Rechecked all seven frozen narratives,
the published integration metadata, the authoritative parent summaries, and
retained receipts. The documentation now correctly describes a completed warm
integration replay. All earlier corrections remain present, and the mathematical
scope remains X lower bound six, Z lower bound seven, overall `6 <= d <= 20`,
nineteen exact submitted instances, and only 32 of 2,047 X residual patterns.
No new numerical campaign or exact-distance-twenty result is claimed.

### Runtime claims and counts

The authoritative `parent-step-summary.json` and the published exact-runner and
fresh-main receipts agree on exit zero, monotonic wall time, and process RSS:

| Measurement | Exact runner | Additional fresh main audit |
| --- | --- | --- |
| Monotonic wall seconds | 414.42819383903407 | 21.12268992397003 |
| Narrative rounding | 414.43 | 21.12 |
| Process maximum RSS, KiB | 2,036,092 | 2,039,212 |

The retained terminal summary and public accounting agree on `COMPLETED`, exit
`0:0`, 450 allocation seconds, and sampled batch RSS 4,522,900 KiB. The narratives
correctly distinguish allocation duration from command wall time, and sampled
batch RSS from per-command process RSS. One CPU/thread, an effective 8 GiB
memory ceiling, zero swap, and the twenty-minute wall limit agree with the
published job/resource records.

All thirteen published timed receipts equal their fetched counterparts and the
commands aggregate; all exits and GNU time fields agree. The exact runner's raw
output has exactly the documented fourteen project audit markers followed by
the standalone helper marker, in the published order. Its internal hash output
contains precisely two successful checks for each of 428 source paths, or 856
success lines. Separate source pre/post logs each have the same exact 428 paths.
The main audit wording remains correct: 371 guarded unique targets and 550
textual axiom-print commands, including 179 historical repeated prints.

All current 428 source hashes still match the unchanged manifest. Its contents
include the exact current 347-entry Python snapshot. The imported-state records
are identical before and after the run and agree with the public associations:
61 literal modules plus four generic/helper modules, eleven pins, and 33 regular
configuration files. All 65 source hashes match current files; the accepted
literal artifact-map digest matches its frozen standalone record. The public
pin names, revisions, and origins agree with the tracked Lake manifest.
The literal input identities also agree between the two imported states.

The two fetched fresh objects, package root and main audit, independently hash
to the published artifact digests. Their source identities match current files.
The 65 retained imported object identities and private Git/configuration checks
were compared through the executed validator and its before/after records;
those imported objects and private Git objects were not independently replayed
or rehashed locally in this documentation follow-up.

### Final document and evidence identities

All 97 local Markdown links still resolve, including checked heading fragments.
External URLs were not fetched. The current approved narrative hashes are:

| Document | SHA256 |
| --- | --- |
| Root `README.md` | `3a7c6b8dcc2cf38b35f362c94e8091ce7210fba3cfc6a6f015be95867550a80d` |
| `RECOMMENDATIONS.md` | `615ecef7d36a2c7dcc097e241f6cf3232446ef97e0e286c59a189cda1c757270` |
| `CHECKS_AND_RESULTS.md` | `670b62ed64fa8110c52304e4105f2504607b930064e8f7b6ea6af78a0470f891` |
| `CERTIFICATES.md` | `c477c94f4d6b81d48699c72f05d0388ee286591bf7a58550add9ab4753ff95c0` |
| `lean/README.md` | `8b5e9745af7b7d4c718bbcced39e6bdef856fda4bc2f6cfd0d4c28910bb0a369` |
| Sector-record `README.md` | `990bd628e1f5dc64b7085e56ac6a8fb7573e6c698cab15f3415751121556918b` |
| Integration `README.md` | `793a56b3f8b1bcbb4f26b49ae890399f6dcd04c7bfac099a123e815d621fa4d5` |

The inspected public integration records, relative to `../integration/`, have
these identities:

| Evidence | SHA256 |
| --- | --- |
| `integration-validation.json` | `421c47b7faebd2864b0a3bbf666d1fadf1e2f56ec1bf1d61a03e5bd09b1e615c` |
| `commands.json` | `03f5e1336e980b74d00467648d7cf80a902254500314fa2a3dca66879a3be17b` |
| `job-results.json` | `c66999a42d4865e45de750a4f73482a1643cc5cce9f4108818fd77b8e494b84a` |
| `dependency-configurations.json` | `2df32ea764abfab3a48a81a5ea9128f452988dd4e66fc358e94fbdd615e7448c` |
| `imported-artifact-association.json` | `986888a870d20ef4098974978add39a3ed9078e137d6e524ec66b543953bb35b` |
| `fresh-artifacts.json` | `3d422bc1e987aff6634723c30790fd4dc3fb06895f6088450866009767891f3a` |
| `resources.json` | `c4869229c1c0cc6a47bba4e4655925c1018f9bf5529096b8267157a6c7dae3d4` |
| Frozen 428-source manifest | `0f6bc39cd6f06b3499dd0164a406dcc0076f596fd7a9c4439266c32bb0fb73e5` |

This closes the documentation/runtime-consistency follow-up. Ram's separate
runtime evidence review and the literal proof review retain their own scope;
this report does not replace them. No tests, Python, generator, solver, search,
Lean, cluster job, or scheduler query was run. Only this review report changed.
