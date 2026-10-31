# Additive bound-six proof for the literal 566 matrices

## Standalone result and integration status

All 84 new modules pass kernel compilation with the project options. The focused
audit passes 30 guarded dependency checks and nine finite controls. The additive
capstones prove unconditional `d_X >= 6`, `d_Z >= 6`, and weight at least six for
every nontrivial Pauli logical. The unchanged stored X witness supplies the
weight-twenty upper bound. Thus the standalone proof establishes `6 <= d <= 20`.

The combined [root and twelve-audit replay](integration/README.md) also passes,
including the fresh main-audit artifact with 300 unique guarded targets. The
successful allocation completes in 9 minutes 9 seconds. The exact parent runner
takes 476.77 seconds and the fresh main audit 32.37 seconds. Its 408-source and
literal-input pre/post checks match the frozen bytes.

The first two integration attempts failed before root compilation because isolated
dependency mirrors lacked Git metadata and a usable QEC configuration file. The
successful retry restores private configuration bytes from pinned Git objects.
These repairs change no proof source, tracked dependency pin, shared cached
worktree, or certificate. The parent-owned integration record preserves the
separate attempts and their measurement scopes.

The existing committed `3 <= d <= 20` proof and all its evidence remain unchanged
historical checkpoints. The exact-distance inventory remains nineteen. Exact
target distance twenty remains open.

The input is the immutable weighted exploration's `analysis-v1/lean-ready.json.gz`.
Only its target 566 entries are used. The 578 control results remain numerical.
The independent exploration review in this directory is preserved separately.

## Proof route

The standard-library exporter first revalidates the literal matrices, coordinates, original-row
witnesses, natural weights, exact loads, and independently paired detector bases.
It then deletes representatives only when the exact strict inequality
`5 * cap < totalWeight` survives. The new compact certificate preserves the source
artifact and does not expand natural multiplicities.

The immutable input has 2,892 positive representatives. The new `compact.json.gz`
retains 734 X detector representatives and 732 Z detector representatives. Each sector keeps its full paired
18-class basis, and all 36 strict thresholds survive exact deletion. X detectors
bound Z logicals; Z detectors bound X logicals. The smallest remaining strict
surpluses are 4,018 and 166 respectively. Natural weights are never rounded again.

`WeightedPackingCertificates` connects weighted projection and checked row-mask
tables to the existing original-row membership theorem. Raw row indices have
explicit range gates before decoding to `Fin`; physical masks and detector
supports also have range checks. Separate family data and check modules split
membership and capacity reduction into small blocks.

The checked capstones are `Distance566WeightedCoverage`,
`Distance566WeightedPacking`, `Distance566WeightedPauli`, and
`Distance566WeightedAudit`. Coverage uses 18 independent detectors in each sector
and separately paired witnesses. Z detector families bound X logicals; X detector
families bound Z logicals. The existing stored weight-twenty X witness is reused.

## Validation scope

All generation, tests, and Lean runs use detached bounded cluster allocations:
one CPU, one Lean thread, 8 GiB, zero swap, and 15–20-minute wall limits. Independent
family batches later use two disjoint allocations concurrently with user approval.
Replay reuses pinned dependency and earlier project artifacts; it is not a cold
build. Targeted Lean commands explicitly pass `-DautoImplicit=false` and
`-DmaxSynthPendingDepth=3`, with `-j1 -M7000`.

The final default locked suite passes 114 tests and skips one optional SciPy test.
All 22 weighted exploration tests also pass in the isolated SciPy environment;
that environment's initial focused run passes 34 cases in total. No search was
rerun. Ruff passes. Both emitter checks pass, including byte comparison of all
79 new generated modules. The prior ten distance modules regenerate identically.
The new rejection tests cover raw row ranges, changed row combinations, altered
weights and pairings, strict-threshold equality, source hashes, and line endings.

The final focused audit takes 95.92 seconds, with process RSS 2,004,592 KiB.
The largest new-module process RSS is 4,526,196 KiB. The combined replay's GNU time
report is 2,027,100 KiB; its scheduler-sampled batch RSS is 4,418,664 KiB. These
measurements have different scopes and do not establish a whole-allocation peak.
`module-results.json` gives all 84 source hashes, commands, resources, and successful
execution records. `capstone-and-audit-results.json` preserves the earlier audit
message failure separately from the corrected successful check. Only the usual
foundational axioms `propext`, `Classical.choice`, and `Quot.sound` occur; exact
subsets, including the range-gate dependencies, are guarded in the audit source.

Development failures concerned elaboration, isolated artifact layout, an optional
benchmark's recursion setting, or expected axiom messages. The successful finite
checks prove actual original-row membership, natural capacities and strict
thresholds. No parser, solver result, or numerical rank calculation is a trusted
assumption. Operational configuration and raw logs remain ignored.

## Reproduction and evidence

`proof-modules.txt` lists the exact 84-module dependency order, including 79
generated inputs. `source-sha256.txt` freezes 124 related source/input files.
Its SHA256 is `27875b80d70dd9e8daec469e4aeda5f4beb6a331621872a31dc47aa4f6d876f4`.
`standalone-validation.json`, `module-results.json`, `proof-artifacts-sha256.txt`,
`capstone-and-audit-results.json`, and `python-checks.json` are the execution handoff.
Both the ordered module inventory and the compiled-artifact inventory have explicit
paths and digests in the aggregate. `job-results.json` records terminal standalone
allocation states. `python-source-sha256.txt` captures the full Python test inputs.
`changed-files.txt` lists all 100 worker-owned additions; `artifacts-sha256.txt`
hashes the worker-owned evidence files. Parent reviews and integration files have
separate ownership and are excluded from that list.

Within a bounded allocation and a staged pinned upstream checkout, regenerate with
`uv run --locked python scripts/emit_distance566_weighted.py --check`. Omit
`--check` only to regenerate this new compact certificate and its new input files.
The immutable weighted source export is never overwritten. `replay.sh` replays
the new modules against retained baseline artifacts. Its optional zero-based
start/count arguments support bounded, dependency-ordered warm-cache slices.

Parent integration of the shared umbrella, main audit, and root documentation
owns the reserved `integration/` directory. The target's two detector bases remain
independent; the 578 controls receive no stronger kernel distance claim here.
