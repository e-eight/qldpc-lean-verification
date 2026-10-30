# Kernel certificate for twelve removals from 578 to 566 qubits

The certificate connects the literal submitted matrices at [upstream revision 8c87413d](https://github.com/unitaryfoundation/qldpc-challenge/tree/8c87413d16b78cdd934b7b7a8592cddc81ae6eed).
Thirteen physical matrix stages give six X removals and six zero-fan Z cleanups.
This is a reconstructed legal sequence, not the missing historical random-search trace.

| Endpoint | Physical qubits | X rank | Z rank | Encoded dimension |
| --- | ---: | ---: | ---: | ---: |
| Source | 578 | 280 | 280 | 18 |
| Target | 566 | 274 | 274 | 18 |

Every intermediate stage also satisfies `n-rankX-rankZ=18`.
The existing matrix bridge gives these logical predicates their QECLean homological meaning.

## Formal scope

The namespace is `QldpcVerification.Removal566`.
The `source_HX/HZ` and `target_HX/HZ` theorems identify the literal matrices.
Each `Stage*.step_eq` identifies a physical permutation and reversible pivot-row clearing of the elementary normal form.
The six Z operations use CSS duality.

The `ranks` and `encoded_dimensions` capstones have no distance hypotheses.
The distance capstones state:

- `lower_X`: a source X lower bound D transfers unchanged.
- `lower_Z`: a source Z lower bound D transfers as `Nat.sub D 6`.
- `conditional_twenty`: source lower bounds twenty on both sides imply target X/Z lower bounds twenty/fourteen.

No source lower bounds of twenty are supplied here.
This proves no unconditional target distance of fourteen or twenty.
The nineteen submitted exact-distance instances remain nineteen.
The reverse composite Z comparison and exact block minimum formulas remain mathematical derivations in the [investigation](../lifting-566-investigation/).

## Finite certificates and review

The generator emits 39 input modules.
Kernel checks validate raw index ranges, all twelve sparse row matches, final commutation, and both independent rank certificates.
The commutation and rank checks use complete blocks of sixteen outer rows.
Checked append identities preserve the full matrix and the global indices.
No `native_decide` or `sorryAx` occurs in audited dependency closures.

A separate reviewer checked the mathematical interfaces, literal endpoints, every row transformation, both binary rank identities, and the block coverage.
The reviewer found no correctness issue or missing hypothesis after the implementation fixes.
The focused audit guards 128 targets, including all 28 no-wrap gates.
The integrated main audit guards 256 targets.
All ten audits pass using only subsets of `propext`, `Classical.choice`, and `Quot.sound`.

## Replay

Use Lean 4.30.0-rc2 with the pinned dependencies and their caches ready.
Put the matching toolchain binaries first on PATH.
The ordered list in `proof-modules.txt` contains 55 proof modules.

Run one module or a small sequential group inside each detached, resource-limited allocation.
For example, from the repository root:

```bash
systemd-run --user --unit=qldpc-removal566-replay --collect \
  --working-directory="$PWD" \
  --setenv=PATH="$PWD/.tools/lean-4.30.0-rc2-linux/bin:$PATH" \
  --setenv=LEAN_NUM_THREADS=1 \
  -p MemoryMax=5G -p MemorySwapMax=128M -p CPUQuota=100% \
  -p RuntimeMaxSec=300 -p LimitCPU=280 -p Nice=10 \
  bash data/removal566-evaluation/replay.sh \
  QldpcVerification.QubitRemovalTransport
```

Check completion before starting the next allocation.
After all modules finish, pass `--audit` in a bounded allocation to rebuild the package root and run all ten audits.
The script compiles directly and sequentially with `lake env lean`.
It does not impose allocation limits itself.
Do not put the entire module list in a single five-minute allocation.

Python checks are:

```bash
uv run --locked python scripts/emit_removal566.py --check
uv run --locked pytest -q
uv run --locked ruff check .
uv run --locked ruff format --check .
```

The generator enforces a 1 GiB address-space limit and 120-second CPU/wall limits.
It checks the two pinned raw JSON hashes and byte-for-byte regeneration.
The parser and generator remain outside the kernel.

## Resources and provenance

All Lean jobs used detached user-systemd allocations with a 5 GiB memory cap, 128 MiB swap cap, one CPU, and one Lean thread.
Recorded build allocations had wall limits of at most 300 seconds.
The final integration took 37.39 seconds with dependency and project caches retained.
It rebuilt the package root and ran the audits. It was not a cold build.
No cluster job ran.

A monolithic commutation attempt exhausted its allocation.
A single-file blocked attempt reached its time limit.
The successful checks use separate compilation units.
A combined rank/theory allocation also timed out after finishing its finite rank work.
The theory was split and its elaboration was improved without repeating those finite checks.

`max_child_rss_kib` and cgroup charged-memory peaks have different scopes.
MemoryMax caps charged memory, rather than the reported per-process RSS.
Keep these measurements distinct.

All 68 Python tests, Ruff, and shell syntax checks pass.
Earlier datasets, archived proofs, and dependency pins retain their original bytes.
Among existing proof sources, only the root import and main audit change.

`evaluation.json` records source/pin hashes, inputs, audit names, review scope, measurements, and limitations.
`worker-build-results.json` includes selected successful, partial, and failed resource attempts.
The journal excerpts omit host names, process identifiers, and private paths.
Exact operational records remain under ignored `.local/` storage.
The [literature assessment](../removal566-literature/) makes no novelty or first-formalization claim.
