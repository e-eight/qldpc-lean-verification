# Analytic family-theory verification

All 41 modules in the ordered replay passed. The run checked 131 guarded
axiom commands, including 86 in the eight new family audits. Every guarded
result uses only a subset of `propext`, `Classical.choice`, and `Quot.sound`.
No audited capstone depends on `sorryAx` or `native_decide`.

This is the historical family-development replay. Later integration and commit
packaging are recorded in the [instance-integration record](../../family-integration-evaluation/2026-11-12/).
Its commit-scope record distinguishes the selected package wiring from the
pre-existing local 566 edits present when these historical hashes were captured.

The results are:

| Construction | Proved statement | Complete hand proof |
| --- | --- | --- |
| Arbitrary positive cyclic binomial period and steps | Both ranks m−c, k=2c, both exact distances equal the shortest relation norm, c=gcd(s,t,m) | [Cyclic proof](../../../analytical/cyclic-distance/PROOF.md) |
| Coprime rotated-square parameters a>0,b≥0,h>0 | Exact [[2h(a²+b²),2,a+b]] | [Same complete proof](../../../analytical/cyclic-distance/PROOF.md) |
| Open M×N rectangle, M,N≥2 | Both ranks, k=8, dX≥M−2, dZ≥N−2, mixed bound min(M,N)−2 | [Rectangle proof](../../../analytical/rectangle-family-distance/PROOF.tex) |
| Exact polynomial strip of length L≥3 | Weight≥L−2; L−1 absent the directional missing exit | [Strip proof](../../../analytical/strip-family/PROOF.tex) |
| Uniform repetition factor r≥1 | k preserved, exact sector distances (dX,r*dZ), fixed-r sparsity | [Repetition proof](../../../analytical/qubit-replication/PROOF.md) |

Each final document has three independent hostile document-only passes and
an adversarial author/root rereading. The cyclic component extension received
three further passes. The assembled physical rectangle proof received three
fresh passes. Their `REVIEWS.md` files record scope, checks, and resolutions.
The independent [rectangle rank proof](../../../analytical/rectangle-family/PROOF.md)
has its own three passes.

## Verification scope

This is a **warm-import replay**, not a cold build of the whole package.
It compiles all new family modules and their aggregate, the three refactored
fixed-length strip modules, their audits, the existing 722 distance-15 and
distance-17 theory, and the model/submitted distance-17 capstones and bounds
audits. The 56 original public strip declaration headers are unchanged;
502 net lines of duplicated proof were removed.

The full legacy package/main `KernelAudit` replay remains outside this record
because inherited build artifacts are missing. The package umbrella now imports
`FamilyTheory`, and the main audit imports `FamilyTheoryAudit`. The new aggregate
and all its capstones were checked directly in this replay.

The sum of compiler times is **196.253 seconds**. The reported maximum child
process RSS is **4,271,908 KiB**; this process accounting includes mapped imports
and is distinct from service memory accounting. Enforced allocation limits were
5 GiB memory, 128 MiB swap, one CPU, one Lean thread, 1,200 seconds wall time,
and 1,140 seconds CPU time. Raw logs remain under ignored `.local/`.

Repository Python lint and formatting checks passed. The replay helper also
passed an explicit Ruff check. No Python generator or application behavior
changed, so the Python regression suite was not rerun for this Lean-only change.

## Records and reproduction

- [results.json](results.json): theorem scope, guard counts, limits, toolchain and dependency pins, final proof hashes.
- [replay.json](replay.json): ordered compiler outcomes, timing, and unchanged source hashes for all 41 modules.
- [source-hashes.json](source-hashes.json): hashes of all 130 project sources in that dependency closure.
- [replay.py](replay.py): exact ordered replay. It verifies that each source stays unchanged during its check.

With the pinned dependencies and toolchain already available, run from the
repository root using Python 3.13. Launch Lean only inside a detached allocation
with enforced memory and swap limits. The local run used:

```bash
systemd-run --user --unit=qldpc-family-theory-replay \
  --property=MemoryMax=5G --property=MemorySwapMax=128M \
  --property=CPUQuota=100% --property=RuntimeMaxSec=1200 \
  --property=LimitCPU=1140 --working-directory="$PWD" \
  /usr/bin/python3 data/family-theory-evaluation/2026-11-12/replay.py
```

The helper sets `LEAN_NUM_THREADS=1`, uses the retained pinned toolchain when
present, and writes raw output to `.local/family-theory-2026-11-12/`. It does
not itself allocate resources; do not run it as uncapped foreground Lean.

## Attribution

The construction and geometric framework are established mathematics.
The literature check verified the relevant primary sources: Arnault, Gaborit,
and Saussay, [arXiv:2507.21237v1](https://arxiv.org/html/2507.21237v1),
Theorem II.7, Corollary II.8, Section II-E2, and Lemma IV.4; Liang, Eberhardt,
and Chen, [arXiv:2504.08887v4](https://arxiv.org/html/2504.08887v4), Section II;
Breuckmann et al., [arXiv:2511.14589v1](https://arxiv.org/html/2511.14589v1);
and Gottesman's [1997 thesis](https://thesis.caltech.edu/2900/02/THESIS.pdf),
Sections 3.5 and 6.1. The proof documents give the precise scope of attribution.
No mathematical priority claim is made. No numerical certificate or search
is a load-bearing step in any new analytic proof.
