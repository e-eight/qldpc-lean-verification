# Analytic verification records — 2026-11-11

The JSON records distinguish final mathematical scope, source/dependency hashes,
successful focused Lean replays, timing/RSS scopes, and whole-package limitations.
The new-result Lean proof checks used detached allocations, one Lean thread, one CPU quota,
5 GiB memory and 128 MiB swap caps, and 300 s or 600 s wall limits. Raw operational logs
remain under ignored local storage. `children_peak_rss_kib` is the running maximum RSS of completed child
processes within that replay allocation. It is neither a per-module increment
nor the aggregate memory of the allocation.

- `rectangle722-distance15.json`: complete explicit-model sector and Pauli lower
  bounds 15, ranks 357 and k = 8. The combined proof has three final clean referee
  verdicts and a final author self-audit.
- `charge722.json`: complete logical charge maps and the earlier model bound 9.
- `planar722.json`: explicit finite matrix commutation/ranks/quotient dimension
  and QECLean-backed CSS coordinate transport.
- `strip-deficits.json`: the standalone polynomial strip theorem≥15.
- `small-support.json`: the reusable column-collision criterion.
- `lattice562.json`: symbolic shortest-vector arithmetic and existing 562 replay.

The final artifacts are indexed in [analytical/README.md](../../../analytical/README.md).
No record claims exact distance twenty. Fixed submitted-input recognition now
passes for all714 rows. The package umbrella and main audit received additive
entries. Whole-package replay remains pending: the initial checkout lacked269
inherited own-package compiled modules and cluster authentication was unavailable.
Bounded local restoration has since resumed. All
new claimed capstones have successful focused guarded audits. Those audits allow
only subsets of propext, Classical.choice and Quot.sound; they exclude sorryAx
and native_decide.

The final submitted result is recorded in `submitted722-bounds.json`: ranks357,
k8 and 17<=d<=20, with the literal 714-row input adapter and explicit witnesses.
The 42-page self-contained LaTeX proof and its PDF are in `analytical/rectangle722-submitted`.
Exact distance20 remains open. Thirty-five inherited missing build artifacts have
been restored; full package replay is still pending.

The revised main text foregrounds the cheap-exit and disjoint-excess argument.
Established algebra, ranks and boundary charges are fully proved in appendices
with primary references. Three fresh document-only reviews pass. The numerical
data, seven local lemmas and disjoint counting proof are unchanged.

All analytical documents were converted from Typst to LaTeX on 2026-11-11 and
the `.typ` sources were removed. Each record's `source_sha256` now names the
`.tex` files, regenerated PDFs and updated scripts. Its `document_revisions`
entry lists every replaced hash; the reviewed Typst sources remain in commit
`fa8b57a2d87f41e04ba9b5f5c1ed62e3debf511a`. Lean changes in that revision are
comment-only, so the recorded Lean replays were not rerun.
