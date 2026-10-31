# Literal Z-sector proof replay

Status: all 61 modules passed kernel compilation. The theorem
`QldpcVerification.Distance566SectorZ.lower_Z` proves that every Z logical of the
literal submitted 566 matrices has physical Hamming weight at least seven.
The overall code bound remains `6 ≤ d ≤ 20`. Exact distance remains open.

`Distance566SectorZ.lean` combines fifteen detector families with seven
certificates for the remaining logical sectors. A sector specifies the logical
coordinates of a cycle. Each certificate uses representatives from different
classes and an actual physical reference with checked coordinates. Original HX
row differences establish reference pairing. Opposite-cycle membership ensures
that every representative annihilates Z boundaries. All seven nonzero suffixes
are covered, including sums of basis suffixes. Coordinates never change the
physical Hamming weight.

`Distance566SectorAudit.lean` passed 33 axiom guards and seven suffix/shift
controls. All dependencies use only `propext`, `Classical.choice`, and
`Quot.sound`. The public helper audit runs separately in parent integration.
That audit retains its 13 guards and twelve controls.

Seven generated modules reuse the frozen pilot. Bounded chunks compiled the
remaining 52 modules. One residual chunk reached its wall limit after eleven
successful modules. Recovery checked their source/object hashes and compiled
only its remaining module. The final literal allocation completed in 144 seconds.
The proof took 98.35 seconds and the audit took 16.15 seconds. Peak process RSS
for the proof was 2,191,452 KiB. Scheduler batch MaxRSS was 4,212,672 KiB.

Every allocation used one CPU/thread, an enforced 8 GiB memory ceiling, zero
swap, and a twenty-minute wall limit. The pinned versions are Lean
`4.30.0-rc2`, QECLean `fed020a7e6be12825196cbee7bbc1ba56554158c`, and Mathlib
`a3fde5017d59fa3cef8d4d24999f6b9b71b89a3b`.

In a detached allocation with pinned dependencies, follow `proof-modules.txt`.
Run each module from `lean/` with the direct compiler command recorded in its
receipt. The final two commands add profiler flags:

```bash
lean -Dprofiler=true -Dprofiler.threshold=100 -j1 -M7000 \
  -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  -o .lake/build/lib/lean/QldpcVerification/Distance566SectorZ.olean \
  QldpcVerification/Distance566SectorZ.lean
lean -Dprofiler=true -Dprofiler.threshold=100 -j1 -M7000 \
  -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  -o .lake/build/lib/lean/QldpcVerification/Distance566SectorAudit.olean \
  QldpcVerification/Distance566SectorAudit.lean
```

Use fresh real output directories and reject existing outputs or linked parents.
The final source/artifact identity check passed for all 61 modules. The
preservation comparison passed for all 621 earlier files and both generic
source manifests. No task allocation remains active.

`FROZEN.json` identifies the final sources. `source-artifact-map.json` links all
61 sources to accepted objects. `receipts/` records the final commands.
`chunks/` and `checkpoints/` retain earlier successful receipts. `template-v2/`
records the proof-only exporter correction for the good-family index.
The other 58 generated modules and canonical compact certificate remain
unchanged. The original generated pilot record remains unchanged.

`development/` retains earlier source candidates for failed or stopped runs.
These candidates are not the accepted proof sources. The final proof uses an
explicit cycle-membership transport and an explicit `code.homological` argument.
These arguments avoid expensive inference through literal matrix expressions.
The final proof also uses `Classical.choose` to select a certificate from
the finite coverage theorem.
