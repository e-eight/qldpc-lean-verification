# Independent review record

The reviewed artifact is `DRAFT.tex`, SHA-256
`8b89163ceed05a1132e98b12d10b4adcfa9de6b06ba3e344d002d06ea3a2f2b7`.
All three referees were fresh agents with no inherited conversation history.
Each was instructed to read only this complete proof document, to consult no
code, other reviews, numerical data, historical reasoning, or external sources,
and to find a fatal mathematical flaw. All three read the complete document.

## Referee 1

Agent: `/root/planar_family/distance_referee_one`.

Verdict: **PASS for the analytic mathematical theorem.** No fatal flaw or
missing load-bearing lemma was found.

The referee checked finite commutation, both ranks, dimension eight, all
zero-parameter cases, complete syndrome ranges, reflected Z orientation,
permitted peeling anchors, support shrinkage at transverse size two,
zero-length induction bases, gap splitting, both directions of every local
gap lemma, all singleton cases, the cheap-exit cancellations, recurrence
indices, short-run propagation, exact endpoint exception, disjoint excess
allocation, physical weight identities, and the mixed Pauli conclusion.

The pass expressly excludes certification of Lean, replay, axiom auditing,
bibliographic assertions, and formalization coverage.

## Referee 2

Agent: `/root/planar_family/distance_referee_two`.

Verdict: **PASS for the self-contained mathematical theorem.** The referee
independently rederived the equations and found no load-bearing gap.

The referee verified that X and Z strip support bounds retain every overlap;
rederived the two rank eliminants; checked all four zero/nonzero parameter
cases; derived the reflected synthesis and backward syndrome; verified both
peeling inductions and degree restrictions; checked every local gap case and
its distinct polynomial exponents; verified both cheap-exit classifications;
and checked the disjoint baseline/additional-unit allocation, including
`z=0`, `z=1`, and `L=3`. Physical and mixed Pauli weights were checked.

One optional editorial suggestion was to state the full shifted Z-synthesis
index range and transverse anchor support again in the peeling section.
The referee explicitly said these bounds already follow from the defined
reflected anchors and are **not a proof gap**. The paper retains the proved
ranges in the definitions and rank-reflection section. No mathematical
objection survives.

The pass expressly excludes certification of Lean, replay, source code,
numerical evidence, and external references.

## Referee 3

Agent: `/root/planar_family/distance_referee_three`.

Verdict: **PASS for every nonnegative pair of parameters.** No fatal flaw or
unresolved load-bearing gap was found.

The referee checked finite projection and empty anchors; the two ranks;
complete syndrome ranges; reflected species order and synthesis shift;
allowed degree/anchor bounds in both peeling directions; termination and
empty-support bases; gap separation; both versions of all local inequalities;
run propagation and cheap exits; disjoint excess reservations; endpoint
exceptions and the minimal strip length three; and physical/mixed weights.

The pass expressly excludes certification of Lean, replay, novelty,
bibliography, and sharpness.

## Author adversarial rereading

The author read the complete assembled draft from its beginning. That reading
led to explicit definitions of cycles and stabilizers, explicit coefficient
pairing with matrix checks, the full reflected X-anchor range underlying the
Z recurrence, empty-prefix/suffix cases, and a separate written Z gap-split
argument. These changes preceded the three final passes above. Rank equation
tags and lemma numbering were separated from the strip lemma numbering.
The assembled source passed two pdfLaTeX draft-mode runs with no undefined
references, overfull boxes, or warnings.

No search or numerical certificate supplies a mathematical proof step. The
artifact remains graded PROPOSITION until the full family Lean replay and
all guarded audits pass and the final author audit is recorded.

## Final root audit and kernel verification — 2026-11-12

The root reread every line of the assembled proof from the main statement
through the final section. In particular, the reflected Z packets, boundary
anchor ranges, transverse degree-two shrinkage at size two, split-cycle
argument, empty parameter cases, distinct physical weights, cheap-exit
classification, and disjoint allocations were independently checked. No
load-bearing objection remains.

All physical X/Z modules and the 24-target family-distance audit now pass.
The initial Z synthesis kernel timeout was resolved by proving reversal on
an abstract scalar array, so the kernel need not unfold the entire polynomial
synthesis. Resource caps were unchanged. The final distance adapter uses
direct additive identities in characteristic two.

The final proof differs from the reviewed draft only in its acceptance grade
and updated formalization inventory. No mathematical statement or proof changed.

Final `PROOF.tex` SHA-256: `6b5f875cdbecb00ff3e2f0f49c4efc9511160f5ee8ce7b1f748389102350a331`.

> **Source format note (2026-11-12).** `PROOF.tex` and `DRAFT.tex` were later
> brought to the analytical LaTeX standard: numbered displays, lemma and proof
> environments, and labelled cross-references instead of hard-coded numbers. One
> sentence in the rank--nullity proof was reworded to avoid an overfull line. No
> mathematical statement or proof changed. The hashes quoted in this record name
> the reviewed files in commit `cee205f5615f9404e1b27eafd7513604663abe95`.
