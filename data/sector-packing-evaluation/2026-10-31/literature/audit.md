# Targeted audit of packing within logical sectors

## Finding and present proof boundary

The proposal is consistent with standard stabilizer extension, relative minimum
distance, and overlap counting. No mathematical blocker was found under the
stated hypotheses. The useful addition is a coverage/sector adapter to the
existing counting theorem, together with successful finite certificates.
This audit makes no novelty claim and proves no new distance bound.

The rank-fifteen threshold-seven span is supplied by the parent investigation,
not independently checked here. Its unpruned families still need Lean
certification. The compact certificate preserves six only. Even a completed
Z-sector bound of seven would leave the overall proved lower bound at six
until the X sector also reaches seven. The present overall result remains
`6 <= d <= 20`; source-578 lower bounds of twenty remain unproved.

## A clean formulation on the same physical qubits

Write `B_Z = row(HZ)`, `Z = ker(HX)`, and let
`pi : Z -> H_Z = Z/B_Z` be the complete eighteen-coordinate logical map.
Let `U` be the span of the good X-detector classes, of dimension fifteen.
The perfect logical pairing gives `K = Ann(U)`, of dimension three.
The residual physical code pair is

`B_Z ⊆ Z_K := {z in Z | pi(z) in K}`.

Equivalently, add fifteen independent X detectors as X stabilizers. Because
they commute with HZ and are independent modulo the old X row space, the new
CSS ranks are `(289,274)`, so `k = 566 - 289 - 274 = 3`. Its Z logicals are
exactly `Z_K \ B_Z`. This follows from the standard stabilizer-space
construction in [Gottesman, §3.2, arXiv:quant-ph/9705052v1](https://arxiv.org/html/quant-ph/9705052).
Calling it **logical fixing by stabilizer extension** avoids confusing it with
physical puncturing. “Logical expurgation” is a useful description here, not
an attribution of that particular name to the cited source.

No physical coordinate is removed, and no weight is transported through a
logical-coordinate isomorphism. The norm remains Hamming weight on the same
566 positions. An adapter can use `Z_K` or the predicate `pi(z) in K` without
constructing augmented matrices. Rank-nullity and this annihilator description
are standard linear algebra, not new coding theorems.

The same stabilizer formalism gives the standard lower-bound monotonicity:
modulo Pauli phases, `S ⊆ S'` implies
`N(S') \ S' ⊆ N(S) \ S`. Therefore adjoining these commuting checks preserves
the old global lower bound of six. This is a direct deduction from
[Gottesman's normalizer characterization in §3.2](https://arxiv.org/html/quant-ph/9705052),
not a separately numbered expurgation theorem located by this search. It
does not establish seven without a new residual argument. Conversely, an old
upper witness may become a new stabilizer, so the original weight-twenty upper
bound must not automatically be attributed to the extended code.

There is a further standard simplification: the residual X logical space is
`H_X/U`. For a fixed nonzero `c in K`, exactly four of its eight classes pair
to one with c. Original detector classes differing by U become one class in
the extended code. Thus some useful mixing can already be viewed as
same-class packing after extension; allowing all four eligible residual
classes is the broader sector-specific option. Neither observation guarantees
a packing with sufficient physical overlap ratio.

### Optional scaling route: pool classes in the quotient and iterate

Representatives with the same image in `H_X/U` differ by an old X boundary
plus a lift of U. On `Ann(U)`, all those extra terms pair to zero. Such a pool
is literally one detector class in the extended code, so the fixed-class
packing results below apply there. If a nonzero quotient class acquires a
strict threshold-seven certificate, its detected residual vectors are now
bounded and its class can be added to U. Repeating reduces the remaining
annihilator dimension. This can avoid enumerating all 2,047 patterns on the
other sector if suitable pools are found; their existence and computational
tractability are not guaranteed.

The useful next lemma is conditional span extension: combine a bound already
proved outside `Ann(U)` with a bound for vectors in `Ann(U)` detected by the
new quotient class, obtaining a bound outside the smaller annihilator.
Certificate membership must allow old-row combinations **plus** good-span
terms; old-row-only class checks do not validate these enlarged pools.
This is a proposed application of standard quotient/stabilizer extension and
fixed-class weighted packing, not a located named iterative theorem or a
novelty claim. It leaves the initial seven-residue prototype unchanged.

## Existing results and their precise scope

### Audoux–Couvreur: overlap bounds

[Theorem 2.8, Corollary 2.11, and Lemma 2.7, arXiv:1512.07081v3](https://arxiv.org/html/1512.07081v3):
Theorem 2.8 assumes a binary CSS pair `C2 ⊆ C1^perp`, full-rank check matrices,
paired quotient bases `g_i,g_i*`, and, for every i, families in
`g_i*+C1` and `g_i+C2`, each with cardinality at least `N>0` and overlap at
most `K>0`. It gives
`d(C tensor D) >= ceil((N/K)*d(D))` for every CSS code D.
Lemma 2.7 requires at least one factor complex to be balanced; the discussion
after Theorem 2.8 permits separate bases for the two orientations.
Corollary 2.11 gives the single-complex bound `ceil(N/K)`.

This is a direct predecessor of the existing overlap argument and does not
require constructing a product to obtain the single-code bound. Its stated
families lie in individual detector cosets. Mixed classes satisfying only a
sector-dependent pairing condition are not its stated hypothesis.
**Next lemma:** derive uniform detector pairing within one coordinate fiber
from boundary orthogonality and `difference_mem_iff`, then invoke the existing
weighted bound. Do not replace complete coverage by a rank-deficient basis.

### Jochym-O'Connor–Kubica–Yoder: disjointness and scrubbing

[Lemma 2, proof Eq. (14), and Lemma 4, arXiv:1710.07256v1](https://arxiv.org/html/1710.07256v1):
for noncommuting nontrivial logical classes G and G',
`Delta_c(G) <= d(G')`, with support measured in a fixed qudit partition.
The argument counts intersections of a c-disjoint set of representatives of
G with an opposing representative. Lemma 4 states that for any region H and
`1 <= c <= m^(n-k)`, some `g in G` satisfies
`Delta_c(G) * |supp(g) intersect H| <= |H|`.

The common-anticommutation counting is the relevant match. The paper fixes a
single detector class; its original definition uses sets of distinct
representatives. It supplies neither the proposed mixed-class adapter nor
permission to repeat elements under that set definition.
**Next lemma:** isolate the already-proved common-pairing hypothesis in the
adapter. A reference-vector pairing alone is insufficient without boundary
orthogonality. Scrubbing guides representative selection but supplies no
automatic threshold-seven certificate.

### Bostanci–Kubica: weighted packing as an LP

[Theorem 5, Eqs. (27)–(31), arXiv:2108.04738v1](https://arxiv.org/html/2108.04738v1):
for any stabilizer code and fixed nontrivial logical Pauli class L, maximize
the sum of nonnegative representative weights subject to each physical-qubit
load being at most one. With a variable for every representative of L, the
optimum equals `sup_c Delta_c(L)`, attained at finite positive integer c.
This definition explicitly permits multiplicities.

This supports exact natural weights and finite primal certificates. The
theorem's class is fixed; the mixed-class LP needs the sector pairing argument
before it becomes a distance certificate. Restricting the available columns
still permits valid feasible packing certificates, but a restricted dual
optimum cannot exclude better representatives outside that list.
**Next lemma:** package the existing weighted theorem with a sector-dependent
finite family and exact `6*cap < totalWeight`. Floating-point output and
`6*cap = totalWeight` do not certify seven.

### Relative minimum distance and logical-coordinate codes

[Galindo–Geil–Hernando–Ruano, relative-weight definition and Theorem 3,
arXiv:1610.06363, latest metadata v3](https://arxiv.org/html/1610.06363)
records the standard nested-code formulation: for
`C2 ⊊ C1 ⊆ F_q^n`, the CSS sector distances are
`M1(C1,C2)` and `M1(C2^perp,C1^perp)`, where
`M1(C1,C2) = min wt(x)` over `x in C1 \ C2`.
Higher relative weights minimize the union of supports of a v-dimensional
subspace disjoint from C2; they are not simply the weights of v chosen vectors.

Here the residual Z objective is exactly `M1(Z_K,B_Z)`. This gives a concise
standard formulation of the target. The paper's polynomial-code constructions
do not automatically apply to these submitted matrices.
**Next lemma:** identify the residual logical predicate with
`Z_K \ B_Z`. Do not treat logical-coordinate Hamming weight as physical weight,
or bounds for three chosen basis vectors as bounds for all seven residues.

[Matsumoto, Theorem 1.1, arXiv:1405.0149v5](https://arxiv.org/html/1405.0149v5)
starts from any strict nested pair `C2 ⊊ C1 ⊆ F_q^n` and defines physical
coordinate projections `P_J` and their induced quotient maps. A set J can
recover `dim(Ptilde_J(ker Ptilde_complement))` secret qudits; full recovery is
equivalent to preserving the full quotient dimension on J and obtaining zero
quotient dimension on its complement. This is useful precedent for explicit
quotient-map and kernel bookkeeping, not a packing lower bound.
**Next lemma:** state the well-defined quotient/fiber map explicitly. The
projection criterion does not justify replacing 566 physical positions by
three logical coordinates for purposes of weight.

### Lifting, grafting, and surgery: extra distance hypotheses remain essential

[Cowtan–Burton, arXiv:2301.13738v6, Lemma 6.7](https://arxiv.org/html/2301.13738v6)
considers the separated logical-operator subcomplex and sandwiched pushout of
Definition 6.6. Its X-distance bound
`d_X(T) >= min(d_X(C),d_X(D))` additionally requires
`k_T = k_C + k_D - 1`. Definition 6.8 separately requires that merged Z
logicals have no weight below the initial direct-sum distance; Proposition
6.10 uses that requirement for the error-corrected procedure. Appendix F
exhibits a merge that lowers Z weight. Thus a valid gluing map alone is not a
distance-preservation certificate. **Next lemma for a construction route:**
prove the relevant logical map, dimension condition, and physical-weight
control, including the sector where new low-weight representatives can occur.

[Poirson–Roffe–Booth, arXiv:2505.01370, latest metadata v3,
Definitions 2.5–2.6 and §4.2.2](https://arxiv.org/html/2505.01370)
defines Z-preserving maps as chain maps and X-preserving maps as cochain maps.
They induce logical maps, but these definitions impose no Hamming-norm bound.
Section 4.2.2 requires sufficient auxiliary-code distance and identifies the
risk that introducing an auxiliary logical qubit degrades distance.
**Next lemma for lifting:** a nontrivial target logical must have an explicitly
nontrivial source lift with the required physical-weight inequality. A source
lower bound must itself be certified. Neither paper supplies the missing
unconditional source-578 lower bounds or a proof of target distance twenty.

## Concrete risks and required adapter obligations

* **Pairing must hold on the full fiber.** In `F_2^2`, take boundary space
  `B=span(10)`, reference `r=01`, and detector `h=11`.
  Then `h dot r=1`, but `h dot (r+10)=0`. Boundary orthogonality is essential.
* **A fiber is not a single-coordinate half-space.** On the sector `x1=1`,
  `h=11` pairs to one with `10` and to zero with `11`. Mixed detectors must
  work for the entire claimed sector, or the sector must fix the full residue.
* **Sums matter.** Vectors `11111110` and `11111101` both weigh seven, but their
  sum weighs two. Check all seven nonzero elements of the three-dimensional
  annihilator, not only its three generators.
* **Extension bounds do not transfer backward by themselves.** For a
  three-qubit CSS example with `HX=[110]` and empty HZ, the Z minimum is one
  (`001`). Adding `001` as an X check leaves residual Z minimum two (`110`).
  This improvement for the extended code says nothing about the eliminated
  original class unless the good-family argument handles it.

The implementation can therefore remain small: certify the good detector
rank and original threshold-seven families; classify the annihilator; build a
reference for each nonzero residue; use `difference_mem_iff` and orthogonality
to transfer pairing to every physical representative; check a weighted family
and strict threshold for every residue; combine the detected/residual cases.
These are proposed obligations, not claims that new Lean declarations already
exist. The parent's description of current interfaces was taken as input;
this audit did not inspect or modify their implementation.

## Priority and limits

Prioritize the seven residual Z classes and the generic adapter. The same
analysis leaves 2,047 nonzero classes on the rank-seven X side, so bound its
pilot budget separately. Successful Z work alone does not raise the overall
lower bound. Physical-weight-controlled lifting or grafting is a later route
unless it supplies both a proved source bound and the missing norm control.

Five targeted TinyFish queries were used. One returned no results; several
hits were off topic and were not used as theorem evidence. Five additional
primary papers were fetched, plus the surgery publisher page and three
bibliographic version pages. Three seed papers were reused from the preceding
sidecar's inspected statements instead of fetched again. All fetches succeeded.
The unversioned full-text endpoints for two papers were identified as latest
v3 by their abstract-page metadata; no PDF/HTML identity check was performed.
The theorem numbering is that of the fetched HTML, not an independently
compared publisher PDF.

The complete deduplicated URL set and per-URL access status are in
[sources.json](sources.json): nineteen URLs in this extension, twenty-seven
including the preceding sidecar. The count includes search-only hits and the
earlier snippet-embedded URL, not just the eight papers whose relevant text was
read across the two passes. Unvisited outbound references and static assets
are excluded. Fetch snapshots remain ignored under
`.local/sector-packing/literature/`.

This bounded search cannot establish absence of prior work or novelty. No
numerical hypotheses, parser results, Lean proofs, physical matrices, tests,
or cluster execution were verified by this audit. Only this literature
directory and its assigned ignored cache were written.
