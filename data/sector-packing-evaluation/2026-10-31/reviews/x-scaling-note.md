# Bounded X-scaling note

The X pilot validates 32 of 2,047 residual patterns; 2,015 remain untested.
The greedy disjoint diagnostic found no seven-unit family in those 32 cases.
This does not establish infeasibility. Preserve weighted certificates as the
baseline, following the reviewed [fractional-packing literature](../literature/audit.md).

One mixed certificate can cover several patterns. Let its positive-weight
Z-detectors have quotient labels `q_i in F₂^11`, expressed in the frozen
selected basis. Put those labels in the rows of Q. The exact common-pairing
region is

`R = {c in F₂^11 : Qc = 1}`.

When consistent, `R = c₀ + ker(Q)` has `2^(11-rank(Q))` elements and excludes
zero. Equivalently, a proposed affine region `c₀ + V` is covered precisely when
every used detector satisfies `q_i·c₀=1` and annihilates V. Checking a basis of
V suffices for the latter condition. A certificate covering c and d cannot
also cover `c+d`: its detectors pair zero with that sum. Affine regions must
not be confused with linear subspaces or a list of basis patterns.

Minimum certificate checks: pin the literal matrices, paired basis and pool;
derive each used quotient label from physical pairings; check each detector's
own-base row witness and annihilation of X boundaries; verify the affine offset
and direction-basis equations; and recompute natural weights, all 566 physical
loads, capacity C and total W with `6*C < W`. Reference cycles and complete
coordinates transfer these pairings to physical representatives. Claiming the
*maximal* region or its stated cardinality additionally requires certified
kernel completeness/rank. A complete X result still needs coverage of every
remaining nonzero residue, alongside the known-good prefix.

The supplied current-table fact matters: its 64 X-bound detector classes have
57 distinct nonzero quotient images. Pooling equal quotient images therefore
offers no extra cross-class collision in this stored pool. This does not
restrict future enrichment or mixing different labels over a common region.

Next bounded experiment: select at most two pairs from the existing 32 patterns;
intersect their compatible stored pools and attempt one weighted packing per
pair, with at most four LP seconds each and a thirty-second soft total budget
in a future bounded allocation. Record exact region constraints and thresholds.
Stop and assess if this restriction loses seven; failure remains pool/search
limited. No full 2,047-pattern campaign is proposed here.

This is a planning reformulation, not a new theorem or kernel result. No algebra,
search, LP, tests, or cluster computation was run for this note.
