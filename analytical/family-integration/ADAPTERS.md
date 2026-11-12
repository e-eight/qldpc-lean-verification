# Normalized matrix recognition and shortest-relation integration

**Grade: THEOREM.** The transfer argument passed three independent document-only reviews and bounded Lean verification.

## Statement

Let m be a positive integer and a a nonnegative integer. Suppose binary matrices
HX,HZ are recognized by the existing normalized cyclic interface: there is a
bijection between their n physical coordinates and the labelled edges
{h_v,v_v : v in Z/mZ}, surjective vertex labels for each set of rows, and after
that bijection the X rows are the vertex incidence checks for steps 1,a and
the Z rows are the square checks for those same steps. Let D be a natural number.
If every nonzero integer pair (u,v) with m dividing u+av has |u|+|v| at least D,
and one such pair has norm exactly D, then the recognized matrices have two
encoded qubits and both CSS distances exactly D. Separate physical logical
supports are not additional inputs to this theorem.

## Definitions and exact identification

The field is F2, with addition modulo two. A physical binary vector is a
function on the finite set of matrix columns; its Hamming weight is the number
of coordinates with value one. For a matrix, its row space is the set of all
binary linear combinations of its rows. An X logical is a vector in ker(HZ)
outside row(HX); a Z logical is a vector in ker(HX) outside row(HZ). Exact sector
distance D means both that every logical in that sector has weight at least D
and that some logical in that sector has weight D.

For every residue z, the normalized construction has labelled horizontal edge
h_z from z to z+1 and labelled vertical edge v_z from z to z+a. Its vertex row
is the sum of the four coordinate vectors at h_z,h_(z-1),v_z,v_(z-a).
Its square row is the sum at h_z,v_(z+1),h_(z+a),v_z. All sums are in F2;
repeated appearances cancel rather than deleting the edge labels.

The jointly generated cyclic construction with steps s,t has exactly the same
formulas with 1 replaced by s and a replaced by t. Setting s=1,t=a therefore
makes both row functions identical at every residue and every labelled edge.
This also covers a=0, repeated endpoints, and m=1, because these are identities
of sums rather than assumptions that four appearances are distinct.

## Proof of the transfer

Reuse the same two matrices, physical-coordinate bijection, and row-label
functions from the normalized recognition. Their surjectivity is unchanged.
The row identities just proved give recognition by the jointly generated
interface. The resulting CSS code has literally the same HX and HZ. Its
commutation proof may have a different expression, but commutation is a
proposition; the two records have the same mathematical data. Thus their
stabilizer spaces, cycle spaces, logical predicates, ranks, and physical weights
are equal. No change of support or weight is performed by this adapter.

The steps 1,a jointly generate Z/mZ because repeatedly adding 1 reaches every
residue; equivalently gcd(gcd(1,a),m)=1. Apply the proved connected
shortest-relation theorem to these recognized matrices, the supplied analytic
lower bound, and the supplied attaining integer pair. That theorem constructs
a closed signed path of the attaining length, proves that a shortest relation
cannot have both binary winding coordinates zero, and obtains both physical
logical witnesses by its weight-preserving duality. It concludes two encoded
qubits and both exact CSS distances D, precisely as asserted.

The complete proof of the invoked cyclic theorem is included in
`analytical/cyclic-distance/PROOF.tex`; this integration note records only the
new recognition adapter, not a replacement for that full proof.

## Formal correspondence and dependency requirement

`Bicycle/NormalizedShortest.lean` defines `Bicycle.Match.connected`, proves
`connected_code`, and exports `Bicycle.Match.parameters_of_shortest`. Its
`parameters_minimum` also directly identifies both distances with the least
nonzero relation norm. The implementation invokes the already audited
`Connected.Match.parameters_of_shortest` and `parameters_minimum`.

Every migrated instance capstone calls the new normalized adapter with its
analytic arithmetic module's `bound` and `shortest_relation`. Stored physical
witnesses and their check lemmas remain available under their old public names
as independent controls, but the exact parameter proof does not invoke them.
The arithmetic modules have separate symbolic proofs and are reproduced through
the generator. This is an interface integration of proved mathematics, with no
claim of a new mathematical construction.


---

# Literal specialization of the open-rectangle family at nineteen by nineteen

**Grade: THEOREM.** The specialization argument passed three independent document-only reviews and bounded Lean verification.
The result here is an equality of code definitions and its transfer rule.
The family rank and distance theorems already have their complete independent
proof in `analytical/rectangle-family-distance/PROOF.tex`; no new distance
claim is assumed in the equality argument below.

## Main theorem

Define the fixed nineteen-by-nineteen check matrices and the two-parameter
family matrices by the formulas below. After the displayed finite-index
ordering, the fixed matrices equal the family matrices at parameters
`m=n=17`, entry for entry and in the same row order. Consequently their CSS
codes, logical predicates, and Hamming weights agree. If another ordered pair
of matrices has the same indexed rows as the fixed matrices, the same conclusions
hold for it by transitivity.

## Definitions and row identities

All entries lie in the two-element field F₂, in which addition is modulo two.
Let the three exponent pairs of f and g be respectively

\[
S_f=((1,0),(2,0),(0,2)),\qquad
S_g=((0,0),(2,1),(2,2)).
\]

The fixed board consists of the cells `(i,j)` with `0≤i,j<19`, with two
species `b∈{0,1}` at every cell. Its X row indices are `(a,b)` with
`0≤a<21,0≤b<17`; its Z row indices are `(c,d)` with
`0≤c<17,0≤d<21`. For a cell q and integer pair p, put `δ(q,p)=1` when
q=p and zero otherwise. Its X row at `(a,b)` has species-zero entry

\[
\sum_{s\in S_f}\delta((i,j),(a-2,b)+s)
\]

and species-one entry with `S_g` in place of `S_f`. Its Z row at `(c,d)`
has species-zero entry

\[
\sum_{s\in S_g}\delta((i,j),(c+2,d)-s)
\]

and species-one entry with `S_f` in place of `S_g`. Each displayed sum
has exactly three listed summands. No periodic coordinate identification
is used: a lattice point outside the board contributes to no cell.

For nonnegative parameters m,n, the family has cells
`0≤i<m+2,0≤j<n+2`, X row indices `0≤a<m+4,0≤b<n`, and Z row indices
`0≤c<m,0≤d<n+4`. Its entries use precisely the same four formulas just
displayed. Substitution m=n=17 gives

\[
m+2=n+2=19,\qquad m+4=n+4=21.
\]

Thus the domains of all row and column indices are equal. For each allowed
index the anchors `(a-2,b)` and `(c+2,d)`, each of the three shifts, and the
delta predicate are unchanged. Each of the four entry formulas is therefore
equal term by term. The two species exhaust all columns. This proves both
matrix equalities without listing or evaluating the 357×722 entries.

## Finite orderings

Both constructions send a physical coordinate `(b,(i,j))` to

\[
q=361b+19i+j\quad(0\le q<722),
\]

send X anchor `(a,b)` to `r_X=17a+b`, and send Z anchor `(c,d)` to
`r_Z=21c+d`. These maps are bijections. To recover the physical coordinate,
divide q by 361 to recover its quotient b and remainder t; then divide t
by 19 to recover i and j. The specified ranges make both divisions unique.
For X rows divide r_X by 17; for Z rows divide r_Z by 21. Division by a
positive integer has unique quotient and remainder: if `dk+r=dk'+r'`
with `0≤r,r'<d`, then `d(k-k')=r'-r`, and the only multiple of d strictly
between −d and d is zero. Thus r=r' and k=k'. Each inverse is in its
specified range because the original index is below the product of the
two factor sizes.

The bijections in the two constructions are identical, so reindexing the
already equal matrices retains equality and row order. No column or row
permutation is introduced by this integration.

## Transfer of code statements

For binary matrices A,B with `ABᵀ=0`, define an X logical to be a vector
in `ker B` outside the row span of A, and a Z logical to be a vector in
`ker A` outside the row span of B. Matrix equality implies equality of
the corresponding linear maps, kernels, and row spans. Hence it implies
equality of both logical predicates and both ranks. The physical coordinates
are the same and Hamming weight counts their nonzero entries, so every
vector has exactly the same weight under both descriptions.

A CSS code record also contains a proof that the checks commute. Equality
of these proof fields is immaterial to the mathematical structure: its data
are exactly the two matrices. In Lean, proof irrelevance makes the records
equal once the matrix fields agree. The transferred commutation proof now
comes from the family commutation theorem at `(17,17)`.

Suppose a further pair of matrices A',B' satisfies A'=A and B'=B, preserving
the stated row and column indices. Transitivity of equality identifies it
with the family member too. Its logical and weight statements therefore
transfer by the argument above. This is exactly the interface used for
the pinned submitted arrays: their existing sparse row-identification
theorems supply A'=A and B'=B. Those input identities and input data are
unchanged by this integration.

## Formal integration inventory

`Planar/Rectangle722Family.lean` proves the two matrix equalities by `rfl`,
then specializes family commutation. `Rectangle722.code_eq_family` proves
equality of the finite-index code records by `rfl`. The existing `rankX`,
`rankZ`, and `encoded_qubits` now apply the family theorems through that
equality. `Rectangle722.x_lower_seventeen` and `z_lower_seventeen` similarly
apply the family lower bounds; the earlier bounds fifteen and nine are
their arithmetic weakenings. Their public statements are unchanged.

`Rectangle722Submitted.code_eq_family` composes the unchanged sparse input
recognition with the equality above. The submitted rank, dimension, and
lower-bound capstones now call the family results directly. The weight-twenty
upper witness and its proof remain unchanged. Thus the final submitted
parameter/bounds theorem combines the family lower bounds with the existing
independently proved upper witness, while retaining the original literal
matrices and theorem names.
