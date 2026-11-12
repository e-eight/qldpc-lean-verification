# Normalized matrix recognition and shortest-relation integration

**Grade: PROPOSITION pending independent review and final bounded Lean audit.**

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
`analytical/cyclic-distance/PROOF.md`; this integration note records only the
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
