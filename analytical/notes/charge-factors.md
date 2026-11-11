# Charge factors and physical hypergraph connectivity for rectangular722

All results below are **PROPOSITION — pending independent review and
formalization**, except statements explicitly marked **FALSE** or **CONJECTURE**.
No Lean runs or numerical distance search are used. The input is the explicit
model in `analytical/charge722/PROOF.typ`, especially its charge completeness
results (Theorems 5–7). This note does not use the strip-deficits argument.

The main conclusion, strengthened in the continuation below, is concrete:
**every cycle with two qubit-disjoint boundary paths has physical weight at
least 20, in either sector.** This includes all nonzero pure-mode logicals.
For mixed charges, singleton-cut labels lie in one lattice coset; straight-cut
geometry gives physical bounds of 14 for X and 13 for Z, plus stronger path
costs for certain bottleneck displacements. The set-endpoint argument below
now proves W≥20 whenever consecutive X bridges have singleton displacement
(3,13). It also supplies an additive inequality for all bridge regions.
A cycle with exactly one bridge now has weight at least 19: the two-transition
weight-18 configurations are excluded by the local identities below.
Any nontrivial cycle of weight below 20 has at most two distinct bridge centers
and at most four bridge qubits. The final reduction below derives the remaining
lattice-displacement families and their boundary restrictions without enumeration.
Exact distance 20 remains open for mixed classes. All new statements retain
the pending-review grade above.

## 1. Factorization, fields, and exact periods

**PROPOSITION 1 (pending review/formalization).** Over F₂, put

\[
a=x^3+x^2+1,\qquad b=x^5+x^4+x^3+x^2+1.
\]

Then the charge algebra has the following presentation and decomposition:

\[
\mathcal A=\mathbf F_2[x]/(p),\quad p=x^8+x^5+1=ab,
\qquad \mathcal A\cong\mathbf F_8\times\mathbf F_{32}.
\]

Writing α and β for the respective images of x, the images of y are

\[
y\longmapsto (\alpha^3,\beta^{26}).
\]

Both x and y have exact order 7 in the first factor and exact order 31 in
the second. Thus x and y have exact order 217 in the product.

*Proof.* The x-presentation follows from Theorem 5 of the input: its eight
powers of x form a basis and satisfy p=0. For the y substitution one can use
the closed identities

\[
x^2(x^6+x^3)=1\pmod p,
\qquad y=x^{-2}+x+x^2=x^6+x^3+x^2+x.
\]

Expanding ab gives p. The cubic a has no root in F₂, hence is irreducible.
The quintic b has no root either. A reducible quintic with no linear factor
must have an irreducible quadratic factor: otherwise its irreducible factors
would each have degree at least three. The only monic irreducible quadratic
over F₂ is x²+x+1, and the remainder of b on division by it is x, not zero.
This proves irreducibility of b without a table of field elements.
The two factors are coprime; a useful explicit identity is

\[
b=(x^2+1)a+x^2.
\]

For completeness the CRT projectors can be written in the quotient as
e₃=x⁻²b and e₅=1+e₃. Their images are (1,0) and (0,1); these give
surjectivity onto the two factors. A polynomial vanishing in both is divisible
by ab, giving injectivity. In particular a pure-mode charge means exactly
c=e₃c≠0 or c=e₅c≠0.

Modulo a, x³=x²+1 and x⁶=x²+x, so y=x²+1=x³. Modulo b,

\[
x^6=x^2+x+1,\quad x^8=x^4+x^3+x^2,\quad
x^{13}=x^4+x^2+x+1,
\]
\[
x^{26}=x^8+x^4+x^2+1=x^3+1=y.
\]

These identities follow by multiplying x⁵=x⁴+x³+x²+1 and squaring.
Each field has respectively 8 or 32 elements by monic division. Multiplication
by any nonzero z permutes the nonzero elements; multiplying those elements
and cancelling their nonzero product gives z⁷=1 or z³¹=1. Since 7 and 31 are
prime, any nonzero element other than 1 has that exact order. The displayed
representatives of x and y are neither 0 nor 1 in their respective fields.
This proves every period assertion. ∎

## 2. Periodic geometry and a limitation of direct BCH reasoning

**PROPOSITION 2 (pending review/formalization).** For all integer i,j,

\[
\rho(x^iy^j)=(\alpha^{i+3j},\beta^{i+26j}).
\]

Consequently the lattice of translations preserving a monomial's full charge is

\[
\Lambda=\mathbf Z(16,-3)+\mathbf Z(3,13).
\]

*Proof.* Proposition 1 gives the formula, including negative exponents because
x,y are units. Its kernel is specified by i+3j=0 modulo 7 and i+26j=0
modulo 31. Both displayed vectors satisfy these congruences. Their determinant
is 217. The map from Z² to Z/7×Z/31 is onto already on (i,0), by the coprimality
of 7 and 31, so its kernel also has index 217. The inclusion of the displayed
lattice into that kernel is therefore equality. ∎

**FALSE: zero charge forces a charge polynomial to have many terms, or the
charge evaluation is injective on physical-square monomials.** The closed
counterexample is

\[
\rho(1+x^3y^{13})=0,
\qquad 3+3\cdot13=42=6\cdot7,
\qquad 3+26\cdot13=341=11\cdot31.
\]

Both monomials lie in [0,18]². Another identity is ρ(x¹⁶+y³)=0.
These counterexamples concern charge polynomials, not logical operators:
they do not assert that either polynomial is a cycle or a two-qubit logical.
They rule out a direct lower bound on support from vanishing in both fields
alone. Any BCH-style application must also use the physical syndrome equations.

## 3. Physical qubits are three-vertex syndrome hyperedges

Use the actual coordinates and syndrome from the explicit model:

\[
Q=[0,18]^2,\quad f=x+x^2+y^2,\quad
g=1+x^2y+x^2y^2,\quad \sigma(u,v)=gu+fv.
\]

For an X cycle, σ is supported only in the low rows {0,1} and high rows
{19,20}; its low part ℓ has charge c=ρ(ℓ). For a reflected Z cycle
M(u,v)=(J(v),J(u)), J(h)=x¹⁸y¹⁸h(x⁻¹,y⁻¹), the same assertions hold
with columns instead of rows. Reflection preserves physical weight. Charge
completeness in the input says that c=0 exactly for stabilizers in each sector.

Define vertices to be all syndrome positions in [0,20]². Each occupied physical
coordinate supplies one hyperedge, with these three vertices:

\[
A(i,j):\quad (i,j),(i+2,j+1),(i+2,j+2),
\]
\[
B(i,j):\quad (i+1,j),(i+2,j),(i,j+2).
\]

Each edge costs exactly one unit of physical weight. These are full syndrome
supports, including vertices outside Q: no boundary vertex is discarded.
Assign vertex (r,s) its label z(r,s)=ρ(xʳyˢ). Every label is nonzero in
both fields, and the three labels of each edge sum to zero, since ρ(f)=ρ(g)=0.

**PROPOSITION 3 (pending review/formalization; arbitrary-cut identity).**
Let R be any subset of the syndrome vertices containing every low-boundary
vertex and no high-boundary vertex. No regularity or straightness is required.
For every occupied edge e crossing R, define zₑ(R) to be the label of its
unique vertex on the side containing only one vertex of e. Then

\[
c=\sum_{e\text{ crossing }R}z_e(R).
\]

In particular a nonzero charge requires at least one occupied edge across
every such cut. A pure-mode charge requires at least two.

*Proof.* Sum the labels of σ's nonzero coefficients in R. Interior coefficients
vanish by the finite check equations, high-boundary coefficients are excluded,
and all low-boundary coefficients are included, so this sum is c. Alternatively,
sum the contribution of every occupied qubit. An edge entirely outside R
contributes zero; one entirely inside R contributes its three labels, also zero.
A crossing edge has one or two vertices in R. In the first case its contribution
is the single label. In the second, the two labels sum to the third label,
because all three sum to zero in characteristic two. This proves the identity.
Each zₑ(R) is nonzero in both fields. Thus zero crossing edges give c=0,
and exactly one crossing edge gives a charge nonzero in both factors. Neither
can give a nonzero pure-mode charge. ∎

This also gives a precise local matroid constraint: for a pure F₈ charge,
the crossing labels sum to zero in F₃₂ and to a nonzero value in F₈; exchange
the fields for a pure F₃₂ charge. If there are exactly two crossing edges,
their singleton labels must agree in the vanishing field and disagree in the
other. For vertices with displacement (Δi,Δj), this is exactly
Δi+26Δj=0 modulo 31 but Δi+3Δj≠0 modulo 7, or the reverse. These are
necessary conditions on actual occupied qubits, through the cut construction.

## 4. Two qubit-disjoint paths and a physical weight bound of 19

**PROPOSITION 4 (pending review/formalization).** Every cycle with nonzero
pure-mode charge has two hyperedge-disjoint paths from the low syndrome
boundary to the high syndrome boundary. Consequently its physical weight is
at least 19, for X cycles and for original Z cycles.

*Proof of the path statement.* Removing zero or one occupied hyperedge cannot
disconnect the boundaries. Otherwise take R to be all vertices reachable from
the entire low boundary after the removal. This R contains every low vertex,
no high vertex, and has at most one occupied hyperedge crossing it, contrary
to Proposition 3.

Here is the elementary network argument turning this into two paths. Replace
each hyperedge by an entrance and exit with a directed capacity-one arc between
them. Connect each incident vertex to the entrance and the exit to each incident
vertex with capacity-two arcs. Connect a source to all low vertices and all high
vertices to a sink with capacity-two arcs. Integral augmenting paths either
produce a flow of value two or terminate with a cut of capacity at most one.
For the latter assertion, take the vertices reachable in the residual network:
every outgoing arc is saturated, every incoming arc has zero flow, and summing
flow conservation gives cut capacity equal to the flow value. Such a cut can
cross only at most one capacity-one hyperedge arc; deleting that hyperedge
would disconnect the boundaries, already excluded. An integral flow of value
two, with cycles removed, supplies two paths sharing no hyperedge. Thus their
qubits are distinct, and their combined length is bounded by physical weight.

*First geometric bound.* Each hyperedge changes either coordinate by at most
two. A path from a row in {0,1} to a row in {19,20} must change its row
coordinate by at least 18, so it uses at least nine hyperedges. For reflected
Z, use the same argument on columns. Two disjoint paths give W≥18.

*Excluding equality for X.* Suppose W=18. Both paths must have exactly nine
edges, use all occupied qubits, start at syndrome row 1, end at row 19, and
increase row by exactly two on every edge. Therefore every occupied qubit has
physical row in {1,3,…,17}, with exactly two qubits in each such row.

Write the row polynomials as uᵢ(y),vᵢ(y). At each even tested syndrome row
2,4,…,18 the only possible contribution is vᵢ₋₁: the middle-row vertex
of B. A edges and the other two B vertices lie in odd rows. The syndrome
equations therefore force all vᵢ to vanish. There are exactly two A qubits
in every odd row. At the odd tested rows the remaining equations are

\[
u_i=(y+y^2)u_{i-2}\quad (i=3,5,\ldots,17).
\]

But three consecutive members of this recurrence cannot all have weight two.
Indeed, if h=yᵃ+yᵇ, a<b, then (y+y²)h has weight two only if b=a+1:
the sole possible collision among its four terms is a+2=b+1. In that case

\[
h=y^a(1+y),\quad (y+y^2)h=y^{a+1}(1+y^2),
\]
\[
(y+y^2)^2h=y^{a+2}(1+y+y^2+y^3),
\]

whose weight is four. Apply this to u₁,u₃,u₅ for a contradiction.
These are full polynomial identities; there is no truncation in the check
equations, whose tested column range is 0 through 20.

*Excluding equality for reflected Z.* Now W=18 forces every occupied qubit
to have physical column in {1,3,…,17}, exactly two per such column. The only
contribution to an even syndrome column is x²uⱼ₋₁, the middle-column term
of A. Its vanishing forces all A qubits to be absent. The B column polynomials
vⱼ(x) consequently satisfy

\[
(x+x^2)v_j=v_{j-2}\quad (j=3,5,\ldots,17).
\]

Apply the same weight-two polynomial argument in the reverse column direction
to v₁₇,v₁₅,v₁₃. Again equality is impossible. The tested row range is
0 through 20, so no polynomial terms are dropped. Thus W≥19 in both cases,
and undoing M proves the original Z assertion. ∎

## 5. A normalized recurrence and the six-singleton obstruction

The following normalization treats both sectors without assuming code symmetry.
For X use physical row polynomials Uᵢ=uᵢ(y), Vᵢ=vᵢ(y), set z=y and d=1.
For reflected Z, write its physical column polynomials as aⱼ(x),bⱼ(x), and
set Uᵢ=b₁₈₋ᵢ(x), Vᵢ=a₁₈₋ᵢ(x), z=x, d=x². Thus the second normalization
reverses the column axis and exchanges the two physical types. In either case,
the physical weight of slice i is wt(Uᵢ)+wt(Vᵢ), and the exact tested equations are

\[
Q_i+tU_{i-2}+V_{i-2}+dV_{i-1}=0\quad(2\le i\le18),
\qquad Q_i=U_i+z^2V_i,\quad t=z+z^2.                 \tag{N}
\]

For reflected Z this is the syndrome equation at original column 20−i,
namely a₂₀₋ᵢ+x²a₁₉₋ᵢ+x²a₁₈₋ᵢ+(x+x²)b₂₀₋ᵢ+b₁₈₋ᵢ=0.
All coefficients are retained, because the transverse tested range is 0…20.
The normalized syndrome axis is the original row for X and 20 minus the
original column for reflected Z. A U edge has one vertex at axis i and two
at i+2; a V edge has one vertex at each of i,i+1,i+2. This also checks the
normalization's physical geometry, not only its equations.

**PROPOSITION 6 (pending review/formalization).** No cycle has six consecutive
physical slices each of weight exactly one, in either normalized sector.
No hypothesis on any slice outside the six is needed.

*Proof.* On a singleton slice let εᵢ be 0 for U and 1 for V, and let mᵢ=zⁿⁱ
be its occupied monomial. Evaluating (N) at z=1 for the four internal equations
gives εᵢ₋₂+εᵢ₋₁=1, since Qᵢ(1)=1, t(1)=0 and d(1)=1.
Thus the first five types alternate. Starting at the first or second slice,
there is consequently a five-slice pattern U,V,U,V,C, where C is either type.
Renumber these five slices 0,…,4. Their last three equations give

\[
m_2+dm_1=tm_0,\qquad z^2m_3=m_1,\qquad Q_4+dm_3=tm_2.
\]

Here Q₄ is one monomial. In the first equation the two terms on the left
must be the two distinct terms of tm₀. Hence dm₁/m₂ is z or z⁻¹.
The last equation similarly gives dm₃/m₂ equal to z or z². The middle
equation then makes dm₁/m₂ equal to z³ or z⁴, a contradiction. These are
equalities of Laurent monomials in a polynomial domain, not field evaluations:
the exponents −1,1,3,4 cannot coincide. This argument works for both specified
values of d. ∎

## 6. Excluding physical weight 19 whenever two disjoint paths exist

**PROPOSITION 7 (pending review/formalization).** A cycle whose occupied
syndrome hypergraph has two hyperedge-disjoint low-to-high paths has weight
at least 20, in either sector. In particular every nonzero pure-mode logical
has weight at least 20.

*Proof.* Work in the normalized coordinates above. The proof of Proposition 4
already excludes weight below 19 using only the existence of the two paths;
it does not otherwise use the charge type. Suppose W=19. Each path has at
least nine edges. There are only two possibilities: two nine-edge paths and
one unused occupied edge, or paths of lengths nine and ten using all edges.

**Two nine-edge paths plus an extra edge.** Every nine-edge path starts at
syndrome axis 1, ends at 19, and takes nine +2 steps. Its qubits occupy exactly
the odd physical slices 1,3,…,17. Thus the two paths give weight two in each
of these nine slices, with one extra qubit elsewhere.

If the extra qubit is in an odd slice, all even slices are empty. The even
equations in (N) force every odd Vᵢ to be zero. At least one uninterrupted
block of three odd slices avoids the single heavier slice: removing one entry
from a nine-entry chain leaves a block of at least four. On that block all
Uᵢ have weight two and successive values multiply by t, contradicting the
sparse-product argument in Proposition 4.

If the extra qubit is in an even slice e, the even equations force all odd
Vᵢ to vanish except possibly at i=e−1,e+1. Remove those at most two adjacent
entries from the nine odd slices. The remaining at least seven entries form
at most two blocks, so one block has length at least four. Every slice in
that block contains two U qubits. Between its consecutive entries there is
no nonzero even slice, so (N) again gives Uᵢ=tUᵢ₋₂. Three entries contradict
the same sparse-product identity. Endpoints e=0,18 merely remove fewer entries.

**One nine-edge and one ten-edge path.** The nine-edge path again contributes
one qubit in each odd slice. Let δ₁,…,δ₁₀ be the signed axis increments of
the ten-edge path. Each is at most two, while their sum is between 18 and 20.
Therefore

\[
\sum_{j=1}^{10}(2-\delta_j)\le2.
\]

In particular there is no negative step. The possibilities are all +2 steps,
one +1 step, two +1 steps, or one zero step. This is a consequence of the
nonnegative integer deficit equation, not a support enumeration.

A +2 step uses a qubit whose physical slice is its starting syndrome coordinate.
A +1 step must use type V, and its physical slice is either its starting
coordinate or one less. A zero step must use type U at physical slice two
less than its syndrome coordinate: only U has two distinct vertices on one
axis level. A simple path cannot use a zero step from a vertex to itself.

We need two consequences of (N) for the +1 cases:

* An initial run of a maximal steps on odd slices, starting at syndrome 1,
  has a≤2. If a≥3, the first two doubled odd slices 1 and 3 have V₁=V₃=0,
  by the tested equations at even slices 2 and 4. There are no even occupied
  slices there; the first possible exceptional edge is at slice 2a or 2a+1.
  Thus U₁,U₃ have weight two and U₃=tU₁. Equation (N) at 5 then gives
  Q₅=t²U₁, of weight four, whereas slice 5 has only two qubits and wt(Q₅)≤2.
  This contradiction includes a=3, when V₅ need not vanish.
* A final run of c maximal steps on odd slices, ending at syndrome 19,
  has c≤2. If c≥3, let h be its first physical slice. All Vᵢ on later
  odd slices vanish by the even equations. There is no occupied even slice
  at h+1; the only possible occupied even slice at h−1 is the preceding
  +1 edge, of type V. Thus the even equation at h+1 gives
  dVₕ=Vₕ₋₁, so Vₕ is zero or a single monomial. The equation at h+2 is
  Uₕ₊₂=tUₕ+Vₕ. Evaluating at 1, its left side is zero because slice h+2
  contains two U qubits. Hence Vₕ(1)=0, forcing Vₕ=0. The first three
  slices of this final run now contain weight-two U polynomials in the
  recurrence Uᵢ=tUᵢ₋₂, again impossible.

Also, any run of b maximal steps on even slices has b≤3. The interval from
its first to last physical slice has 2b−1 consecutive singleton slices:
the ten-edge path fills the even slices and the nine-edge path the intervening
odd ones. The +1 edges lie outside this interval. If b≥4 it contains six
consecutive singletons, contrary to Proposition 6.

Now apply these bounds to each deficit possibility:

* With no deficit, the ten-edge path runs from 0 to 20 through all ten even
  physical slices. Together with the nine-edge path, all 19 slices are
  singletons, impossible by Proposition 6.
* With one +1 step, the ten-edge path runs from 0 to 19 or from 1 to 20.
  Its nine maximal steps split into one even run of length at most three
  and one initial or final odd run of length at most two. Their lengths
  cannot sum to nine.
* With two +1 steps, it runs from 1 to 19. Its eight maximal steps split
  into initial odd, middle even and final odd runs of lengths a,b,c.
  The proved bounds give a+b+c≤2+3+2=7, contradicting a+b+c=8.
  Empty runs are allowed; consecutive +1 steps cause no exception to the
  first/final-run arguments above.
* With one zero step, it runs from 1 to 19. Its nine maximal steps fill
  the odd slices once each, and the zero-step U edge is in another odd
  slice. Together with the nine-edge path this has exactly the odd-slice
  weight pattern already excluded in the extra-edge case.

These exhaust the deficit equation. Consequently W=19 is impossible. All
arguments apply to the explicitly normalized reflected-Z recurrence, so the
conclusion transfers back by the physical coordinate permutations. ∎

## 7. Mixed-charge bottlenecks occupy one small lattice coset

**PROPOSITION 8 (pending review/formalization).** For a fixed nonzero charge c,
the singleton vertices of every one-crossing boundary-separating cut lie in
one coset of Λ. Such a coset contains at most four vertices of [0,20]².
For straight syndrome cuts there are at most eight one-crossing cuts in the
X sector, and at most eleven in the reflected-Z sector. Consequently every
nontrivial X cycle has W≥14 and every nontrivial Z cycle has W≥13.

*Proof.* Proposition 3 says that a one-crossing cut has c equal to its
singleton vertex label. Proposition 2 then puts any two such vertices in
the same Λ coset. This uses the actual occupied crossing qubit.

Fix any coset point and write differences as (r,s)=(16n+3m,−3n+13m).
The inverse expressions are

\[
n=(13r-3s)/217,\qquad m=(3r+16s)/217.
\]

For any two board points, |r|,|s|≤20, whence |n|≤320/217<2 and
|m|≤380/217<2. Thus the n coordinates of all coset points take at most
two consecutive integer values, and so do the m coordinates. There are
at most four points, lying among the corners of a single lattice cell.

For a straight cut at normalized syndrome axis k, 2≤k≤19, crossing qubits
are exactly the occupied physical slices k−2 and k−1. A U singleton label
has axis k−2 or k−1; a V singleton label has axis k−1 or k. Thus a fixed
singleton vertex of axis r can serve only cuts k in {r,r+1,r+2}.

For X, the four possible cell-corner row coordinates, in increasing order,
are r₀,r₀+3,r₀+16,r₀+19. Three corners have extreme-row separation at
least 16. Their three disjoint length-three cut windows cannot all fit in
{2,…,19}, so three points serve at most eight cuts. Two points serve at
most six. If four corners are on the board, r₀ is 0 or 1. The extreme
windows together meet {2,…,19} in only two positions; the middle windows
serve at most six more. This also gives at most eight.

For reflected Z in normalized axis 20−column, the four corner coordinates
instead have the pattern r₀,r₀+3,r₀+13,r₀+16. Their four length-three
windows are disjoint, and their extreme positions differ by 18. All twelve
positions cannot fit in the eighteen-cut interval, whose endpoints differ
by 17. At most eleven survive. Three or fewer vertices serve at most nine.

Let N₁ be the number of singleton straight cuts and wᵢ the physical slice
weights. Nonzero charge forbids a zero-crossing cut. Hence

\[
2W-w_0-w_{18}=\sum_{k=2}^{19}(w_{k-2}+w_{k-1})\ge36-N_1.
\]

The proved lattice bounds N₁≤8 or N₁≤11 yield W≥14 or W≥13, respectively.
The different sector bounds reflect the different orientations of Λ; no
rotational symmetry is assumed. Pure charges already obey the stronger
bound in Proposition 7. ∎

## 8. What bridge displacement costs in physical qubits

**PROPOSITION 9 (pending review/formalization).** A one-crossing cut's singleton
vertex belongs to every simple low-to-high hyperedge path. For X, let distinct
singleton vertices of straight cuts, in increasing row order, be
(r₁,s₁),…,(rₕ,sₕ). Every such path has at least

\[
\left\lceil\frac{\max(r_1-1,0)}2\right\rceil
+\sum_{j=1}^{h-1}\left\lceil
  \frac{\max(r_{j+1}-r_j,|s_{j+1}-s_j|)}2\right\rceil
+\left\lceil\frac{\max(19-r_h,0)}2\right\rceil             \tag{P}
\]

qubits. In particular a pair displaced by (3,13) forces a path of length
at least 15; a pair displaced by (13,−16) forces length at least 11.
The total physical weight is at least these path lengths.

*Proof.* Any boundary path must cross the cut through its unique crossing
edge. On the side containing only one vertex of that edge, the path must
use that vertex. A simple path uses the edge only once. For nested straight
cuts, their unique crossings are therefore encountered in cut order.
Distinct same-coset board vertices have row separation at least three:
their difference has lattice coordinates n,m in {−1,0,1}, and 16n+3m
has absolute value at least three unless n=m=0. Their allowed cut windows
are consequently disjoint and have the same order as their rows.

Each path segment between mandatory vertices costs at least half their
maximum coordinate separation, rounded up, because a hyperedge changes
either coordinate by at most two. The first and last segments have the
indicated minimum row distances to the boundaries. These segments partition
the path's edges, proving (P). For a (3,13) displacement the middle segment
costs seven edges, and the outer segments together cost at least eight:
for interior endpoints their row distances sum to 15, and a vertex in the
outermost row can only increase that minimum. Thus the total is at least 15.
For (13,−16), the middle segment costs eight and the outside distances
sum to at least five, requiring three more edges. ∎

This retains transverse displacement: replacing each middle cost by only
half its row displacement would lose the transverse detour cost.
The analogous formula holds in normalized Z coordinates using the transformed
coset and its two coordinate displacements.

**PROPOSITION 10 (pending review/formalization; bridge reduction).** Any
nontrivial cycle of weight at most 19 must have an occupied hyperedge whose
removal disconnects the two syndrome boundaries. Its charge must be mixed,
and the singleton labels of all such separating cuts satisfy Proposition 8.

*Proof.* If removing any single occupied hyperedge leaves a boundary path,
the integral network argument in Proposition 4 gives two edge-disjoint paths.
Proposition 7 then forces weight at least 20. Otherwise take the reachable
set after deleting a separating edge; Proposition 3 applies to its unique
crossing edge and makes its charge nonzero in both factors. ∎

The continuation resolves the set-endpoint decomposition step. It still does
not double the fixed-vertex costs in (P): the endpoints in each region are
attachment sets, and shifts between those sets and singleton labels must be
charged to the appropriate side of each bridge.

## 9. Consecutive bridges and the entire middle network

Use the incidence graph of the occupied syndrome hypergraph: syndrome vertices
are one node class, and each occupied qubit is a degree-three node joined to
its three syndrome vertices. Wire all low-boundary vertices to one source S
and all high-boundary vertices to one sink T, by auxiliary links of zero
physical cost. A *bridge* here means an occupied qubit node whose deletion
disconnects S from T. It need not be an ordinary graph-edge bridge.
Only qubit nodes are counted in physical weight or deleted in separators.

Restrict to the connected component containing S and T. Nonzero charge ensures
this component exists. All boundary vertices belong to it by the wiring;
other occupied components can only add physical weight.

**PROPOSITION 11 (pending review/formalization; set-endpoint bridge lemma).**
All bridges have one consistent S-to-T order. Let e,f be consecutive in that
order. Deleting both leaves an S-side component L, a T-side component R,
and a middle network M which is the union of either one or two components.
Every middle component touches both e and f. Set

\[
A=V(e)\cap M,\qquad B=V(f)\cap M.
\]

Both sets have size one or two. If A and B are disjoint, M contains two
qubit-disjoint A-to-B paths. If they overlap, their minimum path cost is zero
and no positive distance estimate is claimed. Every nonbridge qubit counted
in M is disjoint from the qubits in L and R and from e,f themselves.

*Proof: a bridge has no third component.* Delete a bridge e. If a resulting
component C contains neither S nor T, it contains no boundary vertex. The
sum of syndrome coefficients times their charge labels over C is therefore
zero. Every occupied edge other than e contributes either all three labels
or none; these contributions vanish. Since the original component was
connected, C meets at least one vertex of e, and it cannot meet all three.
Its contribution is thus a sum of one or two labels of e, equal to a single
nonzero monomial label. This contradicts zero. Consequently deleting e leaves
exactly two components, Lₑ containing S and Hₑ containing T. Its three
vertices split as one plus two between them. Write vₑ for the singleton
vertex of that split. The charge identity on Lₑ gives ρ(vₑ)=c.

*Proof: order and components.* Every simple S-to-T path uses every bridge
exactly once. Choose one such path to order them. If e precedes f on it,
then f lies in Hₑ and e lies in L_f. Every other S-to-T path must first
cross e to reach f, so the order is independent of the path. Also Lₑ is
contained in L_f: its paths from S stay in Lₑ and cannot meet f in Hₑ.

After deleting e and f, L=Lₑ and R=H_f remain connected components. No
vertex of f is in L, since that would allow an S-to-f-to-T route avoiding e;
similarly no vertex of e is in R. Every other component must touch both e
and f. If it touched only e, restoring f would leave a third, boundary-free
component after deleting e, which was just ruled out; the argument for only
f is identical. Each middle component consumes at least one vertex of each
bridge. Each bridge also has at least one vertex on its outside side, so
there are at most two middle components and 1≤|A|,|B|≤2.

*Proof: no outside bypass, and Menger.* Any simple S-to-T path uses e and f
once in that order. The part between them lies entirely in M, connecting A
to B: entering L or R would require another passage through e or f, since
these are distinct components after both deletions. Thus if an occupied
middle qubit g separated all of A from all of B in the union M, deleting g
would destroy every S-to-T path. It would be a bridge strictly between e and
f, contrary to consecutiveness. There is an A-to-B path to begin with, from
the chosen global path. When A∩B is empty, the same integral capacity-one
qubit network used in Proposition 4 therefore gives two qubit-disjoint paths
from the entire set A to the entire set B. Their endpoints need not agree.
This proves the assertion and excludes an outside alternative explicitly. ∎

It is essential to use the union M. If it has two components, removing an
edge from one may cut that component's attachment pair while the other
component still connects e to f. The preceding proof does not assert that
each separate component is two-edge-connected.

## 10. Complementary endpoint shifts give a weight-20 bridge bound

For this section use X coordinates, let vₑ=(r,s), v_f=(r′,s′), and define

\[
D=\max(|r'-r|,|s'-s|),\quad C=\lceil D/2\rceil,\quad
B_0=\left\lceil\frac{\max(r-1,0)}2\right\rceil
   +\left\lceil\frac{\max(19-r',0)}2\right\rceil.
\]

The same formulas apply in normalized Z coordinates. They use bridge order,
not a presumption that the singleton rows increase in that order.

**PROPOSITION 12 (pending review/formalization).** For consecutive bridges
whose singleton vertices are distinct, the physical weight satisfies

\[
W\ge B_0+2\lceil D/2\rceil-2.                         \tag{B}
\]

In particular, for X singleton displacement v_f−vₑ=(3,13), one has W≥20.

*Proof.* Distinct singleton vertices have equal full charge c, so their
displacement is a nonzero element of Λ. The inverse-lattice bounds in
Proposition 8 put its lattice coordinates n,m in {−1,0,1}. If n=0,
then |Δs|=13. If n≠0, then |Δr|=|16n+3m|≥13. Thus D≥13;
the attachment sets cannot intersect, because each lies within coordinate
distance two of its respective singleton vertex.

Let a count how many of vₑ,v_f lie on their *outside* sides, namely L for
e and R for f. Then 0≤a≤2. If a singleton is on the middle side, the
corresponding middle attachment set is exactly that singleton, while the
outside attachments are within two in each coordinate of it. If the singleton
is outside, the outside attachment is exact and only the middle endpoints
can shift by up to two. These alternatives are complementary.

Therefore any A-to-B middle path has length at least

\[
\left\lceil\frac{D-2a}{2}\right\rceil=C-a.
\]

Proposition 11 supplies two edge-disjoint such paths, costing at least
2(C−a). Choose also a path in L from the low boundary to a vertex of e,
and a path in R from a vertex of f to the high boundary. Relative to the
singleton-based estimate B₀, these outside paths lose at most one step
for each singleton on the middle side. Their combined cost is at least
B₀−(2−a). A negative lower estimate would still be valid, though it is
positive in the (3,13) application. These outside paths, the two middle
paths, and the two bridge qubits occupy disjoint regions. Consequently

\[
W\ge 2+[B_0-(2-a)]+2(C-a)=B_0+2C-a\ge B_0+2C-2.
\]

For displacement (3,13), C=7. The two distances inside B₀ sum before
rounding to at least 15/2, since
max(r−1,0)+max(16−r,0)≥15. Hence B₀≥8 and W≥8+14−2=20. ∎

This validates the proposed five-edges-per-middle-path count, with its necessary
bookkeeping correction: the outside estimate of eight is automatic when both
singletons are outside. If one or both are inside, that outside estimate can
drop, but each middle path becomes correspondingly longer. The combined bound
is 22−a≥20, so no orientation assumption or double-counting is needed.

**PROPOSITION 13 (pending review/formalization; parallel middle components).**
If the same (3,13) pair has two middle components, the stronger bound W≥24
holds, even when there are other bridges outside the pair.

*Proof.* Each middle component has exactly one attachment to e and one to f,
and both singleton vertices lie outside M. Call the attachments in one
component u,w. Summing the syndrome labels over that component leaves only
ρ(u)+ρ(w)=0, so w−u is in Λ. Its row displacement lies in [−1,7] and
column displacement in [9,17], because each endpoint is within two of its
bridge singleton. If w−u=(16n+3m,−3n+13m), then

\[
-64\le 13\Delta r-3\Delta s=217n\le64.
\]

Thus n=0, and the column interval forces m=1. The attachments are separated
by exactly (3,13), requiring at least seven edges in each component's path.
The components are disjoint, their paths cost at least fourteen altogether,
the outside paths cost at least eight, and e,f cost two. Hence W≥24. ∎

## 11. An additive bound for the complete bridge decomposition

**PROPOSITION 14 (pending review/formalization).** List all bridges in their
S-to-T order as e₁,…,eₘ, with m≥1. Deleting them partitions the relevant
nonbridge network into layers: a low-boundary layer, a high-boundary layer,
and for each consecutive pair a middle layer containing all its parallel
components. Let δⱼ be the minimum number of occupied nonbridge qubits in
a path across layer j between its entire attachment sets, for 0≤j≤m.
The outside layers use the respective full boundary as one attachment set.
Set δⱼ=0 if the attachment sets meet. Then

\[
W\ge m+2\sum_{j=0}^m\delta_j.                       \tag{S}
\]

There are at most eight bridge qubits. If the cycle has exactly one bridge,
then W≥17. If it has exactly two bridges with distinct singleton vertices,
then, with B₀,C from Proposition 12,

\[
W\ge 2B_0+2C-2.                                    \tag{T}
\]

In particular exactly two X bridges with displacement (3,13) force W≥28;
with displacement (13,−16) they force W≥20.

*Proof of the partition and (S).* An S-to-T path meets every bridge once in
the fixed order. A component left after all bridge deletions cannot touch
nonconsecutive bridges: traversing that component would bypass an intermediate
bridge. Likewise a component touching S can attach only to e₁, and one
touching T only to eₘ. A component with no terminal and only one adjacent
bridge would survive as a forbidden boundary-free component on deleting that
one bridge. Thus the remaining components have precisely the asserted layer
structure. There is a path across each layer, obtained from a global path.

If a nonbridge qubit separated that layer's full attachment sets, every
global path would use it, making it an additional bridge. Thus when δⱼ>0
the capacity argument gives two disjoint paths in the layer, each of length
at least δⱼ. When δⱼ=0 its contribution to (S) is zero. All layers have
disjoint qubit sets; adding their bounds and counting each deleted bridge
once gives (S). Auxiliary source/sink wiring costs no qubits.

*Proof of the bridge count.* Every bridge singleton has label c, so there
are at most four distinct singleton vertices on the board. Every global
simple path must visit each such vertex. At a fixed visited vertex it can
use at most two incident bridge qubits, one entering and one leaving. Hence
there are at most two bridges with any one singleton vertex and m≤8. If
two bridges have the same singleton, they are consecutive in the bridge
order, since their occurrences on a simple path are adjacent at that vertex.
This count uses physical incidences, not merely the number of charge values.

*Proof for one bridge.* Choose attachment vertices at rows p on its low side
and q on its high side attaining the minimum outside path lengths. Since
they belong to the same hyperedge, q−p≤2. The outside path lengths obey

\[
2(\delta_0+\delta_1)\ge
\max(p-1,0)+\max(19-q,0)\ge18-(q-p)\ge16.
\]

Thus δ₀+δ₁≥8 and (S) gives W≥1+16=17.

*Proof for two bridges.* Use the complementary shifts in Proposition 12.
The sum of the two outside layer distances is at least B₀−(2−a), and
the middle layer distance is at least C−a. Thus the sum of all three
distances is at least B₀+C−2, independently of the orientation a.
Substitution into (S) gives (T). For (3,13), B₀≥8 and C=7, giving 28.
For (13,−16), B₀≥3 and C=8, giving 20. ∎

**CONJECTURE / remaining gap.** These set-endpoint inequalities do not yet
exclude every mixed-charge cycle of weight below 20. A single bridge, repeated
singleton vertices, and other lattice displacements can leave insufficient
geometric cost. Local recurrence or defect arguments are still needed in
those configurations. The gap is now in strengthening the layer costs, not
in establishing the layer partition or the set-endpoint two-path property.

## 12. One bridge: equality at 17 and the first bounded-defect case

**PROPOSITION 15 (pending review/formalization).** A nontrivial cycle with
exactly one bridge has physical weight at least 18, in either sector.

*Path extraction, including zero outside distances.* Let e be its bridge,
and L,H the components after deleting e. The low attachment set is V(e)∩L
and the high attachment set V(e)∩H. There is no further bridge in either
outside layer. Thus if its boundary and attachment sets are disjoint, that
layer has two qubit-disjoint boundary-to-attachment paths, by Proposition 14.
If those sets intersect, choose the same zero-edge path at an intersection
vertex twice instead. This uses no occupied qubit and creates no overlap in
the qubit count. Such a choice is available even if the layer contains other
occupied qubits.

Pair the two low paths with the two high paths arbitrarily, joining each
pair by one traversal of e between its attachment vertices. The components
L,H are disjoint, so each joined path is a simple boundary path. The resulting
two paths P₁,P₂ share exactly the one qubit e and have no other shared qubit;
sharing other syndrome vertices causes no problem. If their lengths are n₁,n₂,
their union therefore has exactly n₁+n₂−1 occupied qubits. In particular,

\[
9\le n_1,\quad9\le n_2,\quad n_1+n_2-1\le W.       \tag{E}
\]

This construction uses the whole attachment sets and does not prescribe the
bridge's singleton vertex as the endpoint of both outside layers.

*Equality forces the physical slices.* Proposition 14 already gives W≥17.
If W=17, equation (E) forces n₁=n₂=9 and exhausts all occupied qubits.
Every nine-edge boundary path goes from syndrome axis 1 to 19 and every
step is +2: its displacement is at least 18 and each of its nine steps
is at most two. Thus it uses one qubit in each odd physical slice
1,3,…,17. Both paths use the bridge in the same odd slice b. Since e is
their only shared qubit, every odd slice has weight two except b, which has
weight one; all even slices are empty. This reasoning is valid in both
normalized sectors from (N).

The argument does not assume that the paths visit a third, unused vertex
of e. That vertex is retained in the full syndrome equations. Specifically,
the equations at even tested slices i=2,4,…,18 reduce to dVᵢ₋₁=0.
Since d is a nonzero monomial, all odd V polynomials vanish, including a
putative V-type bridge. Hence every occupied qubit is U-type, and the odd
equations reduce to

\[
U_{2j+1}=t^jU_1\quad(0\le j\le8),\qquad t=z+z^2.
\]

For j≥1 this polynomial evaluates to zero at z=1; a monomial evaluates to
one. Thus a singleton slice can only be slice 1. In that case U₁=zᵃ and

\[
U_3=z^{a+1}(1+z),\qquad
U_5=z^{a+2}(1+z^2),\qquad
U_7=z^{a+3}(1+z+z^2+z^3).
\]

Their weights are 2,2,4, contradicting the required weight two in slice 7.
This excludes W=17 and proves W≥18. ∎

**PROPOSITION 16 (pending review/formalization; weight-18 defect reduction).**
A weight-18 cycle with exactly one bridge cannot have two nine-edge boundary
paths sharing only that bridge. Consequently any weight-18 one-bridge cycle,
if it exists, has a nine-edge and a ten-edge boundary path sharing just the
bridge and together exhausting its physical support. The ten-edge path has
exactly two +1 steps and eight +2 steps; the bridge is one of its +2 steps.

*Proof.* Two such nine-edge paths contribute weight two in every odd physical
slice except the bridge slice b, which has weight one. Their union has 17
qubits, leaving exactly one extra qubit.

If that extra qubit is in an odd slice, all even slices are empty, so (N)
again forces V=0 and U₂ⱼ₊₁=tʲU₁. If the extra qubit lies in slice b, every
odd slice has weight two, contrary to the three-weight-two recurrence identity
in Proposition 4. Otherwise slice b is still a singleton. It cannot be
noninitial, by evaluation at 1. If b=1, the monomial seed forces weight four
in slice 7, which has weight at most three even if the extra qubit lies there.
This also gives a contradiction.

If the extra qubit lies in an even slice e, all odd slices still have weight
one or two, with precisely one singleton. The even equations in (N) force
Vᵢ=0 for every odd i except possibly e−1 and e+1. Remove those at most two
adjacent entries from the chain of nine odd slices. At least seven entries
remain, in at most two contiguous blocks. In each block the slices contain
only U qubits, and consecutive entries satisfy Uᵢ=tUᵢ₋₂; no nonzero even
slice lies between two entries of a block.

Such a block can have length at most two if its first polynomial has weight
two, by the sparse-product identity of Proposition 4. If it starts with a
monomial, it can have length at most three, by the displayed weights 1,2,2,4
in Proposition 15. A monomial cannot occur later in a block because t divides
every noninitial polynomial. Only one block can contain the sole singleton,
so the two blocks contain at most 3+2=5 entries altogether. This contradicts
the at least seven remaining entries. The endpoint choices e=0,18 remove
fewer entries and give the same contradiction.

Apply (E) to any weight-18 one-bridge cycle. Its extracted path lengths,
in increasing order, can only be 9,9 or 9,10. The first alternative was just
excluded. In the second their union has 18 qubits, exhausting the support.

*Continuation: restrictions on the ten-edge path.* Its total forward deficit
is at most two. Hence its steps are all +2, or all +2 apart from one +1,
two +1 steps, or one zero step. If all steps are +2, the ten-edge path uses
only even physical slices and cannot share a qubit with the nine-edge path,
which uses only odd slices. This is impossible.

If there is a zero step, every occupied physical slice is odd. The two paths'
maximal steps give two qubits in each odd slice, except for the possible
subtraction of their shared bridge; the zero step adds one odd-slice U qubit
unless that is itself the shared bridge. Thus the weights are either all two,
or one singleton, one weight-three slice, and seven weight-two slices. These
are exactly the odd-only patterns excluded above by the full recurrence.
This argument uses only slice counts; removing a zero step is not asserted
to leave a valid path.

For the +1 possibilities, any maximal-step even run of length b has b≤3:
the interval from its first to last even slice contains 2b−1 consecutive
singleton slices. The shared bridge cannot be in this interval, since it
belongs to the odd-slice nine-edge path and the ten-edge path uses only its
even slices there. The +1 edges lie outside the interval. Proposition 6
therefore applies without a missing-qubit exception.

The initial and final maximal-step odd runs have weight two per slice,
except possibly for the one bridge singleton. The following weaker terminal
bounds, accounting for that singleton, suffice to exclude one +1 step:

* An initial odd run has length at most three. If its length were at least
  four, no even slice up to 6 would be occupied, so V₁=V₃=V₅=0. Its first
  three U polynomials and the fourth Q polynomial satisfy
  U₃=tU₁, U₅=t²U₁, Q₇=t³U₁. All have weight at most two. If U₁ is
  a monomial, Q₇ has weight four. If U₁ has weight two, U₃ cannot be a
  monomial; making it weight two forces U₅ to have weight four by the
  sparse-product identity. Both alternatives are impossible.
* A final odd run has length at most four. Let h be its first slice. All
  later V polynomials vanish by the even equations. At h−1 the only possible
  occupied even slice is the preceding +1 edge, of type V, so the equation
  at h+1 gives dVₕ=Vₕ₋₁. Thus Vₕ is zero or a monomial. If Vₕ=0, the
  whole run obeys the U-only recurrence, which has at most three successive
  nonzero polynomials of weight at most two. If Vₕ is a monomial, the
  equation Uₕ₊₂=tUₕ+Vₕ evaluated at 1 forces slice h+2 to be the sole
  singleton. Subsequent weights are 2,2,4, so the fifth slice cannot belong
  to the run. This proves the bound four.

With one +1 step, the nine remaining maximal steps split into one even run
of length at most three and one terminal odd run of length at most four.
They cannot have total length nine. Therefore exactly two +1 steps remain,
and the ten-edge path goes from syndrome 1 to 19.

If the shared bridge were one of these +1 steps, all maximal odd slices
would still have weight two. The initial/final bounds of two from Proposition
7 apply to those runs without alteration: their internal equations are
unaffected by a missing qubit at a transition slice. The even run has length
at most three. Their eight maximal steps would then number at most 2+3+2=7,
a contradiction. Hence the shared bridge is a +2 step in an odd run. ∎

For clarity, if a,b,c are the remaining initial-odd, middle-even and final-odd
run lengths, then a+b+c=8 and b≤3. If the bridge is in the initial run,
then a≤3,c≤2; if it is in the final run, then a≤2,c≤4. These are necessary
conditions, not assertions that such slice patterns lift to physical cycles.
The shared singleton prevents directly reusing Proposition 7's final contradiction.

For W=19, equation (E) reduces the extracted path lengths, in increasing
order, to 9,9 with two unused qubits; 9,10 with one unused qubit; or 9,11
and 10,10 with none. These are direct integer consequences of (E), not a
support search. No exclusion of these one-bridge weight-19 cases is claimed.

**PROPOSITION 17 (pending review/formalization; minimum logical supports).**
Every minimum-weight nontrivial sector cycle has no nonempty proper cycle
subset of its physical support. Thus it is a support circuit of the binary
cycle space. Its occupied syndrome hypergraph is connected even before the
boundary vertices are wired together.

*Proof.* Let w be such a minimum logical and let z be a nonzero cycle with
support strictly contained in supp(w). If z is nontrivial, it is a lighter
logical, a contradiction. If z is a stabilizer, then w+z is still nontrivial
and, since the coefficients are binary and supp(z)⊂supp(w), has weight
wt(w)−wt(z)<wt(w), again a contradiction. This uses only that stabilizers
form a subspace of the cycle space. For the connectedness assertion, each
occupied hypergraph component separately satisfies every tested syndrome
equation: all occupied edges incident to any tested vertex belong to the
same component. Two occupied components would therefore provide a forbidden
proper cycle subset. ∎

This minimal-support reduction is available for a later lower-bound proof,
but Propositions 15–16 do not require it: their exclusions apply to every
one-bridge cycle with the stated weight or path configuration.

The weight-18 reduction is completed by Proposition 22 below. Weight 19 remains
open; minimum-support connectedness alone is not an exclusion of that case.

## 13. Below weight 20: at most two bridge centers

Call a bridge's singleton vertex its *center*, retaining its actual syndrome
coordinates. Multiple bridge qubits can have the same center; their charge
labels are equal regardless of whether their centers coincide. This section
uses A=(3,13), B=(16,−3) for lattice vectors, not physical qubit types.

**PROPOSITION 18 (pending review/formalization; X center reduction).** Every
nontrivial X cycle with W<20 has one or two distinct bridge centers, in strictly
increasing row order along the bridge sequence. It has at most four bridges.
If there are two centers, their displacement is one of

\[
B=(16,-3),\qquad B-A=(13,-16),\qquad A+B=(19,10).
\]

*Proof: a bridge exists and centers cannot descend.* Proposition 10 supplies
at least one bridge. All its centers have the same full charge. Proposition
14 shows that repeated occurrences of a center form a consecutive block of
at most two bridges. Between successive distinct-center blocks, the last
bridge of the first block and the first bridge of the second are consecutive.
Thus the bound (B) applies directly to each change of center.

For a displacement Δr<0, its singleton-based outside estimate satisfies

\[
B_0\ge\left\lceil\frac{18-\Delta r}{2}\right\rceil
 =\left\lceil\frac{18+|\Delta r|}{2}\right\rceil.
\]

The board's inverse-lattice bounds imply |Δr|≥3 and D≥13 for distinct
centers. Therefore B₀≥11, C=⌈D/2⌉≥7, and (B) gives

\[
W\ge11+2\cdot7-2=23,
\]

a contradiction. Distinct centers cannot have equal rows either: with lattice
coordinate differences n,m∈{−1,0,1}, the equation 16n+3m=0 implies n=m=0.
Consequently the distinct centers strictly increase in row along bridge order.

*Proof: one lattice cell contains all centers.* Choose any origin for the
common charge coset and write each center in lattice coordinates n,m, so its
physical displacement from that origin is nB+mA. For every pair of centers,
the coordinate differences satisfy

\[
|\Delta n|\le\frac{(13+3)20}{217}<2,\qquad
|\Delta m|\le\frac{(3+16)20}{217}<2.
\]

Hence all n values lie in two consecutive integers, as do all m values.
Taking their respective minima gives a point v₀ (not necessarily itself an
occupied center or even a board point) such that every center is among

\[
v_0,\quad v_0+A,\quad v_0+B,\quad v_0+A+B.
\]

Their row offsets are 0,3,16,19. Partition these four corners into the two
pairs {v₀,v₀+A} and {v₀+B,v₀+A+B}. Any three selected corners contain
both members of one pair. Those members are adjacent in the full row order,
and hence adjacent among the selected distinct centers. The corresponding
consecutive bridge blocks therefore have displacement A=(3,13), which forces
W≥20 by Proposition 12. This is impossible, so at most two centers occur.
At most two bridges per center then give at most four bridge qubits.

*Proof of the remaining displacements.* For two row-increasing centers write
their displacement as nB+mA with n,m∈{−1,0,1}. Positive row displacement
excludes n=−1. If n=0, positivity forces m=1, giving the already excluded
vector A. Thus n=1 and the three possible m values give B−A, B, B+A.
This is a lattice consequence, not an enumeration of physical supports. ∎

**PROPOSITION 19 (pending review/formalization; boundary multiplicity).**
A center on the low or high syndrome boundary belongs to at most one bridge.
A low-boundary center, if present, belongs to the first bridge; a high-boundary
center belongs to the last. This holds in either normalized sector, without
assuming W<20.

*Proof.* Every simple wired S-to-T path must visit a bridge's center. Suppose
that center v is on the low boundary. On such a path replace the entire prefix
through v by the auxiliary source link S–v. The suffix from v to T, preceded
by that link, is still a simple S-to-T path. Thus no bridge can have occurred
before v on the original path: the replacement would bypass it. At v a simple
path has only one outgoing edge, so at most one bridge can have v as its
singleton. That bridge is the first bridge. For a high-boundary center, retain
the prefix to v and use the auxiliary link v–T; the symmetric conclusion
follows. This reasoning concerns free boundary wiring and never adds a physical
qubit. ∎

**PROPOSITION 20 (pending review/formalization; residual X families).** Under
the assumptions of Proposition 18, the following are necessary restrictions:

* With one center there are one or two bridges; a boundary center permits
  only one. The one-bridge cases are further restricted by Propositions 15–16.
* With two centers displaced by A+B=(19,10), there are exactly two bridges.
  Their rows are (0,19) or (1,20).
* With two centers displaced by B=(16,−3), four bridges require center rows
  exactly (2,18). If either center is on a boundary, there are at most three.
* With two centers displaced by B−A=(13,−16), there must be at least three
  bridges. Four bridges require the lower center's row to lie in [2,5].

*Proof.* For displacement 19, the lower row is 0 or 1 and the upper row
is 19 or 20, so both centers are on their respective boundaries. Proposition
19 makes both multiplicities one. For displacement 16, four bridges mean
both centers have multiplicity two and therefore both are interior. If r
is the lower row, this requires r≥2 and r+16≤18, forcing r=2. These are
necessary conditions; no existence claim is being made.

For displacement 13, exactly two bridges would obey (T) with B₀≥3 and
C=8, giving W≥2·3+2·8−2=20. Thus the W<20 case has three or four
bridges. If there are four, both centers are interior and 2≤r≤18−13=5.
The one-center assertion follows directly from Propositions 14 and 19. ∎

These families specify actual bridge multiplicities and locations. They are
not a list of logical charges, nor a claim that every listed family occurs.
In particular, they replace the general eight-bridge bound by four for W<20
without a support search or the minimum-support circuit hypothesis.

## 14. The corresponding normalized-Z reduction

**PROPOSITION 21 (pending review/formalization).** A nontrivial Z cycle with
W<20 also has at most two distinct bridge centers and at most four bridges.
In normalized coordinates (r,s)=(20−original syndrome column, original row),
the two-center displacement, if present, must be

\[
(13,-3)\quad\text{or}\quad(16,13).
\]

Four bridges in the second family require normalized center rows (2,18);
four in the first require the lower normalized row to lie in [2,5].

*Proof.* Rotation/reflection of the lattice gives the cell generators
A_Z=(3,16) and B_Z=(13,−3): A_Z is the image of B, and B_Z is the
image of −A. Its row-ordered corners have offsets 0,3,13,16. The coordinate
transformation preserves the maximum coordinate distance, so distinct board
centers still have D≥13 and distinct normalized rows differ by at least three.
A decreasing transition therefore costs at least 23, by the same bound (B).

The pair-partition argument for three corners now forces an adjacent A_Z
displacement. Here B₀≥8 and C=8, so (B) gives W≥22. Thus at most two
centers remain. The positive-row candidate differences are A_Z, B_Z,
B_Z−A_Z and A_Z+B_Z. Besides A_Z, the difference B_Z−A_Z=(10,−19)
is excluded by B₀≥4, C=10, which gives W≥22. Only B_Z and A_Z+B_Z
remain. Boundary multiplicity, applied in the normalized coordinates, gives
the asserted restrictions for four bridges. ∎

**CONJECTURE / remaining structural gap.** The residual families in Propositions
20–21 might all require W≥20, but that is not proved here. Boundary multiplicity
and monotonic center order restrict the possible physical geometry; they do
not by themselves exclude the single-center cases or all the remaining
two-center attachment layers.

## 15. Completing the one-bridge weight-18 exclusion

**PROPOSITION 22 (pending review/formalization).** Every nontrivial cycle with
exactly one bridge has physical weight at least 19, in either sector.

*Proof.* Proposition 15 excludes weights at most 17. If W=18, Proposition 16
gives a nine-edge path and a ten-edge path, sharing exactly the bridge and
covering every occupied qubit. The ten-edge path has the form

\[
(+2)^a,\ +1,\ (+2)^b,\ +1,\ (+2)^c,
\qquad a+b+c=8,
\]

where its initial and final maximal runs use odd physical slices and its
middle run uses even slices. The bridge is a +2 step in an odd run.
Every +1 edge has type V. The previous bounds give b≤3; if the bridge is
initial then a≤3,c≤2, and if it is final then a≤2,c≤4. In particular
b≥2: otherwise the maximal allowed terminal runs cannot sum with b to eight.
Thus the two +1 edges are separated by at least two maximal steps. All
arguments below use the exact normalized recurrence (N), with d=1 or d=z².

**Bridge in the initial odd run.** The length bounds force a=3,b=3,c=2.
The initial odd physical slices are 1,3,5; the first +1 step goes from
syndrome row 7 to 8 and has physical slice 6 or 7. Slices 2 and 4 are empty,
so V₁=V₃=0. The equations at 3 and 5 give

\[
U_3=tU_1,\qquad Q_5=tU_3=t^2U_1.
\]

The bridge singleton cannot be at slice 3 or 5: U₃ and Q₅ evaluate to zero
at 1, whereas the Q polynomial of any singleton evaluates to one. Hence the
bridge is in slice 1 and U₁ is a monomial.

If the +1 edge is in slice 7, slice 6 is empty and its equation forces V₅=0.
The equation at 7 then gives Q₇=tU₅=t³U₁, of weight four. But slice 7
contains only the nine-edge-path qubit and this +1 qubit, so wt(Q₇)≤2.
This is impossible.

If the +1 edge is in slice 6, V₆ is a monomial and U₆=0. The even equation
at 6 gives dV₅=z²V₆, so V₅(1)=1. Slice 7 is now a singleton, because
the ten-edge path's next occupied slice is 8 and the second +1 step is farther
away. Evaluating its equation at 1 yields

\[
0=Q_7(1)+t(1)U_5(1)+V_5(1)+d(1)V_6(1)=1+0+1+1=1.
\]

This excludes the initial-bridge possibility.

**Bridge in the final odd run.** Now a≤2,b≤3 imply c≥3. Write
h=19−2c for the first physical slice of that final run. In fact c is 3 or 4,
so h is 13 or 11 and all the following equations are at tested slices.
The preceding +1 step goes from syndrome h−1 to h. Its V qubit is in
physical slice h−2 or h−1. Every later even slice is empty; the even
equations force Vᵢ=0 on odd slices i>h, and at h+1 give

\[
dV_h=V_{h-1}.                                      \tag{F1}
\]

If that +1 qubit is in the even slice h−1, Vₕ is a nonzero monomial.
The next odd equation is

\[
U_{h+2}=tU_h+V_h.                                  \tag{F2}
\]

Evaluation at 1 makes slice h+2 a singleton. It must therefore be the bridge
slice. Slice h has two qubits: write Uₕ=p and Vₕ=q, both monomials.
Because the right side of (F2) is a monomial, q cancels one of the two
terms of tp. Consequently

\[
q=z^\epsilon p,\qquad\epsilon\in\{1,2\}.
\]

Slice h−2 contains exactly the nine-edge-path qubit; the last maximal even
step is in h−3, and the other transition is separated from this one.
Evaluating equation (N) at h forces that singleton at h−2 to have type V.
Write Vₕ₋₂=m, a monomial. Combining (F1) with the full equation at h gives

\[
m=p+(z^2+d^2)q,
\qquad\frac mp=1+(z^2+d^2)z^\epsilon.               \tag{F3}
\]

For d=1 the right side is 1+zᵋ+zᵋ⁺²; for d=z² it is
1+zᵋ⁺²+zᵋ⁺⁴. In both cases the three exponents are distinct, since
ε is 1 or 2. Thus (F3) equates a Laurent monomial with a three-term
polynomial, which is impossible.

If the +1 qubit is instead in the odd slice h−2, then Vₕ₋₁=0 and (F1)
gives Vₕ=0. The entire final run is U-only and obeys Uᵢ=tUᵢ₋₂.
Since c≥3, its singleton must be the first entry: a noninitial singleton
is excluded by evaluation at 1, while three weight-two entries are excluded
by Proposition 4. Thus the bridge is the sole U qubit in physical slice h.

Let v be this bridge's unique syndrome vertex at row h. Both boundary paths
traverse the bridge by +2 steps and therefore enter it at v. The preceding
qubit on the nine-edge path is in physical slice h−2; the preceding qubit
on the ten-edge path is the +1 V qubit, also in slice h−2. They are distinct,
since the paths share only the bridge, and both are incident to v. These are
the only two qubits in slice h−2. Slice h−1 is empty and slice h contains
only the bridge. Since syndrome row h can receive contributions only from
physical slices h−2,h−1,h, precisely these three occupied qubits meet v.
The syndrome coefficient at this tested vertex is therefore 1+1+1=1,
contradicting the cycle equation. This counts actual incident qubits; it does
not assume a path covers every vertex of its hyperedges.

All final-bridge possibilities are now excluded as well. Hence W=18 cannot
occur. Both values of d were handled explicitly, proving the claim in both
normalized sectors and therefore in the original X and Z sectors. ∎

## 16. A further weight-19 restriction with two nine-edge paths

**PROPOSITION 23 (pending review/formalization).** Suppose a weight-19 cycle
has exactly one bridge and its extracted paths from (E) both have length nine.
Then its two occupied qubits outside those paths must lie in two distinct
even physical slices e<f with f−e≥4. In particular they cannot both be odd,
be of opposite slice parity, or occupy the same or consecutive even slices.

*Proof.* The path union has weight two in every odd slice except the bridge
slice, which is a singleton, and is empty in even slices. There are two extra
qubits.

If both extras are odd, all even slices stay empty. Thus V=0 and, writing
hⱼ=U₂ⱼ₊₁, one has hⱼ=tʲh₀ for 0≤j≤8. Every hⱼ is nonzero; for j≥1
its weight is a positive even integer. The total weight is 19, and h₀ has
weight at most four because at most two extra qubits were added to slice 1.
Hence wt(h₀) is 1 or 3.

If wt(h₀)=3, all eight later polynomials must have weight two. Then h₁ and
h₂=th₁ both have weight two, forcing h₁=zᵘ(1+z) by the sparse-product
identity. Cancelling t=z(1+z) from h₁=th₀ would make h₀ a monomial,
a contradiction. This cancellation can be taken in the Laurent polynomial
domain, so no exponent-range assumption is needed.

If wt(h₀)=1, exactly one later polynomial can have weight four and the others
must have weight two. But both h₃ and h₅ have weight four, by the identities

\[
t^3=z^3+z^4+z^5+z^6,
\qquad t^5=z^5+z^6+z^9+z^{10}.
\]

This also contradicts the weight budget.

If exactly one extra qubit is even, say at slice e, remove the odd entries
e−1,e+1 as in Proposition 16. At least seven entries remain in at most two
clean U-only recurrence blocks. Their slice weights are at most three, and
at most one entry is a singleton. A block starting with weight two has length
at most two; a block starting with a monomial has length at most three.
A block starting with weight three also has length at most two: its later
entries, if present, must have weight two, and two such consecutive entries
would force the first entry to be a monomial by the cancellation argument
above. Thus the two blocks together have at most five entries, a contradiction.

If both extras are in the same even slice, the same two deleted odd entries
leave at least seven entries in at most two blocks, now of weights one or two;
their total allowed length is again at most five. If the two extra slices
are distinct consecutive even slices e,e+2, the only possibly nonzero odd V
polynomials are at e−1,e+1,e+3. Removing those at most three consecutive
odd entries leaves at least six entries in at most two clean blocks, again
exceeding the allowed five. Endpoints only reduce the number removed.

These contradictions leave only distinct even slices separated by at least
four. This is a necessary geometric restriction, not an assertion that such
extras can complete a cycle. ∎

The one-bridge weight-19 cases still open are: two nine-edge paths with the
two separated-even extras just described; a nine/ten pair with one extra
qubit; and nine/eleven or ten/ten pairs covering the support. The general
multi-bridge residual families in Propositions 20–21 also remain open.
In particular, neither Proposition 22 nor 23 proves the full distance-20
lower bound or supplies a weight-20 logical construction.

## 17. Scope, gaps, and reproducibility

**PROPOSITION 5 (pending review/formalization; scope, updated).** In either sector,
the pure-mode weight-20 bound applies to 38 nonzero logical classes: 7 nonzero charges
of form (c₃,0) and 31 of form (0,c₅). There are 217 remaining nonzero classes
with both components nonzero. These counts follow from Proposition 1 and
charge completeness, not from enumeration of representatives. The bound holds
for every stabilizer translate because the charge is constant on a class.

**CONJECTURE (unproved here).** All nontrivial sector cycles have weight at
least 20. Proposition 7 resolves weight 19 in pure classes and, more generally,
every case admitting two disjoint boundary paths. Propositions 11–14 also
resolve certain mixed-charge bridge configurations. Proposition 22 completes
the one-bridge weight-18 exclusion, giving W≥19 for one bridge; Proposition 23
restricts one of its weight-19 configurations. Other mixed separating-qubit
configurations remain open. Propositions 18–21 reduce any
remaining W<20 configuration to at most two centers and four bridges, with the
stated sector-specific displacement restrictions. No weight-20 logical
construction is asserted here, so this note by itself establishes neither
the lower nor upper half of exact distance
20. The periodic two-term identities in Section 2 explain why plain field
evaluation without the physical hypergraph is insufficient.

The companion `charge_factors_check.py` persists the symbolic checks used in
this derivation. Run `python3 analytical/notes/charge_factors_check.py` with
Python 3.13. It checks polynomial multiplication and remainders, the mode
substitutions, periods, periodic identities, the two normalized syndrome kernels,
the lattice inverse matrix, and the sparse-product identity. These checks do not
constitute a machine verification of the hypergraph/path proof.
Its small power scan was used only to discover the exponent 26; the proof
above instead supplies closed identities for it. No machine-generated case
list, support enumeration, external field table, or script output is a premise
of any proof. No Lean sources or other analytical notes were changed.
