#set page(paper: "a4", margin: 18mm)
#set text(size: 10pt)
#set par(justify: false)
= A supplied weight-20 logical witness

*Upper-witness proposition (explicit rectangular model).* For the two check
matrices defined below, the displayed 23-qubit X vector and 20-qubit Z vector
are opposite-check cycles with binary pairing one. In particular, the Z vector
is a nontrivial logical of weight 20, and its pure-Z Pauli operator is a
nontrivial logical Pauli of weight 20. Thus the Z-sector and Pauli minimum
weights are at most 20. The X partner has weight 23. This proposition concerns
the explicitly defined model; applying it to the literal JSON requires the
separate ordered-input identification in INPUT.

This is a witness appendix, pending bounded Lean replay and three independent
reviews. It is not the final PROOF document. It supplies an upper bound of 20,
not an assertion that the distance equals 20. No search is used here.

The input is `qldpc-challenge/codes/722-8-20.json`, revision
`8c87413d16b78cdd934b7b7a8592cddc81ae6eed`. Its exact byte SHA-256 is
#linebreak()
#text(size: 8pt)[`4ab209d0c450dc7a96e6054ed29322808be87ee52eb3002c51ab4531dcc91b15`].
The separate INPUT appendix identifies its ordered matrices with the rectangle.
The supports here are the explicit pair recorded in `analytical/notes/geometry.md`.

= Model and check rows

All qubit labels start at zero. A(i,j) = 19i+j and B(i,j) = 361+19i+j,
where 0 ≤ i,j ≤ 18. The vector of a support has coefficient one at each
listed qubit and zero elsewhere. Work over the two-element field, so two
copies of any monomial cancel. Exponents in this appendix are ordinary
integers; there is no periodic wrap.

Let Q be the square of integer exponent pairs with 0 ≤ i,j ≤ 18. A physical
vector is a pair (u,v) of polynomials supported in Q, for species A and B.
Let P delete all terms outside Q in each component of a Laurent-polynomial
pair. Put f = x + x² + y² and g = 1 + x²y + x²y², and let bar replace
x and y by their inverses. Thus bar(f) = x⁻¹ + x⁻² + y⁻² and
bar(g) = 1 + x⁻²y⁻¹ + x⁻²y⁻². Define the binary check rows by

$ H_X[(a,b),:] = P(x^a y^b (f,g)), quad -2 <= a <= 18, quad 0 <= b <= 16; $
$ H_Z[(c,d),:] = P(x^c y^d (overline(g),overline(f))),
  quad 2 <= c <= 18, quad 0 <= d <= 20. $

These are actual integer anchor coordinates. They correspond to the input
indices (a+2,b) and (c−2,d), respectively. Both matrices have 357 rows and
722 columns. The dot product sums the products of corresponding A and B
coefficients over Q. No rank assertion is needed for this witness argument.

= Coefficients are check dot products

Write [i,j]h for the coefficient of x^i y^j in a Laurent polynomial h,
with coefficient zero at absent exponents. Multiplication is the finite
convolution [r,s](h u) = sum over (i,j) of ([r−i,s−j]h)([i,j]u).
Because u and v vanish outside Q, projecting a check row with P does not
change its dot product with (u,v). The Z row at (c,d) has A coefficient
[i−c,j−d]bar(g) = [c−i,d−j]g, and the analogous B coefficient uses f.
Consequently convolution gives

$ H_Z[(c,d),:] dot (u,v) = [c,d](g u + f v). $

For the X row at (a,b), the A coefficient is [i−a,j−b]f =
[a−i,b−j]bar(f), and the B coefficient similarly uses bar(g). Hence

$ H_X[(a,b),:] dot (u,v) = [a,b](overline(f) u + overline(g) v). $

These identities derive the full X syndrome g u + f v and full Z syndrome
bar(f) u + bar(g) v directly from the defined rows. Only coefficients at
retained check anchors are tested; the full polynomials may be nonzero outside
those anchors. No matrix computation or Lean result is a premise of this derivation.

= Commutation and retention of every overlap

Before projection, the X row at (a,b) has every y exponent in [b,b+2],
which lies in [0,18]. Thus all its columns lie on the physical board even
when some x exponents do not. Before projection, the Z row at (c,d) has
every x exponent in [c−2,c], which lies in [0,18]. Thus all its rows lie
on the physical board even when some y exponents do not. Any common
monomial of these two rows, in either species, therefore has both coordinates
in [0,18]. Projection discards no term that contributes to their dot product.

For finite Laurent polynomials h and k, their full-plane coefficient dot
product is the constant coefficient of h bar(k): each constant term pairs
equal exponent coordinates. Apply this componentwise to the two unprojected
check rows. The result is the constant coefficient of

$ x^(a-c) y^(b-d) (f g + g f). $

Polynomial multiplication commutes, and the field has characteristic two,
so fg + gf = 0. The full-plane row dot product is zero; retention of every
overlap proves the same for the projected physical rows. Hence
$H_X H_Z^T = 0$, so the rows define a commuting CSS stabilizer model.

= The two supplied supports

X support (23 distinct qubits):

65, 103, 104, 105, 142, 162, 199, 219, 220, 332, 390, 407, 426, 504, 541, 560, 561, 579, 598, 617, 619, 636, 655.

Z support (20 distinct qubits):

46, 47, 61, 63, 65, 66, 80, 97, 131, 150, 167, 409, 424, 425, 446, 448, 456, 486, 487, 526.

= Complete multiplication and cancellation

Each pair (i,j) below denotes x^i y^j. Each input row contributes exactly
the three exponent pairs in its product column. Nothing is truncated before
multiplication. The cancellation tables list a multiset C: every listed
entry is removed twice. Consequently the full product multiset is exactly
R + C + C, where R is the stated residual multiset. These are fixed integer
identities that can be checked by sorting the product columns and tallying.

#pagebreak()
== X multiplication

#table(columns: (35pt, 75pt, 1fr), inset: 3pt,
  table.header([Qubit], [Input monomial], [Three product exponents]),
  [65], [A(3, 8)], [(3, 8), (5, 9), (5, 10)],
  [103], [A(5, 8)], [(5, 8), (7, 9), (7, 10)],
  [104], [A(5, 9)], [(5, 9), (7, 10), (7, 11)],
  [105], [A(5, 10)], [(5, 10), (7, 11), (7, 12)],
  [142], [A(7, 9)], [(7, 9), (9, 10), (9, 11)],
  [162], [A(8, 10)], [(8, 10), (10, 11), (10, 12)],
  [199], [A(10, 9)], [(10, 9), (12, 10), (12, 11)],
  [219], [A(11, 10)], [(11, 10), (13, 11), (13, 12)],
  [220], [A(11, 11)], [(11, 11), (13, 12), (13, 13)],
  [332], [A(17, 9)], [(17, 9), (19, 10), (19, 11)],
  [390], [B(1, 10)], [(2, 10), (3, 10), (1, 12)],
  [407], [B(2, 8)], [(3, 8), (4, 8), (2, 10)],
  [426], [B(3, 8)], [(4, 8), (5, 8), (3, 10)],
  [504], [B(7, 10)], [(8, 10), (9, 10), (7, 12)],
  [541], [B(9, 9)], [(10, 9), (11, 9), (9, 11)],
  [560], [B(10, 9)], [(11, 9), (12, 9), (10, 11)],
  [561], [B(10, 10)], [(11, 10), (12, 10), (10, 12)],
  [579], [B(11, 9)], [(12, 9), (13, 9), (11, 11)],
  [598], [B(12, 9)], [(13, 9), (14, 9), (12, 11)],
  [617], [B(13, 9)], [(14, 9), (15, 9), (13, 11)],
  [619], [B(13, 11)], [(14, 11), (15, 11), (13, 13)],
  [636], [B(14, 9)], [(15, 9), (16, 9), (14, 11)],
  [655], [B(15, 9)], [(16, 9), (17, 9), (15, 11)],
)

Cancellation multiset C (each entry cancels twice):

(2, 10), (3, 8), (3, 10), (4, 8), (5, 8), (5, 9), (5, 10), (7, 9), (7, 10), (7, 11), (7, 12), (8, 10), (9, 10), (9, 11), (10, 9), (10, 11), (10, 12), (11, 9), (11, 10), (11, 11), (12, 9), (12, 10), (12, 11), (13, 9), (13, 11), (13, 12), (13, 13), (14, 9), (14, 11), (15, 9), (15, 11), (16, 9), (17, 9).

Residual multiset R: (1, 12), (19, 10), (19, 11).

#pagebreak()
== Z multiplication

#table(columns: (35pt, 75pt, 1fr), inset: 3pt,
  table.header([Qubit], [Input monomial], [Three product exponents]),
  [46], [A(2, 8)], [(1, 8), (0, 8), (2, 6)],
  [47], [A(2, 9)], [(1, 9), (0, 9), (2, 7)],
  [61], [A(3, 4)], [(2, 4), (1, 4), (3, 2)],
  [63], [A(3, 6)], [(2, 6), (1, 6), (3, 4)],
  [65], [A(3, 8)], [(2, 8), (1, 8), (3, 6)],
  [66], [A(3, 9)], [(2, 9), (1, 9), (3, 7)],
  [80], [A(4, 4)], [(3, 4), (2, 4), (4, 2)],
  [97], [A(5, 2)], [(4, 2), (3, 2), (5, 0)],
  [131], [A(6, 17)], [(5, 17), (4, 17), (6, 15)],
  [150], [A(7, 17)], [(6, 17), (5, 17), (7, 15)],
  [167], [A(8, 15)], [(7, 15), (6, 15), (8, 13)],
  [409], [B(2, 10)], [(2, 10), (0, 9), (0, 8)],
  [424], [B(3, 6)], [(3, 6), (1, 5), (1, 4)],
  [425], [B(3, 7)], [(3, 7), (1, 6), (1, 5)],
  [446], [B(4, 9)], [(4, 9), (2, 8), (2, 7)],
  [448], [B(4, 11)], [(4, 11), (2, 10), (2, 9)],
  [456], [B(5, 0)], [(5, 0), (3, -1), (3, -2)],
  [486], [B(6, 11)], [(6, 11), (4, 10), (4, 9)],
  [487], [B(6, 12)], [(6, 12), (4, 11), (4, 10)],
  [526], [B(8, 13)], [(8, 13), (6, 12), (6, 11)],
)

Cancellation multiset C (each entry cancels twice):

(0, 8), (0, 9), (1, 4), (1, 5), (1, 6), (1, 8), (1, 9), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 2), (3, 4), (3, 6), (3, 7), (4, 2), (4, 9), (4, 10), (4, 11), (5, 0), (5, 17), (6, 11), (6, 12), (6, 15), (7, 15), (8, 13).

Residual multiset R: (3, -2), (3, -1), (4, 17), (6, 17).

= Cycle, nontriviality, and upper bound

The X residual is x y¹² + x¹⁹ y¹⁰ + x¹⁹ y¹¹. Its first coordinates,
1 and 19, are outside the retained Z-check range 2 through 18.
The Z residual is x³ y⁻² + x³ y⁻¹ + x⁴ y¹⁷ + x⁶ y¹⁷.
Its second coordinates, −2, −1, and 17, are outside the retained X-check
range 0 through 16. Both actual opposite-check syndromes therefore vanish.

The displayed supports intersect in exactly {65}, so their binary dot
product is one. Every Z stabilizer is a sum of Z-check rows and pairs to
zero with the X cycle. Thus the displayed Z vector cannot be a Z stabilizer.
The same argument with X and Z interchanged makes the X vector nontrivial.
Counting the distinct Z labels gives weight 20; the X partner has weight 23.

The pure-Z Pauli operator placing Z on the 20 listed qubits and identity
elsewhere commutes with every stabilizer and is nontrivial modulo stabilizers.
Its Pauli weight is exactly 20. Hence the Z-sector minimum and the minimum
nontrivial Pauli weight are at most 20. The X partner only supplies an
X-sector upper bound of 23. No lower bound of 20 follows from these witnesses.

= Separate application to the submitted input

The proposition above uses only the explicit model definition and the supplied
supports. The ordered row identities in INPUT identify the literal submitted
matrices with this model in the same physical numbering, so the same vectors,
pairing, and weights give its upper witness. This is a separate input transport
step, not an assumption in the model proof. The persistent check script verifies the
closed polynomial products, weights, intersection, and sparse check parities;
these calculations are separate from the Lean kernel proof. No errors,
logical classes, or alternative supports are enumerated.
