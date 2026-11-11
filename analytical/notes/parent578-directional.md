# The 578 parent: directional rectangles, boundary orientation, and charge algebra

## Status and grading

**Answer:** in the fixed A/B coordinates and with X and Z kept in their
specified roles, the proposed directional rectangle is **not** the parent,
even at row-space level. There are explicit separating rows. However, the
parent is exactly the **oppositely oriented** directional rectangle, including
an explicit ordering of all 560 check rows. Moreover, coordinate reversal
`q -> 577-q` together with exchange of X and Z takes the parent to the
proposed rectangle. Thus the directional structure survives, with a precise
orientation/duality correction.

Grading applies globally:

- **PROPOSITION — independent review and formalization pending:** every
  derived mathematical statement below, including identities and proofs.
  No new result is graded as a formal or independently reviewed result.
- **PROPOSITION:** raw hashes and direct comparisons of sparse row supports.
  These establish the interface to the input file; they are not numerical
  distance or rank certificates.
- **FALSE:** an explicitly rejected assertion, with a separating witness.
- **NAMED UNPROVED HYPOTHESIS / RESEARCH DIRECTION:** any proposed identification
  of bulk charges with finite-board logical classes or weight constraints.

Only this file is owned by this investigation. No Lean runs, distance searches,
global distance assertions, or edits to the earlier lifting note are involved.
All indices below are zero based. This is a new structural investigation,
independent of stabilizer-parity surjectivity arguments.

## 1. Literal input and the two directional models

**PROPOSITION.** The input is the sibling checkout's
`codes/578-18-20.json`, with raw SHA-256

```text
440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514
```

This is the parent identified in the existing
[removal record](../../data/removal566-evaluation/README.md).
Define physical unit vectors A(i,j) and B(i,j), for `0<=i,j<=16`, at indices
`17i+j` and `289+17i+j`. An A or B expression outside that board means zero.
All sums in the note are over F2. Set

```text
f = 1+y^3+x^2 y^2+x^3,
g = y+xy+x^2+x^3 y^3.
```

The clipped translate formulas are

```text
X(a,b) = A(a,b)+A(a,b+3)+A(a+2,b+2)+A(a+3,b)
         +B(a,b+1)+B(a+1,b+1)+B(a+2,b)+B(a+3,b+3),

Z(c,d) = A(c,d-1)+A(c-1,d-1)+A(c-2,d)+A(c-3,d-3)
         +B(c,d)+B(c,d-3)+B(c-2,d-2)+B(c-3,d).
```

The Z formula uses g and f with both displacement signs reversed; it does
not use independently shifted reflected polynomials.

| Construction | X anchors | Z anchors |
| --- | --- | --- |
| Proposed rectangle M | `-3<=a<=16, 0<=b<=13` | `3<=c<=16, 0<=d<=19` |
| Actual-parent rectangle N | `0<=a<=13, -3<=b<=16` | `0<=c<=19, 3<=d<=16` |

Both have 280 rows of each type and 196 fully supported bulk rows per type.
Those counts do not distinguish the two constructions. The rest of this
note does distinguish them by explicit row formulas, not by ranks.

## 2. Commutation and explicit row-space counterexamples

**PROPOSITION P1 (commutation of both rectangles; review/formalization pending).**
Both M and N are CSS constructions.

**Proof.** Before clipping, the pairing of X(a,b) and Z(c,d) is the coefficient
of `x^(c-a)y^(d-b)` in `fg+gf=0`: the A overlap counts f displacements plus g
displacements, and the B overlap counts them in the opposite order. In M,
every full X support already has y in [0,16], and every full Z support already
has x in [0,16]. Consequently every possible intersection is inside the board.
Clipping deletes no overlap and preserves the zero pairing. In N the roles
of the axes are reversed: full X supports have x in [0,16], full Z supports
have y in [0,16]. The same argument applies. This proves all pairwise
commutations, including the boundary rows.

**FALSE:** the parent's X and Z row spaces equal those of M in the stated
physical coordinates with the same sector labels.

**PROPOSITION P2 (separating witnesses; review/formalization pending).**
The following input rows prove failure on both sides:

| Literal parent row | Its support | Opposite check in M | Support in M | Intersection |
| --- | --- | --- | --- | --- |
| X row 200 | `{0,340}` | Z(3,0) | `{17,289,340}` | `{340}` |
| Z row 200 | `{2,289,292}` | X(-3,0) | `{0,292}` | `{292}` |

**Proof.** The literal supports in the first column were read from the hashed
input. The model supports follow immediately from the clipped formulas:
`Z(3,0)=A(1,0)+B(0,0)+B(3,0)` and
`X(-3,0)=A(0,0)+B(0,3)`. Both displayed pairings are one. By P1, every vector
in the X row space of M pairs to zero with Z(3,0), and every vector in its Z
row space pairs to zero with X(-3,0). Thus neither displayed parent row can
belong to the respective model row space. This refutes row-space equality
and therefore ordered-row equality without any rank computation.

**PROPOSITION, not needed for that proof:** direct comparison found exactly
196 literal row matches on each side, namely the bulk. A preliminary binary
elimination check found all 84 remaining parent rows on each side outside
the corresponding M span. The separating witnesses above replace reliance
on that numerical observation; no rank assertion is used as the proof.

## 3. The corrected rectangle matches every ordered parent row

**PROPOSITION P3 (ordered formulas; review/formalization pending).**
Let `H_X[j]`, `H_Z[j]` denote the literal parent rows. Their formulas are

```text
0<=j<196,  j=14t+u with 0<=t,u<14:
    H_X[j] = X(t,u),
    H_Z[j] = Z(3+t,3+u).

j=196+6t+s, 0<=t<14, 0<=s<6:
    H_X[j] = X(t, beta_s),    beta = (-1,14,-2,15,-3,16),
    H_Z[j] = Z(gamma_s,3+t),  gamma = (2,17,1,18,0,19).
```

**PROPOSITION interface.** Substitution into these formulas was compared
directly against every sparse row in the hashed JSON. All 280 rows on each
side agree exactly, including sorted support order. No basis changes,
builder invocation, corner completion, or rank comparison are needed.
The recognition statement depends on that finite read of the input bytes;
the formulas below supply complete symbolic witnesses for what was checked.
This is not represented as a Lean check of a JSON parser.

Here are the complete boundary templates. In the X table, `0<=a<=13`:

| b | A support | B support |
| --- | --- | --- |
| -1 | `(a,2),(a+2,1)` | `(a,0),(a+1,0),(a+3,2)` |
| 14 | `(a,14),(a+2,16),(a+3,14)` | `(a,15),(a+1,15),(a+2,14)` |
| -2 | `(a,1),(a+2,0)` | `(a+3,1)` |
| 15 | `(a,15),(a+3,15)` | `(a,16),(a+1,16),(a+2,15)` |
| -3 | `(a,0)` | `(a+3,0)` |
| 16 | `(a,16),(a+3,16)` | `(a+2,16)` |

In the Z table, `3<=d<=16`:

| c | A support | B support |
| --- | --- | --- |
| 2 | `(2,d-1),(1,d-1),(0,d)` | `(2,d),(2,d-3),(0,d-2)` |
| 17 | `(16,d-1),(15,d),(14,d-3)` | `(15,d-2),(14,d)` |
| 1 | `(1,d-1),(0,d-1)` | `(1,d),(1,d-3)` |
| 18 | `(16,d),(15,d-3)` | `(16,d-2),(15,d)` |
| 0 | `(0,d-1)` | `(0,d),(0,d-3)` |
| 19 | `(16,d-3)` | `(16,d)` |

**Proof of the row formulas and coverage.** In the X translate, x coordinates
are a,a+1,a+2,a+3 and all lie on the board. For each of the six listed b values,
discard exactly those terms whose y coordinate is outside [0,16]; this gives
the six X templates. In the Z translate, all y coordinates d,d-1,d-2,d-3 lie
on the board. Discarding the out-of-range x coordinates for the six c values
gives the Z table. No two retained terms within a species cancel, since their
coordinates are distinct. The bulk anchor formulas have no clipped terms.
The bulk and boundary anchor lists are disjoint and together exhaust the N
anchor rectangles. Combining these identities with the literal support
comparison establishes ordered equality, stronger than a row-space match.

For a quick independent spot check, X rows 196,198,200 are respectively
`X(0,-1)`, `X(0,-2)`, `X(0,-3)`. Z rows 196,198,200 are respectively
`Z(2,3)`, `Z(1,3)`, `Z(0,3)`. The counterexample rows in P2 are therefore
the simplest truncated edge rows of N, not unexplained extra generators.

## 4. Exact duality with the originally proposed orientation

**PROPOSITION P4 (reversal and sector exchange; review/formalization pending).**
Let pi be the physical permutation

```text
pi(A(i,j))=B(16-i,16-j),
pi(B(i,j))=A(16-i,16-j),    equivalently pi(q)=577-q.
```

Then, term by term including clipping,

```text
pi(X(a,b)) = Z(16-a,16-b),
pi(Z(c,d)) = X(16-c,16-d).
```

Thus pi takes the parent X rows to all Z rows of M and the parent Z rows to
all X rows of M, with explicit anchor bijections. It does not establish
same-sector row-space equality in the original coordinates, which P2 refutes.

**Proof.** Reflection changes every positive displacement into its negative,
and species exchange converts (f,g) to (g,f). The board is invariant under
reflection, so clipped terms correspond exactly. The parent X anchors map
to `3<=16-a<=16, 0<=16-b<=19`, precisely the M Z range. The parent Z anchors
map to `-3<=16-c<=16, 0<=16-d<=13`, precisely the M X range. These maps are
involutions, proving the bijections. This is a structural identification;
no numerical distance assertion is made.

## 5. The twelve removed qubits are consecutive boundary anchors

**PROPOSITION P5 (hole positions in the directional model;
review/formalization pending).** For `0<=i<6`, the removed source qubit pair is

```text
alpha_i=A(16,i),       physical index 272+i,
beta_i =B(16,i+3),     physical index 564+i.
```

The distinguished source X row is `H_X[182+i]=X(13,i)`, and the distinguished
source Z row is `H_Z[201+6i]=Z(19,i+3)=alpha_i+beta_i`.

**Proof.** Substitute into P3: `182=14*13` and
`201+6i=196+6i+5`, with gamma_5=19. The c=19 boundary template is exactly
the displayed pair. Expanding X(13,i) gives that pair plus the six terms

```text
A(13,i), A(13,i+3), A(15,i+2),
B(13,i+1), B(14,i+1), B(15,i).
```

All are retained. An A(16,i) entry can occur in an N X row only through its
`A(a+3,b)` term, since a<=13; that forces a=13,b=i. A B(16,i+3) entry can
occur only through `B(a+3,b+3)`, forcing the same anchor. Thus each pair is
touched by only this X row. Deleting these six X rows, the six indicated
pair Z rows, and the twelve coordinates is exactly the literal removal
operation recorded for 566. The six fans are consecutive translates along
one boundary, not six unrelated holes. This gives a structural starting
point for coupling them by strip recurrences.

## 6. An explicit eighteen-dimensional bulk charge algebra

This section concerns a polynomial quotient, not finite-board distance or a
claim that its elements already classify parent or target logical operators.

**PROPOSITION P6 (bulk quotient; review/formalization pending).** Put

```text
P(y)=y^18+y^15+y^13+y^8+y^7+y^6+y^2+1,
q(y)=y^17+y^15+y^12+y^9+y^7+y^3+y.
```

Then in F2[x,y],

```text
(f,g) = (P(y), x+q(y)).
```

Consequently `F2[x,y]/(f,g)` has basis `1,y,...,y^17` and dimension eighteen.
Both x and y are units in this quotient, so the Laurent quotient
`F2[x^±1,y^±1]/(f,g)` is the same eighteen-dimensional algebra.

**Proof by explicit identities.** The following formulas provide witnesses;
no numerical rank calculation is used. Write

```text
u=1+y^5, v=y, w=y+y^3+y^6,
h=u*x^2+v*x+w = g+y^3*f,
a=y^11+y^2+y,
b=y^7+y^5+y^4+y^2+1.
```

Direct multiplication gives

```text
a*x+b = u^2*f + (u*x+u*y^2+v)*h.                    (12)
```

To witness P in (f,g), use the following explicit Sylvester matrix M:

```text
M = [ 1  y^2  0    1+y^3  0      0     ]
    [ 0  1    y^2  0      1+y^3  0     ]
    [ 0  0    1    y^2    0      1+y^3 ]
    [ y^3 1   y    y      0      0     ]
    [ 0  y^3  1    y      y      0     ]
    [ 0  0    y^3  1      y      y     ].
```

Expanding the determinant in F2[y] gives det(M)=P. More explicitly, let
`V=(x^5,x^4,x^3,x^2,x,1)^T`. Then
`M V=(x^2 f,x f,f,x^2 g,x g,g)^T`. The last row of
`adj(M) M V=P V` expresses P as an explicit polynomial combination of f,g:
the coefficients are the indicated five-by-five minors. This is a witness
identity for ideal membership, not an inference from equality of roots.

For the remaining elimination, define

```text
d=y^17+y^11+y^10+y^7+y^6+y^5+1,
e=y^10+y^7+y^5+y^3+y+1,
t=y^6+y^4+y+1.
```

The univariate identities are

```text
d*a+e*P=1,      d*b+q=t*P.
```

Together with (12), they give the membership witness

```text
x+q = d*(a*x+b) + (e*x+t)*P in (f,g).
```

For the converse inclusion, write `E(S)=sum_{j in S} y^j`, and set

```text
S_F={33,31,30,29,28,25,20,19,18,13,12,10,7,6,5,2,0},
S_G={36,34,33,32,31,28,23,22,18,17,16,14,12,11,6,5,4,3,1}.
```

Direct univariate multiplication gives

```text
q^3+y^2*q^2+1+y^3 = P*E(S_F),
y^3*q^3+q^2+y*q+y = P*E(S_G).
```

Writing `L=x+q`, the full two-variable identities are therefore

```text
f = L*(x^2+x*q+q^2+y^2*L) + P*E(S_F),
g = L*(y^3*(x^2+x*q+q^2)+L+y) + P*E(S_G).
```

They prove `(f,g) subset (P,L)` and hence ideal equality. Elimination of x
identifies the quotient with F2[y]/P. Division by the monic polynomial P
gives unique remainders of degree below eighteen, proving the basis claim.

Since P has constant coefficient one, y is a unit. For x=q, an explicit
inverse is `r=y^16+y^15+y^10+y^7+y^4+y+1`: multiplication gives

```text
q*r+1 = P*E({15,14,13,11,10,9,7,5,4,1,0}).
```

Localizing at x and y thus changes nothing, proving the Laurent assertion.
All displayed polynomial identities were also checked by exact symbolic
arithmetic over F2; the identities themselves are the proposed proof.

The number eighteen here is an algebra dimension. Agreement with the parent's
encoded dimension does **not** supply the missing identification with physical
logical classes or a weight bound. Such a bridge needs the boundary conditions.

## 7. What the three-strip direction now concretely means

**PROPOSITION P7 (literal cycle recurrence; review/formalization pending).**
Write a parent Z vector as arrays U(i,j),V(i,j) on A,B and extend both by zero
off the board. It commutes with every parent X check if and only if

```text
U(a,b)+U(a,b+3)+U(a+2,b+2)+U(a+3,b)
+ V(a,b+1)+V(a+1,b+1)+V(a+2,b)+V(a+3,b+3)=0          (13)
```

for `0<=a<=13`, `-3<=b<=16`.

**Proof.** This is exactly the dot product with X(a,b), and P3 lists all the
parent X rows. Thus necessity and sufficiency follow row by row, including
the zero-extension boundary terms.

For example the first three left boundary equations are, for each a,

```text
b=-3: U(a,0)+V(a+3,0)=0,
b=-2: U(a,1)+U(a+2,0)+V(a+3,1)=0,
b=-1: U(a,2)+U(a+2,1)+V(a,0)+V(a+1,0)+V(a+3,2)=0.
```

The right boundary equations follow from the b=14,15,16 templates. The
displacements in (13) reach only three steps along either axis. These are
explicit three-strip boundary relations, not a proof of an invertible
transfer rule: solving the bulk equation for a new column can have a kernel.

**NAMED UNPROVED HYPOTHESIS H_charge / next structural task.** Construct a
map from finite-board cycles modulo the displayed boundary stabilizers to
the algebra in P6 (or its appropriate dual), prove its kernel and image,
and track the six consecutive deletions in P5 under that map. Neither
surjectivity, completeness, nor conservation at the clipped edges is assumed.
The exact question is whether the boundary recurrences impose coupled charge
constraints across those six missing pair checks. Polynomial ideal equality
alone cannot answer it because clipped boundaries can absorb charges.

There is now concrete input for that task: exact ordered row formulas,
all twelve boundary templates, anchor positions of the removals, and a
polynomial quotient with explicit eighteen-dimensional normal form. One can
derive strip relations directly from (13), then test their invariance under
each Z boundary template symbolically. A successful result must show which
relations survive the deletion of `Z(19,3),...,Z(19,8)` and distinguish a
finite-board logical class from a boundary stabilizer. No such bridge or
global distance conclusion is asserted in this note.

## 8. Validation and independent-review boundary

Read AGENTS.md and the actual source JSON; inspected the boundary builder's
coordinate conventions without invoking it. Read-only Python checks compared
both proposed and corrected models to the literal rows. The corrected
ordered lists matched in full. The counterexample supports and the removal
anchor indices were checked directly. Exact symbolic polynomial operations
were used to discover and check P6; no floating-point rank, distance search,
Lean run, or exhaustive logical certificate was used.

The finite input interface is PROPOSITION. P1–P7 and their mathematical
proofs remain PROPOSITION, independent review and formalization pending.
H_charge remains a NAMED UNPROVED HYPOTHESIS. In particular this note does
not upgrade the parent's or target's distance status. It leaves the previous
lifting notes and their counterexamples unchanged.
