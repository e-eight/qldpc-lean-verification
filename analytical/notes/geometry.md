# Geometry and boundary homology: independent analytic route

Date: 2026-11-11. Scope: submitted 722-8-20, with a comparison to 566-18-20.
Owned outputs are this note, `analytical/planar722/DRAFT.tex`, and
`analytical/planar722/RESEARCH.tex`. No Lean, distance search, or exhaustive-search
certificate was run or used. **This note does not prove distance 20.** It proves
bulk exactness, the encoded dimension, and an exact boundary reduction for 722;
it gives an explicit counterexample to an overly strong geometric premise and
states the remaining weight inequality precisely.

Required grades: **THEOREM** = refereed complete; **PROPOSITION** = claim
with a named gap; **CONJECTURE** = unproved mathematical claim; **FALSE** =
refuted claim. All derived results below are **PROPOSITION**, with the named
gap **independent review/formalization pending**; a supplied proof is not a
referee report. Input recognition additionally needs independent replay. No
result in these notes is graded THEOREM. The boundary weight-20 assertion is
CONJECTURE, and the outer-edge spanning premise is FALSE.

The self-contained finite-model main result is now developed in
[the draft](../planar722/DRAFT.tex). Its hypotheses do not involve JSON
matching, and its dimension proof needs no bulk UFD argument.

## Input recognition [PROPOSITION: independent replay pending]

Read both repositories' AGENTS.md, this repository's README.md and
RECOMMENDATIONS.md, `data/lifting-566-investigation/README.md`,
`data/removal566-literature/README.md`, and upstream notes and construction
sources. Upstream checkout: `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.
Source paths below are relative to `../qldpc-challenge` from this repository's
root, not relative to this note.

| Source | SHA-256 |
| --- | --- |
| `codes/722-8-20.json` | `4ab209d0c450dc7a96e6054ed29322808be87ee52eb3002c51ab4531dcc91b15` |
| `research/local2d/planar.py` | `a8391a056a12bda6cf6afe9d59621bcffa2f00d812684619c2a4dac514f6e4eb` |
| `codes/566-18-20.json` | `061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be` |

Set L=19. Qubits are A(i,j)=19i+j and B(i,j)=361+19i+j,
with 0<=i,j<=18. The rotated drawing is (i+j,j-i) for A and
(i+j,j-i+1) for B. Work in unrotated cell coordinates for the proof.
Let

```
f = x + x^2 + y^2,
g = 1 + x^2 y + x^2 y^2,
bar p(x,y) = p(x^-1,y^-1).
```

Let P restrict both components to the square Q=[0,18]^2. The literal rows are

```
X(a,b) = P(x^a y^b (f,g)),       -2 <= a <= 18,  0 <= b <= 16;
Z(c,d) = P(x^c y^d (bar g,bar f)), 2 <= c <= 18, 0 <= d <= 20.
```

They occur in lexicographic anchor order. A standard-library Python 3.13
reconstruction of these sparse sets, including the builder's corner-conflict
test, matched both submitted row lists literally. There are 357 rows of each
type and **zero corner drops**. Each list has 289 weight-six, 34 weight-three,
17 weight-four and 17 weight-two rows. This was construction recognition, not
enumeration of errors or logical operators; no upstream module was imported.

The following proofs concern exactly these formulas. The sole computational
transport step is their literal match to the JSON.

## Lemma 1: commutation and independent boundary checks [PROPOSITION: independent review/formalization pending]

**PROPOSITION (independent review/formalization pending).** These two check sets commute and each is linearly independent.
Consequently the code encodes 722-357-357=8 qubits.

**Proof of commutation.** On the infinite lattice the intersection parity of
an X translate and a Z translate is a coefficient of fg+gf=0. Every full X
row has all its column coordinates j in [0,18], even when it extends outside
the square in i. Every full Z row has all its row coordinates i in [0,18],
even when it extends outside in j. Thus every intersection of the two full
rows is already inside Q. Restriction deletes no intersection and preserves
their zero parity. This also explains why no corner conflict occurs here.

**Proof of X independence.** Encode a linear combination of X anchors by
`c=sum c_i(y)x^i`, with -2<=i<=18 and each c_i supported in y degrees 0..16.
If P(fc,gc)=0, no y term of either product is truncated. Therefore, as
identities in the integral domain F2[y], for every i=0,...,18,

```
c_(i-2) + c_(i-1) + y^2 c_i = 0,
t c_(i-2) + c_i = 0,                 t = y+y^2.
```

Set b=1+y^2 t=1+y^3+y^4. The equations give
`c_(i-1)=b c_(i-2)`. In particular c_-1=b c_-2 and
c_0=b c_-1=b^2 c_-2, while c_0=t c_-2. Hence

```
(b^2+t)c_-2 = (1+y+y^2+y^6+y^8)c_-2 = 0.
```

The multiplier is nonzero, so c_-2=c_-1=0. The second recurrence then
forces c_0,...,c_18=0. All 21*17 X rows are independent.

**Proof of Z independence.** Reflect Q by (i,j)->(18-i,18-j), and exchange
A and B. A Z combination becomes P(fc,gc), now with anchor polynomial c
supported in x degrees 0..16 and y degrees -2..18. This is used only as a
coordinate change in this proof; it is not asserted to be a code symmetry.
Write c=sum c_j(x)y^j and a=x+x^2. Vanishing gives, for j=0,...,18,

```
c_(j-2) + a c_j = 0,
c_j + x^2 c_(j-1) + x^2 c_(j-2) = 0.
```

Set b=1+x^2 a=1+x^3+x^4. Then `x^2 c_(j-1)=b c_j`.
At j=0,1 this yields x^4 c_-1=b^2 c_1. Since c_-1=a c_1,

```
(b^2+x^4 a)c_1 = (1+x^5+x^8)c_1 = 0.
```

Thus c_1=0, then c_0=0 by the j=1 second relation, and
c_-2=c_-1=0 by the first relations. Since a is nonzero, the first
recurrence forces all remaining c_j=0. All 17*21 Z rows are independent.
The CSS dimension formula now gives k=8. QED.

## Lemma 2: exact bulk homology and a boundary-strip obstruction [PROPOSITION: independent review/formalization pending]

Use the Laurent polynomial ring R=F2[x^±1,y^±1]. A finitely supported X
operator is a pair (u,v), and its full-plane Z syndrome is
`sigma_X(u,v)=g u+f v`. Its coefficient at (c,d) is precisely its overlap
with the full Z row anchored there. The corresponding Z syndrome is
`sigma_Z(u,v)=bar f u+bar g v`.

**PROPOSITION (independent review/formalization pending).** Every finitely supported full-plane X cycle has the unique form
(fc,gc), c in R. Every finitely supported full-plane Z cycle has the unique
form (bar g c,bar f c). If such an operator is supported in Q, it is a sum
of fully supported submitted bulk stabilizers. In particular:

* an X logical must meet one of the rows i=0,1,17,18;
* a Z logical must meet one of the columns j=0,1,17,18.

The assertion is a union of boundary strips; it does not say both strips
are met, nor assign any minimum weight.

**Proof.** First f and g are relatively prime. The explicit elimination is

```
g+x^2 f = 1+x^3+x^4+x^2 y,
(g+x^2 f)^2+x^4 f = 1+x^5+x^8.
```

A common irreducible factor must therefore divide the nonzero polynomial
1+x^5+x^8. Its irreducible factors in the Laurent ring depend only on x:
irreducibles of F2[x^±1] stay prime after adjoining y and y^-1. But no
nonunit depending only on x divides f, whose coefficient of y^2 is 1.
This proves relative primality in the unique factorization domain R.

If gu+fv=0, then f divides gu, hence divides u. Write u=fc; cancellation
in the domain gives v=gc. Conversely this pair has zero syndrome, and c
is unique. Applying the bar involution and exchanging components proves
the Z statement. This is a syzygy argument; relative primality is **not**
being confused with the stronger and generally false assertion (f,g)=R.

For nonzero Laurent polynomials, minimum and maximum x exponents add
under multiplication: view their extreme coefficients in the domain
F2[y^±1], where their product cannot vanish. The same holds for y.
Since the minimum exponents of f are 0 and the maximum exponents are 2
in both variables, support of fc in Q forces support of c into [0,16]^2.
Thus every X full-plane cycle in Q is a combination of the 289 full bulk
rows. In the Z case bar g has extrema -2 and 0 in both variables, so c
lies in [2,18]^2 and again gives 289 full bulk rows. The zero operator
is covered by c=0.

Finally, an X operator supported in 2<=i<=16 has full syndrome supported
in [2,18]x[0,20]. Every one of these anchors is a retained Z check.
If it is an open-code cycle, all these coefficients vanish; it is therefore
a full-plane cycle and hence an X stabilizer. For a Z operator supported
in 2<=j<=16, the full syndrome lies in [-2,18]x[0,16], all retained X
anchors. The same conclusion follows. QED.

This rules out all interior logicals, irrespective of weight or support
connectivity. It is stronger than checking small interior errors, but it
does not control logicals ending on or running along a boundary.

## Lemma 3: an exact boundary quotient, with its weight gap [PROPOSITION / CONJECTURE: boundary weight bound open]

Let C_X=ker H_Z and S_X=row H_X, with their actual physical coordinates.
For an X cycle, sigma_X can be nonzero only on

```
E_X = {0,1,19,20} x {0,...,20}.
```

Let D_X=sigma_X(C_X) and T_X=sigma_X(S_X), viewed as subspaces of
F2^(E_X). Then sigma_X induces an isomorphism

```
C_X / S_X  -->  D_X / T_X.
```

**Proof.** Commutation gives T_X contained in D_X. Surjectivity follows
from the definition of D_X. If sigma_X(w) lies in T_X, choose s in S_X
with the same syndrome. Then sigma_X(w+s)=0, and Lemma 2 puts w+s in
S_X, so w is in S_X. This proves injectivity. QED.

There is an identical statement for Z with

```
E_Z = {-2,...,18} x {-2,-1,17,18},
C_Z=ker H_X, S_Z=row H_Z,
D_Z=sigma_Z(C_Z), T_Z=sigma_Z(S_Z).
```

These are boundary charge spaces of at most 84 coordinates each, with
**dim D_X=dim D_Z=76 and dim T_X=dim T_Z=68**. Indeed Lemma 1 gives
dim C=365 and dim S=357. Lemma 2 identifies the kernel of each full
syndrome, both on C and on S, with the 289-dimensional bulk stabilizer
space. The dimension differences give 76 and 68. Thus precisely eight
independent boundary classes survive on each side, without a matrix rank
computation or any distance search.

Here is the exact remaining analytic obligation. For alpha in D_X/T_X set

```
mu_X(alpha) = min { wt(u)+wt(v) : support(u),support(v) subset Q,
                  sigma_X(u,v) supported on E_X,
                  [sigma_X(u,v)] = alpha }.
```

Define mu_Z analogously. Distance 20 follows if and only if
`mu_X(alpha)>=20` and `mu_Z(beta)>=20` for every nonzero boundary class
alpha,beta, together with the existing weight-20 witness below. Importantly,
the cost is physical coefficient count, **not** the number of nonzero
boundary syndrome coefficients. The displayed witness has weight 20 and
only four such coefficients.

Equivalently, a sufficient and necessary lower-bound theorem is the following
explicit polynomial assertion, and its barred Z counterpart:

> For u,v supported in Q with total coefficient count at most 19, if
> gu+fv is supported on E_X, there is a polynomial c supported on
> [-2,18]x[0,16] such that (u,v)=P(fc,gc).

This assertion is graded **CONJECTURE** and is **unproved here**. Lemma 2 proves its zero-full-syndrome
case, not the nonzero boundary-defect cases. An analytic completion should
classify the boundary charge quotient using the two elimination recurrences
above and establish a coefficient-count bound for every nonzero class,
including arbitrary stabilizer additions and cancellations at both ends.
An abstract homology isomorphism or a change of check basis alone does not
control this cost. No weight bound of 20 is claimed from the dimension 8.

## Explicit counterexample to an outer-edge spanning premise [FALSE]

The tempting assertion “every X logical touches i=0 and i=18” is false for
the actual submitted 722 matrices. So is the assertion “every Z logical
touches j=0 and j=18.” Use these submitted supports, in zero-based numbering:

```
X = {65,103,104,105,142,162,199,219,220,332,
     390,407,426,504,541,560,561,579,598,617,619,636,655}
Z = {46,47,61,63,65,66,80,97,131,150,167,
     409,424,425,446,448,456,486,487,526}.
```

They have weights 23 and 20. Here is a short algebraic verification of cycle
membership, without a row-space computation. Split each support into the
A/B polynomial pair. Direct multiplication and cancellation gives

```
sigma_X(X) = x y^12 + x^19 y^10 + x^19 y^11,
sigma_Z(Z) = x^3 y^-2 + x^3 y^-1 + x^4 y^17 + x^6 y^17.
```

All displayed monomials are outside the corresponding retained check-anchor
rectangles, so both opposite-check syndromes vanish. Their supports intersect
in exactly {65}, giving odd pairing. By commutation, neither can be its
own-type stabilizer: such a stabilizer would pair evenly with every opposite
cycle. Thus both are nontrivial logicals, and d<=20 is independently verified.
The X support has row range 1..17 and touches neither outermost row. The Z
support has column range 0..17 and does not touch the last column. The
counterexample refutes the outer-edge premise, **not distance 20**. It is
consistent with the two-cell-strip conclusion of Lemma 2.

A second geometric obstruction is visible without any logical calculation:
A(9,9) belongs to three Z checks at anchors (9,9), (11,10), (11,11).
It belongs to three X checks at (7,9), (8,9), (9,7). Thus the supplied check
matrices are not vertex-edge incidence matrices of an ordinary surface-code
graph in these bases: an edge has at most two endpoints. This does not exclude
a different homological model or a basis change. Any such identification
must prove its effect on physical Hamming weight before importing a graph
path-length lower bound. In particular, 19 cell rows do not by themselves
give 20 qubits in a logical operator.

## Why this route prioritizes 722 over 566 [PROPOSITION / CONJECTURE: recognition and weight gaps]

The submitted 566 construction uses a different pair:

```
f = 1+y^3+x^2 y^2+x^3,
g = y+xy+x^2+x^3 y^3.
```

It is a reduced 17x17, 578-qubit parent. The upstream boundary engine explicitly
distinguishes this from the published tile and other support variants; the
bulk name or the parameter triple is insufficient to transfer a distance
claim. Unlike 722's literal directional truncations, the general engine also
uses secondary boundary generators and corner completion. No identification
of the 566 code with the 722 chain complex is asserted.

The existing `data/lifting-566-investigation/README.md` identifies six removed
pairs and retained fans r_i. Its exact normal form gives

```
dX_parent = min_(x final X logical,t in F2^6)
              wt(x + sum t_i r_i) + 2 wt(t),
dZ_parent = min_(z final Z logical) wt(z) + wt(R(z)),
R(z)_i = r_i dot z.
```

The first formula permits a final X lower bound from a parent lower bound;
the second does not preserve Z distance. Even assuming parent dZ>=20,
final weights 14..19 with wt(z)+wt(R(z))>=20 remain possible. Parent
distance 20 is itself unproved by the source's witnesses. The fan parity map
being onto on stabilizers does not bound the weight of a parity correction.

Thus a 566 completion requires both a parent boundary weight theorem and
a weight-controlled six-pair removal theorem, or a direct theorem for the
final boundary. The 722 route above avoids this additional removal gap.
Its remaining gap is exactly the two boundary-cost inequalities in Lemma 3.

## Validation and outcome

Performed only bounded, direct sparse construction comparison and polynomial
syndrome arithmetic with Python 3.13; the nontriviality check is the explicit
odd pairing above. No logical enumeration, RIS, SAT, MILP, exhaustive-search
certificate, Lean invocation, dependency installation, or upstream write.

Established: a pen-and-paper dimension proof, bulk exactness, the necessary
boundary strips, and an exact 76/68-dimensional boundary quotient for the
submitted 722 construction (subject only to the recorded literal input match).
Refuted: outermost-edge spanning for actual logical representatives.
Open: a physical coefficient-count lower bound of 20 for every nonzero class
in both boundary quotients. These notes provide a concrete analytic reduction,
not a completed distance-20 proof.


## New recurrence mechanism [PROPOSITION: independent review/formalization pending]

Write u=sum u_i(y)x^i and v=sum v_i(y)x^i for an X operator in the finite
722 model. Put t=y+y^2 and F_i=v_(i-1)+v_(i-2)+y^2 v_i. Since the retained
Z anchors contain every possible y syndrome degree, the cycle equations are
exact polynomial identities

```
u_i = t u_(i-2) + F_i,                 2 <= i <= 18.
u_(r+2m) = t^m u_r + sum_(ell=1)^m t^(m-ell) F_(r+2ell),
r=0, 1; m<=9 for r=0, m<=8 for r=1.
```

The second formula follows by substitution and induction. It gives two
propagation channels with explicit forcing from the B block. This is a
physical-coefficient recurrence, rather than just boundary homology.

In particular, **every nonzero X cycle supported only on A has weight at
least 29**. With v=0, degree growth in u_18=t^9 u_0 forces deg u_0<=0;
degree growth in u_17=t^8 u_1 forces deg u_1<=2. A nonzero even channel
has weight 33. Up to a monomial shift, the nonzero odd seeds are
1, 1+y, (1+y)^2, 1+y+y^2. Their nine-slice weights are respectively
29, 32, 34, 43, by expanding (1+y)^m times the seed for 0<=m<=8.
[RESEARCH.tex](../planar722/RESEARCH.tex) preserves the full small coefficient table and its algebraic
verification rule. This is a four-form polynomial calculation, not an
exhaustive distance-search certificate. Equality 29 is attained by
u=sum_(m=0)^8 x^(1+2m) y^m(1+y)^m, v=0; this asserts a cycle, not a logical.

Thus any hypothetical X logical below weight 20 must use the B block.
A mixed cycle can cancel propagated coefficients through the explicitly
shown F_i; counting the unforced slices alone is invalid. The next specific
obligation is a cancellation inequality for this forced recurrence, modulo
X stabilizers, with cost sum_i(wt(u_i)+wt(v_i)). The analogous opposite-sector
bound remains necessary. Neither inequality is claimed solved.


## Frozen review checkpoint

[DRAFT.tex](../planar722/DRAFT.tex) is frozen for three independent
**document-only** referees. Its scope is the explicit finite construction,
commutation, both ranks 357, and binary quotient dimension 8. The quantum
interpretation and all distance research are preserved separately in
[RESEARCH.tex](../planar722/RESEARCH.tex). The user reports that referee Volta passed the main argument, with precision
objections now addressed: the title says rectangular, and external input and
distance assertions are excluded. This records the user-supplied report, not
an independently retrieved referee document. The remaining independent reviews
and formalization are pending; no claim has been upgraded. A final PROOF must
contain only fully refereed and formalized claims; none is issued here.
The quantum interpretation's formalization bridge remains unestablished.


## Mixed-block elimination route [PROPOSITION: independent review/formalization pending]

This route is research-only and does not alter the frozen draft. For an X
cycle (u,v), write its row slices as u_i,v_i in F2[y]. Let L retain degrees
0..16 and H retain degrees 17..18. Put t=y+y^2 and c_-2=c_-1=0. Define
successively, for i=0,...,18,

```
c_i = L(v_i + t c_(i-2)),
b_i = H(v_i + t c_(i-2)),
a_i = u_i + y^2 c_i + c_(i-1) + c_(i-2).
```

Then (a,b) is stabilizer-equivalent to (u,v), and every B coefficient of b
lies in columns 17 or 18. Proof: c=sum x^i c_i uses only allowed X anchors
0<=i<=18, 0<=j<=16. Add P(fc,gc). The B slice becomes
v_i+c_i+t c_(i-2)=b_i; all terms have degree at most 18, so L and H
exhaust that slice. The A slice is exactly a_i. Addition of a stabilizer
preserves the cycle and its logical class by commutation. Uniqueness among
these 323 allowed row operations follows inductively: two such cleanings
differ by c with L(c_i+t c_(i-2))=0; c_-2=c_-1=0 forces c_i=0 in order.
This is a triangular normal form for mixed cycles, not a distance bound.

There remain 34 X generators anchored at i=-2,-1; cleaning their images
must still be accounted for when taking logical classes. The normal form
is not claimed weight-nonincreasing. Its exact change of physical weight
is wt(s)-2|support(w) intersect support(s)| for w=(u,v) and
s=P(fc,gc), since binary addition takes symmetric difference of supports.
Thus a large normal-form weight alone cannot lower-bound the original
weight. The specific gap is a bound on the overlap term, or a cost function
invariant under these cleanings whose value lower-bounds original physical
weight. Such a bound must also handle the remaining 34 generators and the
opposite sector. The one-block29 result cannot be applied to the two-column
B remainder as if it were zero. No mixed-block distance inequality is claimed.
