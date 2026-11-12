# Algebraic distance route for 566-18-20 and 722-8-20

2026-11-11. Required four-grade scheme:
**THEOREM** = refereed complete; **PROPOSITION** = claim with a named gap;
**CONJECTURE** = unproved mathematical claim; **FALSE** = refuted claim.
All supplied derivations are **PROPOSITION**, with the named gap
**independent review/formalization pending**. Input recognition also needs
independent replay. No result here is graded THEOREM. Unproved distance
assertions are CONJECTURE; refuted implications are explicitly FALSE.
The proofs below are mathematical arguments, not Lean results. No Lean was
run. In particular, this note does **not** claim either target has distance 20.
It proves an analytic lower bound of nine in both sectors of the literal
722 code, identifies its eight-dimensional bulk charge module, identifies an
eighteen-dimensional bulk charge module for the actual 566 ancestor, and proves
local exactness and explicit obstructions to extending these results to a
distance-20 theorem. Proposition 8 closes charge completeness by a boundary
image argument; the earlier bound of three is retained as a separate check.
No distance search, logical-support enumeration, packing
certificate, or numerical distance estimate is a premise.

## Definitions and source identification

Read: root `AGENTS.md`, `README.md`, `RECOMMENDATIONS.md`,
`data/lifting-566-investigation/README.md`, and, in the sibling upstream checkout,
`notes/{566-18-20,578-18-20,722-8-20}.md`,
`research/local2d/{planar,boundary_engine}.py`, and the corresponding code JSONs.
Upstream HEAD is `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`;
verification-repository HEAD is `a38eb7aecff05c6cfe7975025f48d5d7322dbca1`.
The existing worktree has other edits; none are modified here.

Raw upstream JSON SHA-256 identifiers:

| Input | SHA-256 |
|---|---|
| 722-8-20 | `4ab209d0c450dc7a96e6054ed29322808be87ee52eb3002c51ab4531dcc91b15` |
| 578-18-20 | `440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514` |
| 566-18-20 | `061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be` |

Use (R=\mathbb F_2[x^{\pm1},y^{\pm1}]), with coefficient Hamming weight,
not degree, as physical weight. A cell ((i,j)) is the monomial (x^iy^j).
There are two qubits A and B per cell. A Pauli sector is a pair ((a,b)\in R^2).
Write \(\bar h=h(x^{-1},y^{-1})\).
The bulk X generator is ((f,g)); the bulk Z generator is
((\bar g,\bar f)). Consequently the full-plane X syndrome is

\[
\partial_X(a,b)=ga+fb,\qquad
\partial_Z(a,b)=\bar f a+\bar g b. \tag{1}
\]

These conventions follow the actual builders, including the block order.
The two relevant polynomial pairs are

\[
\begin{array}{c|ll}
 &f&g\\\hline
722&x+x^2+y^2&1+x^2y+x^2y^2\\
578\text{ ancestor of }566&1+y^3+x^2y^2+x^3&y+xy+x^2+x^3y^3.
\end{array} \tag{2}
\]

For 566, do not substitute `S_G_TILE4_MAIN` from `boundary_engine.py`:
that constant has support \(\{(0,2),(1,3),(2,0),(3,3)\}\), which is a
different polynomial. Nor is the ancestor the published tile whose second
support contains ((1,0)) instead of ((2,0)). The ancestor has a 17-by-17
cell board and a 14-by-14 set of fully supported X translates. The two uses
of “bulk size” in the upstream notes should not be confused.

## PROPOSITION 1: exact elimination for the 722 bulk

Set
\[
s=x^{-2}+x+x^2,\quad h=y+s,\quad p=x^8+x^5+1.
\]
Then
\[
h=x^{-2}g+f,\qquad
p=x^4(f+h^2),\qquad
f=h^2+x^{-4}p,\qquad g=x^2(h+f). \tag{3}
\]
Thus ((f,g)=(h,p)) as ideals of (R), and
\[
R/(f,g)\simeq\mathbb F_2[x]/(x^8+x^5+1),\qquad y\longmapsto s. \tag{4}
\]
This is an eight-dimensional vector space. It does not require (p) to be
irreducible.

**Proof.** Expand (3) in characteristic two. The constant term of (p) makes
(x) invertible modulo (p). Also (p(1)=1), so (1+x) is invertible there.
Equation (3) gives (s^2=x+x^2=x(1+x)) modulo (p), hence (s) is invertible.
The Laurent inverses impose no additional quotient. Division by the monic
degree-eight polynomial gives basis (1,x,\ldots,x^7). This proves (4).
Finally (h=y+s) cannot divide a nonzero polynomial in (x); hence (h,p),
and therefore (f,g), have no common nonunit divisor. ∎

The quotient is a bulk **syndrome/charge** module, not a physical logical
space equipped with its distance. Its dimension being eight is consistent
with the target name, but does not by itself prove finite-board (k=8).

## PROPOSITION 2: the actual 566 ancestor has coprime bulk generators

For the second pair of (2), the resultant with respect to (y) is
\[
q(x)=x^{18}+x^{15}+x^{14}+x^{13}+x^{11}+x^{10}
       +x^6+x^5+x^4+x^2+x+1. \tag{5}
\]
In particular (f,g) are coprime in (R). Moreover
\[
\dim_{\mathbb F_2}R/(f,g)=18. \tag{6}
\]

**Proof, including a reproducible symbolic specification of (5).** The
resultant is the following determinant over \(\mathbb F_2[x]\):
\[
\det\begin{pmatrix}
1&x^2&0&1+x^3&0&0\\
0&1&x^2&0&1+x^3&0\\
0&0&1&x^2&0&1+x^3\\
x^3&0&1+x&x^2&0&0\\
0&x^3&0&1+x&x^2&0\\
0&0&x^3&0&1+x&x^2
\end{pmatrix}. \tag{7}
\]
Expanding (7) gives (5). This is polynomial arithmetic, not a search over
codewords. For coprimality one does not even need that expansion: at (x=0),
the polynomials are (y^3+1,y), and the determinant is 1. Thus the resultant
is nonzero. There is no common factor of positive (y)-degree over
\(\mathbb F_2(x)\); no nonconstant factor in (x) can divide the monic
polynomial (f\in\mathbb F_2[x][y]). Gauss's lemma gives coprimality.

For (6), put (A=\mathbb F_2[x]) and
(B=A[y]/(f)). This is free of rank three over (A).
Multiplication by (g) on (B) has determinant (7). Its cokernel is
(\mathbb F_2[x,y]/(f,g)). Over the Euclidean domain (A), diagonal
reduction of this square presentation gives cyclic summands (A/(d_i));
the sum of their dimensions is
\(\sum_i\deg d_i=\deg\prod_i d_i=\deg q=18\).
The nonzero determinant ensures there is no free summand.
Localization does not change this space: modulo (x), the ideal contains
(y,y^3+1), so (x) is already a unit in the quotient. Modulo (y), it
contains (x^2,1+x^3), whose combination (1+x^3+x\cdot x^2=1)
shows that (y) is already a unit. ∎

This proves a bulk algebra statement for the pair actually recorded for the
ancestor, not an equality between a reconstructed `build_planar` output and
the submitted boundary matrices. No such boundary equality is assumed here.

## PROPOSITION 3: finite-support bulk exactness, with support control

For either pair in (2),
\[
\ker[\,g\ f\,]=R(f,g),\qquad
\ker[\,\bar f\ \bar g\,]=R(\bar g,\bar f). \tag{8}
\]
Thus there are no finite-support full-plane logical operators in either sector.

**Proof.** The Laurent polynomial ring is a unique factorization domain.
If (ga=fb) and (gcd(f,g)=1), Euclid's lemma implies (f\mid a).
Write (a=ft); cancellation in the domain gives (b=gt). The converse
is (gft+fgt=0). Apply inversion and exchange the components for Z. ∎

There is useful geometric control here, not just abstract exactness. Let
(r=2) for 722 and (r=3) for the ancestor. Both (f,g) have minimum
exponent zero and maximum exponent (r) in each coordinate. For any
nonzero (t),
\[
\min_x(ft)=\min_x(t),\quad\max_x(ft)=\max_x(t)+r,
\quad\min_y(ft)=\min_y(t),\quad\max_y(ft)=\max_y(t)+r. \tag{9}
\]
The same is true for (gt). For example, viewing these as polynomials in
(x) over the domain \(\mathbb F_2[y^{\pm1}]\), the extreme coefficients
multiply to nonzero coefficients. This proves (9), including the assertion
that cancellation cannot destroy an extreme face.

Consequently, if an X cycle has support in a rectangle (D), and its **full**
syndrome vanishes, every monomial of its unique (t) gives a translate of
((f,g)) fully contained in (D). Reflection gives the Z version.
On a finite board containing every fully supported bulk check, a cycle whose
bounding box is at least (r) cells from every board edge therefore is a
stabilizer: all opposite translates meeting it are fully supported checks,
so its finite zero syndrome is its full zero syndrome; then apply (8)-(9).
This last implication is conditional on the stated bulk-check inclusion,
not on a numerical matrix-rank computation.

For 566, after a deletion, one must first lift to the ancestor and check this
support hypothesis there. Puncturing the polynomial pair and continuing to
use (8) as if the Laurent-module action survived is invalid.

## PROPOSITION 4: literal 722 rectangle and analytic (d_X,d_Z\ge3)

Here (L=19), (A(i,j)=19i+j), (B(i,j)=361+19i+j), and
(0\le i,j\le18). Define (T) to discard monomials outside this square.
The literal check rows, in their JSON order, are precisely
\[
\begin{split}
X_{c,d}&=T(x^cy^d(f,g)),& -2\le c\le18,&\quad0\le d\le16,\\
Z_{c,d}&=T(x^cy^d(\bar g,\bar f)),&2\le c\le18,&\quad0\le d\le20.
\end{split} \tag{10}
\]
Order the first index first, then the second. Each list has 357 rows.
A direct read-only comparison against the JSON gave literal equality of
both ordered lists. This comparison recognizes the input; it is not a
distance certificate. Formula (10) also follows from `build_open_directional`:
X columns must fit fully, and Z rows must fit fully. Any overlap between a
full X translate and a full Z translate outside the board would have to be
outside both a row and a column, which neither pair permits. Thus truncation
preserves their full-plane zero pairing; no corner conflicts remain for (10).

Here is a complete symbolic classification of cycles of weight at most two.
It uses variable indices, not an enumeration of supports on the board.

### X sector

Let (P) keep (x)-exponents 2 through 18 and all (y)-exponents.
The Z-check syndrome of A(i,j) is (P(x^iy^jg)); that of B(i,j) is
(P(x^iy^jf)). All possible (y)-exponents of these products are 0 through
20, so this is exactly the finite syndrome in (10).
Removing the common factor (y^j), these columns are:

| Qubit row (i) | A column divided by (y^j) | B column divided by (y^j) |
|---|---|---|
| 0 | (x^2(y+y^2)) | (x^2) |
| 1 | (x^3(y+y^2)) | (x^2+x^3) |
| (2\le i\le16) | (x^i+x^{i+2}(y+y^2)) | (x^iy^2+x^{i+1}+x^{i+2}) |
| 17 | (x^{17}) | (x^{17}y^2+x^{18}) |
| 18 | (x^{18}) | (x^{18}y^2) |

Every column is nonzero, excluding weight one. Distinct qubits give equal
columns only for
\[
A(18,j)\quad\hbox{and}\quad B(18,j-2),\qquad2\le j\le18. \tag{11}
\]
To verify completeness of this comparison, first group columns by their
number of monomials. Among triples, A has two distinct (x)-levels whereas
B has three; within each group the levels and (y)-shift recover (i,j).
Among doubles, A has one (x)-level whereas B has two; B's row-1 and row-17
levels differ. Among singles, the only shared (x)-level between distinct
column families is row 18 of A and B. Their exponents give (11).
Each pair (11) is exactly (X_{18,j-2}). Thus every X cycle of weight two
is an X stabilizer, proving (d_X\ge3).

### Z sector

Let (Q) keep (y)-exponents 0 through 16 and all (x)-exponents.
The X-check columns are (Q(x^iy^j\bar f)) for A and
(Q(x^iy^j\bar g)) for B. Their (x)-exponents automatically lie in
the check-index range -2 through 18. Explicitly:

| Qubit column (j) | A syndrome | B syndrome |
|---|---|---|
| 0 | (x^{i-1}+x^{i-2}) | (x^i) |
| 1 | (y(x^{i-1}+x^{i-2})) | (x^iy+x^{i-2}) |
| (2\le j\le16) | (y^j(x^{i-1}+x^{i-2})+x^iy^{j-2}) | (x^iy^j+x^{i-2}(y^{j-1}+y^{j-2})) |
| 17 | (x^iy^{15}) | (x^{i-2}(y^{16}+y^{15})) |
| 18 | (x^iy^{16}) | (x^{i-2}y^{16}) |

Again no column vanishes. For triples, the number of (y)-levels is two for
A and three for B. For doubles, A has one (y)-level and two (x)-levels;
B at (j=1) has two of each, and B at (j=17) has two (y)-levels and one
(x)-level. Their within-family shifts are unique. Comparing the singles
leaves only
\[
A(i,18)\quad\hbox{and}\quad B(i+2,18),\qquad0\le i\le16. \tag{12}
\]
Their sum is (Z_{i+2,20}). Thus (d_Z\ge3). For a CSS Pauli logical,
at least one sector is a nontrivial sector logical and its weight does not
exceed the Pauli support weight, so the full Pauli distance is at least three. ∎

This bound is intentionally modest but unconditional for the recognized
input. Extending the column comparison to a support search would leave the
analytic route; it is not the proposed means of reaching twenty.

## PROPOSITION 5: two explicit counterexamples to bulk-only lower bounds

**Same polynomials, wrong boundary: distance one.** For either pair of (2),
take an (L\)-by-(L) board with (L=19,r=2) or (L=17,r=3), respectively,
and keep *only* fully supported bulk X and Z translates. This defines a
commuting CSS code. The single qubit A(L-1,0) is an X logical.

**Proof.** Fully supported Z centers have both coordinates between (r)
and (L-1). For the 722 (g), the centers that could touch A(L-1,0) are
((L-1,0),(L+1,1),(L+1,2)), none allowed. For the ancestor (g), they are
((L-1,1),(L,1),(L+1,0),(L+2,3)), again none allowed. Thus its finite
syndrome is zero. It is not a sum of full X translates: all such sums have
zero full-plane syndrome by (1), while the full-plane syndrome of this
single qubit is the nonzero monomial multiple (x^{L-1}g). ∎

This is a counterexample using the **actual bulk pairs**, not a claim of
a weight-one logical in either submitted target. It shows that (4), (6),
coprimality, and local exactness alone cannot prove a finite-board lower bound
larger than one. Boundary recognition is indispensable.

**Degree/charge dimension is not weight.** In (4),
\[
[x^8]=[x^5+1],\qquad [1+x^5+x^8]=0. \tag{13}
\]
A monomial and a binomial represent the same charge, and a polynomial with
span eight and weight three represents zero. Frobenius powers give
(1+x^{5\cdot2^m}+x^{8\cdot2^m}\in(p)), still of weight three and
unbounded span. Therefore neither polynomial degree nor support span supplies
a Hamming-weight lower bound without an additional constraint on admissible
physical representatives. Equation (13) is not itself a logical operator;
it refutes the proposed inference about the metric of the charge module.

## PROPOSITION 6: paired deletion has a real, sharp Z-weight defect

Here is a purely algebraic form of the actual six-pair removal pattern.
Let final stabilizer spaces on retained coordinates (K) be
(U',V'\subseteq\mathbb F_2^K), with (U'\perp V'). Add disjoint pairs
((a_i,b_i)) and retained vectors (r_i), for (1\le i\le m). Suppose the
old stabilizer spaces are exactly
\[
\begin{split}
U&=\langle (u,0,0):u\in U';\ (r_i,e_i,e_i):1\le i\le m\rangle,\\
V&=\langle (v,Rv,0):v\in V';\ (0,e_i,e_i):1\le i\le m\rangle,
\qquad (Rv)_i=r_i\cdot v .
\end{split} \tag{14}
\]
Then the two sector distances satisfy the exact variational identities
\[
\begin{split}
d_X^{\rm old}
 &=\min_{x\in(V')^\perp\setminus U',\ t\in\mathbb F_2^m}
       \bigl(\operatorname{wt}(x+\sum_i t_i r_i)+2\operatorname{wt}(t)\bigr),\\
d_Z^{\rm old}
 &=\min_{z\in(U')^\perp\setminus V'}
       \bigl(\operatorname{wt}(z)+\operatorname{wt}(Rz)\bigr).
\end{split} \tag{15}
\]

**Proof.** An old X cycle has equal pair bits ((t,t)) by the pair Z
stabilizers. Pairing with the lifted (v\in V') says exactly that
(x=x_K+\sum_i t_ir_i\in(V')^\perp). Adding distinguished X stabilizers
removes these pair bits and gives ((x,0,0)), so the old class is trivial
exactly when (x\in U'). Its original representative has the first weight
in (15). An old Z cycle has retained part (z\in(U')^\perp) and pair bits
((\alpha,\beta)) with (alpha+\beta=Rz). Its class is trivial exactly
when (z\in V'), by (14). For each pair, adding its Z stabilizer allows
minimum pair weight zero for even parity and one for odd parity. This proves
the second minimum, including nontriviality of all representatives used. ∎

For the documented six-pair deletion of the actual ancestor, (14) is the
row-space recognition statement recorded in
`data/lifting-566-investigation/README.md`. Its (r_i), in final indices, are

\[
\begin{array}{c|rrrrrr}
0&221&224&257&505&522&538\\
1&222&225&258&506&523&539\\
2&223&226&259&507&524&540\\
3&224&227&260&508&525&541\\
4&225&228&261&509&526&542\\
5&226&229&262&510&527&543
\end{array} \tag{16}
\]

The proof of (15) is independent of that finite recognition record. When
transported using (14), it gives
\[
d_X^{566}\ge d_X^{578},\qquad
d_Z^{578}-6\le d_Z^{566}\le d_Z^{578}. \tag{17}
\]
Thus even a future analytic ancestor lower bound of twenty would transfer
only fourteen on the Z side without a further argument. The exact missing
inequality is, for **every** nontrivial final Z cycle,
\[
\operatorname{wt}(z)+\operatorname{wt}(Rz)\ge20+\operatorname{wt}(Rz),
\tag{18}
\]
or a structural argument with the same consequence. Testing (Rz) on a
chosen logical basis is insufficient because it need not be constant on a
logical coset. Merely knowing the left side is at least twenty omits the
right-side defect. Equation (18) is an obligation, not a proved estimate.

**Concrete counterexample with a six-site fan.** Take six retained qubits,
(U'=0), and (V') the even-weight space generated by
(e_1+e_2,\ldots,e_5+e_6). Use one pair and (r=(1,1,1,1,1,1)).
The final code has (k=1,d_X=6,d_Z=1). The old code (14) has eight qubits,
one X generator ((r,1,1)), and the five even-weight Z generators plus the
pair Z generator. It has (k=1). Formula (15) gives
\[
d_X^{\rm old}=\min(6,2)=2,\qquad
d_Z^{\rm old}=\min_{\operatorname{wt}(z)\text{ odd}}
                  (\operatorname{wt}(z)+1)=2.
\]
Paired deletion changes full distance from two to one. This has exactly the
six-retained-site pivot shape occurring in (16). It refutes generic distance
preservation for that shape, though it does not refute the particular target
distance claim. No enumeration is involved.

The additive constant six in the Z estimate (17) is also sharp under the
abstract hypotheses (14). Keep this same final repetition code and use six
pairs with every (r_i=r). For every nontrivial Z cycle, (Rz) is the
all-ones vector of length six. Hence (15) gives (d_Z^{\rm old}=1+6=7)
and (d_Z^{\rm final}=1). The actual supports (16) are distinct, so this
sharpness example does not identify their loss; it proves that improving
(17) needs information beyond the number and size of the removed fans.

## Blocked route: no progress credit for relative exactness below twenty

**CONJECTURE / BLOCKED — RE20-X and RE20-Z.** The relative-exactness
statements below are equivalent to the desired sector lower bounds. They
are not a smaller remaining lemma, not evidence of proximity to twenty,
and receive no progress credit. Likewise (18) cancels to
wt(z) >= 20 and is a tautological restatement, not a descent mechanism.

For 722 the exact finite chain maps are already (10):
\[
\partial_X=P[\,g\ f\,],\qquad
\partial_Z=Q[\,\bar f\ \bar g\,]. \tag{19}
\]
The stabilization maps are the truncated translates in (10). Therefore a
blocked assertion RE20-X is the following *weight-controlled relative exactness*
statement: for every pair supported on the 19-by-19 square with weight
less than twenty and (P(ga+fb)=0), produce coefficients of the allowed
X translates whose truncated sum is ((a,b)); prove the dual assertion
with (Q) and Z translates. Proposition 4 proves precisely this assertion
through weight two. Proposition 3 supplies its interior part at all weights.
Its boundary part remains unproved; this reduction alone does not reduce the
distance problem.

Equations (3)-(4) reduce boundary charge transport to multiplication by (x)
and (s=x^{-2}+x+x^2) in an eight-dimensional algebra. A successful proof
must connect these charge states to physical strip weights, and prove that
a nontrivial relative class cannot disappear at a single allowed boundary
or corner. The counterexample in Proposition 5 shows why that last step
cannot be inferred from bulk exactness. Abstract module transformations
mix physical coordinates, so a hypergraph-product distance formula cannot
be imported without a weight-preserving identification.

For 566, (5)-(8) give the corresponding bulk charge and exactness input for
the correct ancestor pair. One must identify the ancestor's actual boundary
submodules and then prove a strip-weight inequality that includes the six
defects in (16), or work directly with the final punctured complex.
The counterexample after (18) rules out assuming that these defects are free.
The dimensions eight and eighteen are concrete algebraic results; neither
is a surrogate for this missing weight inequality.

## PROPOSITION 7: a cut-charge invariant and an actual strip inequality

**Named gap: independent review/formalization pending.** This is a different
mechanism from RE20: it charges occupied physical rows to an algebraically
conserved boundary value. It proves a lower bound of nine conditional on
nonzero charge. Proposition 8 below proves that every nontrivial logical
has nonzero charge, removing that condition. It does not prove twenty.

For 722, put \(C=R/(f,g)\) and \(t=y+y^2\). Write an X cycle as
\[
a=\sum_{i=0}^{18}x^i a_i(y),\qquad
b=\sum_{i=0}^{18}x^i b_i(y),\qquad S=ga+fb.
\]
By the literal check ranges (10), all coefficients of \(S\) at
\(x^2,\ldots,x^{18}\) vanish. Thus \(S=S_{\rm lo}+S_{\rm hi}\), where
the low part occupies rows 0,1 and the high part rows 19,20. Define
\[
c_X(a,b)=[S_{\rm lo}]\in C. \tag{20}
\]
For every cut \(2\le k\le19\), define
\[
F_k=x^k(t a_{k-2}+b_{k-2}+b_{k-1})
       +x^{k+1}(t a_{k-1}+b_{k-1}). \tag{21}
\]
Then
\[
[F_k]=c_X(a,b)\quad(2\le k\le19). \tag{22}
\]

**Proof.** Truncate the physical operator to rows \(i<k\), denoting it
\((a^{<k},b^{<k})\). Since \(g=1+x^2t\) and \(f=y^2+x+x^2\), direct
multiplication gives
\[
ga^{<k}+fb^{<k}=S_{\rm lo}+F_k.
\]
Below row \(k\), it agrees with the full syndrome, whose interior rows
vanish. Its only terms above the cut are exactly (21). The left side lies
in the ideal \((f,g)\), proving (22).

The value \(c_X\) vanishes on every allowed X stabilizer in (10).
A fully supported generator has full syndrome zero. A generator truncated
at the top has physical rows at most 1 and hence syndrome rows at most 3;
it is a finite cycle, so its full syndrome is just its low part, which
belongs to \((f,g)\). A generator truncated at the bottom has no low
syndrome. These exhaust the generators; linearity proves the assertion.
Thus (20) is a well-defined linear invariant of X logical classes. ∎

**PROPOSITION — strip lower bound, same named review gap.** Put
\(w_i=\operatorname{wt}(a_i)+\operatorname{wt}(b_i)\) and
\(W=\sum_{i=0}^{18}w_i\). If \(c_X(a,b)\ne0\), then
\[
w_i+w_{i+1}\ge1\quad(0\le i\le17),\qquad
2W-w_0-w_{18}\ge18,
\]
and therefore
\[
W\ge 9+\left\lceil\frac{w_0+w_{18}}2\right\rceil\ge9. \tag{23}
\]
Indeed, if the two rows at a cut are empty, (21) vanishes, contradicting
(22). Summing the eighteen adjacent-band inequalities counts each interior
row twice and each outer row once. This proves (23) directly in physical
Hamming weight. It does not require a basis or a search in \(C\).

There is a dual invariant with the same inequality for Z cycles and column
weights. Explicitly set \(J(h)=x^{18}y^{18}h(x^{-1},y^{-1})\) and replace a
Z operator \((a,b)\) by \((a',b')=(J(b),J(a))\). Then
\(ga'+fb'=x^{18}y^{18}\overline{\bar f a+\bar g b}\) has zero
coefficients at \(y^2,\ldots,y^{18}\). Define \(c_Z\) as the class in \(C\)
of its \(y\)-degree 0,1 part. Truncate at a column cut. Both \(f,g\) have
\(y\)-range two, so the outgoing tail depends only on the last two columns.
The same ideal identity proves conservation. The reflected Z stabilizers
are truncations of \((f,g)\), fully supported in rows and possibly truncated
at column ends; the preceding low/high argument makes their charge zero.
Thus (23) holds with column weights for every Z cycle with \(c_Z\ne0\).

## FALSE: nonzero charge forces a qubit in every row or on each outer edge

The following counterexample uses the literal 722 code, not an altered
boundary. Its derivation has **PROPOSITION** status, with independent
review/formalization pending. Let
\[
a=x\sum_{m=0}^{8}x^{2m}t^m,\qquad b=0,\qquad t=y+y^2. \tag{24}
\]
Every coefficient fits the board: the row is \(1+2m\le17\) and the column
degree is at most \(2m\le16\). Telescoping gives
\[
ga=x+x^{19}t^9. \tag{25}
\]
Thus (24) is a finite X cycle, with charge \([x]\ne0\); \(x\) is a unit
in the nonzero quotient (4). By Proposition 7 it is a nontrivial X logical.
It has no qubits in any even row, including both outer rows 0 and 18.
Nevertheless the same nonzero charge crosses every cut (22).

Its weight is exactly 29. Since
\(t^m=y^m(1+y)^m\), binary factorization of \((1+y)^m\) gives
\(\operatorname{wt}(t^m)=2^{\operatorname{popcount}(m)}\).
The sum for \(0\le m<8\) is \((1+2)^3=27\), and the \(m=8\) term adds two.
This also exhibits why the two-row bandwidth in (23) is necessary.
It refutes an invariant forcing one qubit in each of the nineteen rows,
and refutes a positive cost for qubits specifically on the two outer edges.
It does not refute a stronger bound obtained by controlling cancellation
inside each two-row band.

## PROPOSITION 8: charge completeness and unconditional sector bounds of nine

**Named gap: independent review/formalization pending.** The previously
unproved CC-X and CC-Z assertions are established by the argument below,
using the boundary-image mechanism proposed by the user. The proof uses no
weight assumption. In particular it is not RE20 under another name.
The rank and bulk arguments in geometry.md, Lemmas 1–3, and
analytical/planar722/DRAFT.tex were read and checked; the needed arguments
are reproduced here to make the dependency explicit. Their independent
referee reviews remain outstanding.

### 8.1 A second presentation of the same charge algebra

Put
\[
t=y+y^2,\quad B=1+y^2t=1+y^3+y^4,\quad
r(y)=B^2+t=1+y+y^2+y^6+y^8.
\]
There is an isomorphism
\[
C=R/(f,g)\ \cong\ A=\mathbb F_2[y]/(r),\qquad
x\longmapsto t^{-1}+y^2=\frac B t. \tag{26}
\]
All inverses in this formula exist, and
\[
t^{-1}=1+y^4t=1+y^5+y^6,\qquad
x=1+y^2+y^5+y^6 \quad\text{in }A. \tag{27}
\]

**Proof of the presentation, in both directions.** The identity
\(r=1+t+y^4t^2\) proves the formula for \(t^{-1}\). Also \(r(0)=1\)
makes \(y\) a unit (explicitly \(y^{-1}=1+y+y^5+y^7\)).
For \(X=B/t\) in \(A\), the relation \(B^2=t\) implies
\(X^2=t^{-1}\). Thus \(X\) is a unit,
\[
X+X^2+y^2=0,\qquad1+X^2(y+y^2)=0.
\]
These are exactly \(f(X,y)=g(X,y)=0\); substitution therefore defines
a map from the Laurent quotient \(C\) to \(A\).

Conversely, in \(C\), \(g=0\) says \(x^2t=1\), hence \(t^{-1}=x^2\).
The equation \(f=0\) says \(x=t^{-1}+y^2=B/t\). Squaring \(xt=B\)
gives \(B^2=x^2t^2=t\), so \(r(y)=0\) in \(C\).
This defines \(A\to C\). The two maps fix \(y\) and send \(x\) back to
itself, hence are inverse. The monic degree-eight polynomial \(r\)
gives the basis \(1,y,\ldots,y^7\). No irreducibility assumption is used. ∎

### 8.2 Analytic dimensions, including the full-syndrome kernel

Let \(V\) be the 722-dimensional physical space, let \(K_X=\ker H_Z\),
and let \(S_X=\operatorname{row}H_X\). Both check sets in (10) are
independent, so
\[
\dim K_X=\dim K_Z=365,\qquad
\dim S_X=\dim S_Z=357. \tag{28}
\]
Here is the recurrence verification, independent of any matrix-rank output.
For X anchors write \(h=\sum_{i=-2}^{18}x^i h_i(y)\), with
\(\deg h_i\le16\). A vanishing combination \(T(fh,gh)=0\) gives
\[
h_{i-2}+h_{i-1}+y^2h_i=0,\qquad h_i=t h_{i-2}
\quad(0\le i\le18).
\]
Thus \(h_{i-1}=B h_{i-2}\). The cases \(i=0,1\) give both
\(h_0=B^2h_{-2}\) and \(h_0=t h_{-2}\), whence
\(r h_{-2}=0\) in the polynomial domain \(\mathbb F_2[y]\).
As \(r\ne0\), all \(h_i=0\) by these recurrences.

Reflecting the square and exchanging blocks sends a Z combination to
\(T(fh,gh)\), with \(h=\sum_{j=-2}^{18}y^j h_j(x)\) and
\(\deg h_j\le16\). Put \(a=x+x^2\) and \(b=1+x^2a\). Vanishing gives
\[
h_{j-2}=a h_j,\qquad x^2h_{j-1}=b h_j.
\]
For \(j=0,1\), these imply
\[
(b^2+x^4a)h_1=(1+x^5+x^8)h_1=0.
\]
Hence \(h_1=h_0=h_{-1}=h_{-2}=0\); the first recurrence and \(a\ne0\)
force every other \(h_j=0\). This proves both ranks in (28).
Commutation was established from the actual translate supports in (10);
thus \(S_X\subseteq K_X\), and similarly for Z.

For the full X syndrome \(\sigma(a,b)=ga+fb\), Proposition 3 gives
\(\ker\sigma=R(f,g)\). If a nonzero pair \((fh,gh)\) is supported on
the physical square, the extreme exponents of \(fh\) force
\(\operatorname{supp}h\subseteq[0,16]^2\). Conversely every such \(h\)
gives a pair in the square, and the map \(h\mapsto(fh,gh)\) is injective
because \(R\) is a domain. Therefore
\[
\dim(\ker\sigma\cap V)=17^2=289. \tag{29}
\]
This kernel is contained in \(K_X\), and consists of fully supported
X stabilizer combinations. Rank-nullity on \(K_X\), not on an ambient
unrestricted polynomial space, now gives
\[
D_X:=\sigma(K_X),\qquad \dim D_X=365-289=76. \tag{30}
\]
The reflected Z problem has the same square, the same map \(ga+fb\),
and the same 289-dimensional kernel; hence its image also has dimension 76.

### 8.3 Boundary image equals the kernel of total residue

For X cycles the exact full-syndrome support ranges are
\[
E_{\rm lo}=\langle x^iy^j:i=0,1,\ 0\le j\le20\rangle,\qquad
E_{\rm hi}=\langle x^iy^j:i=19,20,\ 0\le j\le20\rangle. \tag{31}
\]
Each is a 42-dimensional space of formal coefficient vectors. The direct
sum \(E=E_{\rm lo}\oplus E_{\rm hi}\) has dimension 84. These ranges follow
because physical exponents lie in \([0,18]^2\), both polynomial supports
lie in \([0,2]^2\), and the retained Z checks test exactly
\([2,18]\times[0,20]\). No untested intermediate coefficients are omitted.

Define the linear residue map
\[
\phi:E\longrightarrow C,\qquad \phi(\ell,h)=[\ell+h].
\]
The restriction to \(E_{\rm lo}\) is onto: its eight vectors
\(1,y,\ldots,y^7\), all at row zero and within (31), map to the basis (26).
The restriction to \(E_{\rm hi}\) is also onto: its vectors
\(x^{19},x^{19}y,\ldots,x^{19}y^7\), all within (31), map to a basis
because multiplication by the unit \(x^{19}\) is invertible on \(C\).
In particular
\[
\operatorname{rank}\phi=8,\qquad \dim\ker\phi=84-8=76.
\]
Every full syndrome lies in \((f,g)\), so \(D_X\subseteq\ker\phi\).
Together with (30), this proves the actual subspace equality
\[
D_X=\ker\phi. \tag{32}
\]
The dimension count is legitimate here because both are subspaces of the
same explicitly specified finite coefficient space \(E\).

Given any \(c\in C\), choose \(\ell\in E_{\rm lo}\) and
\(h\in E_{\rm hi}\) with \([\ell]=[h]=c\). Then
\(\phi(\ell,h)=c+c=0\). By (32) there is a physical X cycle whose full
syndrome is \(\ell+h\), and its low charge (20) is \(c\).
This proves surjectivity of \(c_X:K_X\to C\), not merely equality of
the prospective source and target dimensions.

Proposition 7 proves \(S_X\subseteq\ker c_X\). Surjectivity and (28) give
\(\dim\ker c_X=365-8=357=\dim S_X\), hence
\[
\ker c_X=S_X,\qquad K_X/S_X\xrightarrow{\ \cong\ }C. \tag{33}
\]

### 8.4 Dual completeness: correct reflected ranges and basis

For a Z operator use exactly the reflection/block exchange
\((a',b')=(J(b),J(a))\) from Proposition 7. The original X check anchors
\([-2,18]\times[0,16]\) become the tested syndrome rectangle
\([0,20]\times[2,18]\), since
\[
ga'+fb'=x^{18}y^{18}\overline{\bar f a+\bar g b}.
\]
The reflected full syndrome is supported in \([0,20]^2\).
Consequently the two boundary spaces are now
\[
\widetilde E_{\rm lo}
 =\langle x^iy^j:0\le i\le20,\ j=0,1\rangle,\qquad
\widetilde E_{\rm hi}
 =\langle x^iy^j:0\le i\le20,\ j=19,20\rangle. \tag{34}
\]
They again have dimensions 42 and 42. Use the original presentation (4),
with basis \(1,x,\ldots,x^7\), to prove low-space surjectivity.
The high-space vectors \(y^{19},y^{19}x,\ldots,y^{19}x^7\) map to a basis
because \(y\) is a unit. Thus the dual total-residue map has rank eight.
The reflected image has dimension 76 by (28)-(30), is contained in its
kernel, and equals it. The same low/high lifting argument makes \(c_Z\)
onto. Its kernel contains the reflected Z stabilizers by Proposition 7
and has their dimension 357. Reflection is a coordinate permutation,
so returning to the original code gives
\[
\ker c_Z=S_Z,\qquad K_Z/S_Z\xrightarrow{\ \cong\ }C. \tag{35}
\]
This argument does not assert that reflection alone is a code symmetry.

### 8.5 Distance consequence

Every nontrivial X or Z logical now has nonzero corresponding charge,
by (33) and (35). Applying (23) to every representative proves
\[
\boxed{d_X(722)\ge9,\qquad d_Z(722)\ge9,\qquad d_{\rm Pauli}(722)\ge9.}
\tag{36}
\]
For the last inequality, a nontrivial CSS Pauli class has a nontrivial X
or Z component, whose weight is at most the union support of the Pauli.
No claim about 566 follows from (36).

## Exact remaining crux after charge completeness

**CONJECTURE / BLOCKED — amplification from nine to twenty.**
CC-X and CC-Z are now proved at PROPOSITION grade; (23) establishes nine.
The counterexample (24) rules out the proposed one-qubit-per-row argument
and an unconditional outer-edge surcharge. A stronger result must control
the cost of the forced recurrence
\[
a_i=t a_{i-2}+b_{i-1}+b_{i-2}+y^2b_i,\qquad2\le i\le18,
\]
including cancellations introduced by the B block. No such cost inequality
is proved here, and none is claimed close. This note does not assign
progress credit to replacing that missing inequality by RE20.

For 566, the strip argument cannot be imported through deletion: the
polynomial row action is broken and the six parity defects in (16) remain.
The blanket implications “bulk exactness gives target distance twenty” and
“a six-site paired removal preserves distance” are **FALSE**, as shown by
Propositions 5 and 6. Those counterexample proofs remain **PROPOSITION**.
No new unconditional 566 distance lower bound is asserted.

## Symbolic script and validation

The exact determinant manipulation used above is persisted in
[algebra_check.py](algebra_check.py): the six-by-six Sylvester determinant
and independent three-by-three multiplication determinant, using carryless
polynomial arithmetic over \(\mathbb F_2\). The script also checks the
telescoping identity (25), the polynomial \(r\), its explicit inverses, and
the defining substitutions in (26)-(27). All checks passed, as did Ruff
lint and format checks, using the installed Python 3.13 environment.
It has no code-input dependency, enumerates no
physical supports or logicals, and supplies no numerical distance certificate.
Run with Python 3.13 on analytical/notes/algebra_check.py.

Validation performed: direct reading of definitions; literal reconstruction
of the two 722 ordered row lists using (10); symbolic expansion of the
six-by-six determinant (7), independently checked against the three-by-three
matrix of multiplication by (g) modulo (f); and hand proofs above. No existing lower-bound
certificate was used as a premise, no distance search was run, and no file
other than this note and its authorized symbolic script was written.
All new propositions remain unrefereed. In particular the new charge
isomorphisms and bound nine await independent review/formalization;
independent replay of literal input recognition is also outstanding.
