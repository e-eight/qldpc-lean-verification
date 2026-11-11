# Physical strip deficits for rectangular 722

2026-11-11. **All proved claims below are PROPOSITION, with the named gap
independent review/formalization pending.** No claim is a refereed THEOREM.
Distance twenty remains CONJECTURE. This note first proves a physical X-sector
bound of thirteen, then derives separate Z local equations and improves both
sector bounds to fourteen, fifteen, and (in later research) seventeen.
Interpretation as bounds on nontrivial logical classes uses the proposed
charge results. Propositions
5–8 establish fourteen; Propositions 9–10 establish fifteen using the user's
four-singleton obstruction and its separately derived Z counterpart.
Propositions 13–14 establish a new run-exit inequality and seventeen.
None of these arguments assumes a sector symmetry.

Read: root `AGENTS.md`, `analytical/planar722/RESEARCH.typ`, and
`analytical/notes/algebra.md`, particularly Propositions 7–8. The initial
research changed only this note. At the user's subsequent request, the
self-contained local-fifteen proof was written in
`analytical/strip-deficits/DRAFT.typ`; subsequent research remains here.
No Lean, finite-state enumeration, LP, support search, or distance
search was run. The calculations below are polynomial identities and counting
arguments on arbitrary row supports.

**Frozen review draft.** `analytical/strip-deficits/DRAFT.typ` is frozen for
document-only referees at source SHA-256
`85c5b40dfe2853e4c7f7d68b37d825a2eb8694425335b274b2b5a7d4fcbab779`.
It compiled successfully with Typst 0.15.1 to the four-page
`/tmp/strip-deficits-draft.pdf`, whose SHA-256 is
`674e879d8a76d206486453a504eddfef3d743ed0e4ef88b4a37b0d725b847d63`.
The source states the local bound first and proves it from either explicit
recurrence and adjacent nonemptiness, with no charge or model dependencies.
Compilation and visual inspection are presentation checks, not mathematical
verification. The draft is not to change unless referee objections require
correction. Propositions 11–14 below are later research, outside that draft.

**Separate frozen local17 review packet.**
`analytical/strip-runs/DRAFT.typ` is now frozen for three document-only
referees at SHA-256
`03ecc01626209d6745cadf6336d393b6da77eea31284c09900e8f5917b896419`.
Typst 0.15.1 compiled it to the visually checked six-page
`/tmp/strip-runs-draft.pdf`, SHA-256
`e0cc6035e2c7d97e04cdee8ede0e55a4a47bcff481ced43b6c84ff8530281b85`.
Its main statement is local seventeen, followed by all polynomial and
counting tools needed for its self-contained proof. The exact generic
formalization interfaces are in `analytical/strip-runs/HANDOFF.md`.
Neither frozen source is changed by the research below. Propositions 15–29
are ongoing work toward twenty, outside both review packets.

## Definitions and dependency boundary

Work over the polynomial ring \(\mathbb F_2[y]\), with physical rows
\((a_i,b_i)\), \(0\le i\le18\). Each polynomial has degree at most 18;
zero polynomials are allowed. There is **no reduction modulo a polynomial in
\(y\)** and no truncation of the following identities. Put

\[
t=y+y^2,\qquad
a_i=t a_{i-2}+b_{i-1}+b_{i-2}+y^2b_i\quad(2\le i\le18). \tag{1}
\]

These are exactly the X-cycle equations for the literal rectangle in
`algebra.md`. The physical weight is

\[
w_i=\operatorname{wt}(a_i)+\operatorname{wt}(b_i),\qquad
W=\sum_{i=0}^{18}w_i. \tag{2}
\]

An empty row has \(w_i=0\); a singleton has \(w_i=1\); a heavy row has
\(w_i\ge2\). The global counting proposition uses the explicit hypothesis

\[
w_i+w_{i+1}\ge1\qquad(0\le i\le17). \tag{3}
\]

By the conserved-cut identity in `algebra.md`, Proposition 7, nonzero X
charge implies (3). Its Proposition 8 identifies zero charge with the X
stabilizer space. Those results retain their own independent-review gap;
they are dependencies, not reproved or assumed formally verified here.
The local propositions below require only (1), not charge completeness.

## PROPOSITION 1: exact signed-overlap identity

For a polynomial \(p\), let \(\rho(p)\) be the number of maximal consecutive
runs of exponents in its support, with \(\rho(0)=0\). Then

\[
\operatorname{wt}(tp)=2\rho(p). \tag{4}
\]

For \(2\le i\le18\), define

\[
\begin{split}
d_i&=b_{i-1}+b_{i-2},\\
I_i&=|\operatorname{supp}(t a_{i-2})\cap\operatorname{supp}(d_i)|,\\
O_i&=|\operatorname{supp}(a_i)\cap\operatorname{supp}(y^2b_i)|.
\end{split}
\]

There is an exact identity in ordinary integers:

\[
\boxed{w_i=2\rho(a_{i-2})+\operatorname{wt}(d_i)-2I_i+2O_i.} \tag{5}
\]

**Proof.** The support of \((1+y)p\) consists of the two endpoints of each
run: a run from \(u\) to \(v\) contributes exponents \(u,v+1\). Different
runs give distinct endpoints. Multiplication by \(y\) preserves weight,
proving (4). For binary polynomials,
\(\operatorname{wt}(h+k)=\operatorname{wt}(h)+\operatorname{wt}(k)
-2|\operatorname{supp}(h)\cap\operatorname{supp}(k)|\).
Apply this to both sides of
\(a_i+y^2b_i=t a_{i-2}+d_i\), then rearrange. ∎

Thus overlap within the current A and shifted B slices has a **positive**
physical cost \(2O_i\); it must not be mistaken for free cancellation.
Incoming forcing overlap \(I_i\) has the negative sign. Summing (5) alone
does not bound that negative contribution. The following zero-row arguments
remove it at particular locations.

## PROPOSITION 2: a row between zeros is A-only and forces a branch

Suppose \(1\le r\le17\) and \(w_{r-1}=w_{r+1}=0\). Then
\(b_r=0\). If also \(r\le16\), then

\[
a_{r+2}+y^2b_{r+2}=t a_r,
\qquad
\boxed{w_{r+2}=2\rho(a_r)+2O_{r+2}.} \tag{6}
\]

In particular, a nonempty row between zeros forces \(w_{r+2}\ge2\),
and this continuation weight is even. A singleton between zeros must be
\((a_r,b_r)=(y^j,0)\), and its continuation has weight at least two.

**Proof.** Equation (1) at \(r+1\) reduces to \(0=b_r\).
At \(r+2\), its two unshifted B terms vanish, proving the first identity
in (6). Equation (5) then gives the second. A nonzero polynomial has at
least one run. The degree restriction remains in force: impossible
continuations near a column edge are excluded, rather than truncated. ∎

The upper endpoint matters. For \(r=17\), A-only still follows, but there
is no tested equation at row 19 and no claimed branch cost there.
For a general non-singleton row, (6) charges runs, not its coefficient
count: \(p=1+y+\cdots+y^m\) has \(\operatorname{wt}(tp)=2\).
Any claim that every A coefficient produces two surviving coefficients is
**FALSE**, even before B forcing is introduced.

## PROPOSITION 3: two occupied rows between zeros cost at least four

Suppose \(0\le k\le15\), \(w_k=w_{k+3}=0\), and the two intermediate
rows are not both empty. Then

\[
\boxed{w_{k+1}+w_{k+2}\ge4.} \tag{7}
\]

**Proof.** Write
\(p=a_{k+1},q=b_{k+1},u=a_{k+2},v=b_{k+2}\).
The equations at \(k+2,k+3\) are exactly

\[
u=q+y^2v,\qquad tp+q+v=0. \tag{8}
\]

Evaluating at \(y=1\) gives \(q(1)=v(1)\) and \(u(1)=0\).
If \(u\ne0\), its coefficient weight is even and at least two.
Moreover \(\operatorname{wt}(p)+\operatorname{wt}(q)+\operatorname{wt}(v)
\ge2\): weight zero contradicts \(u\ne0\), while weight one leaves a
single nonzero term in \(tp+q+v\), impossible in the polynomial domain.
This proves (7) in this case.

If \(u=0\), (8) gives \(q=y^2v\) and
\(y(1+y)p=(1+y)^2v\). Cancel the nonzero factor \(1+y\), obtaining
\(yp=(1+y)v\). Evaluation at zero shows \(y\mid v\). Write \(v=yh\);
then

\[
p=(1+y)h,\qquad q=y^3h,\qquad u=0,\qquad v=yh.
\]

The nonempty hypothesis implies \(h\ne0\), so the total weight is
\(2\rho(h)+2\operatorname{wt}(h)\ge4\). ∎

The local constant four is attained by \(h=1\): the two rows are
\((1+y,y^3)\) and \((0,y)\). They satisfy exactly the two equations (8)
between empty endpoint rows and fit the column range. This is a local
sharpness example, **not** a claim that extending all other rows by zero
gives a full cycle. In particular, the pattern zero–singleton–singleton–zero
is impossible.

## PROPOSITION 4: global physical deficit inequality and bound thirteen

Assume (1) and (3). Let \(z\) be the number of empty rows and define the
total excess over one qubit per occupied row by

\[
E=\sum_{i:w_i>0}(w_i-1)=W-(19-z). \tag{9}
\]

Then

\[
\boxed{9E\ge8z-48,\qquad W\ge13.} \tag{10}
\]

**Proof.** No two empty rows are adjacent, so \(z\le10\).
If \(z\le1\), then \(W\ge18\) and the deficit inequality is immediate.
Otherwise list the empty rows as \(q_1<\cdots<q_z\). Let \(G\) count
successive gaps of length two, and \(H\) successive gaps of length three.
All other gaps have length at least four. Since \(q_z-q_1\le18\),

\[
18\ge2G+3H+4(z-1-G-H),\qquad
2G+H\ge4z-22. \tag{11}
\]

For a length-two gap, its unique middle row \(r\) is occupied.
If it is heavy, charge this gap to that heavy row. If it is a singleton
and \(r\le16\), Proposition 2 supplies a heavy row at \(r+2\); charge
the gap there. Different middle rows have different targets \(r+2\).
A heavy row can receive at most one charge as a middle row and one as a
target. There is at most one uncharged exception, namely \(r=17\).
The number of heavy rows is at most \(E\). Therefore

\[
G\le2E+1. \tag{12}
\]

For a length-three gap, its two intermediate rows are both occupied by
(3). Proposition 3 gives weight at least four, hence excess at least two
within that gap. Interiors of distinct gaps are disjoint, so

\[
2H\le E. \tag{13}
\]

There is no assertion that the charges in (12) and (13) use disjoint
excess. Combining the two valid bounds with their stated multiplicities
gives precisely

\[
4z-22\le2G+H\le2(2E+1)+E/2,
\]

which is \(9E\ge8z-48\). Finally (9) gives

\[
9W=171-9z+9E\ge123-z\ge113.
\]

Since physical weight is an integer, \(W\ge\lceil113/9\rceil=13\). ∎

This argument uses arbitrary polynomial slices, including mixed A/B slices.
It counts gaps and excess weight, without listing row states or solving a
finite optimization problem. It is deliberately conservative about repeated
use of a heavy row.

## Initial X logical consequence

**PROPOSITION — same named review/formalization gap.** Using the charge
conservation and completeness propositions of `algebra.md`, every nontrivial
X logical of the explicit rectangular 722 model has physical weight at
least thirteen:

\[
d_X\ge13. \tag{14}
\]

Indeed a nontrivial class has nonzero charge, hence (3), so Proposition 4
applies. Adding any allowed truncated X stabilizer preserves both the cycle
equations and the charge. Thus the argument applies to **every** physical
representative of that class. There is no weight-preserving normal-form
assumption, no replacement of physical weight by charge weight, and no
need to select a minimum-weight representative first.

## Reflected Z definitions: a different recurrence

For an original Z operator \((\alpha,\beta)\), set
\(J(h)=x^{18}y^{18}h(x^{-1},y^{-1})\) and
\((a,b)=(J(\beta),J(\alpha))\). Reflection and block exchange preserve
physical coefficient weight. Expand **in columns**:

\[
a=\sum_{j=0}^{18}y^j a_j(x),\qquad
b=\sum_{j=0}^{18}y^j b_j(x),\qquad s=x+x^2.
\]

Here \(a_j,b_j\in\mathbb F_2[x]\), each of degree at most 18. The reflected
syndrome is \(ga+fb\), whose tested columns are 2 through 18. Its coefficient
at \(y^j\) is
\(a_j+x^2a_{j-1}+x^2a_{j-2}+s b_j+b_{j-2}\). Thus the exact equations are

\[
\boxed{s b_j=a_j+x^2a_{j-1}+x^2a_{j-2}+b_{j-2}}
\qquad(2\le j\le18). \tag{15}
\]

All possible x exponents of this syndrome are 0 through 20, exactly the
tested range; (15) is an identity of entire polynomials, not a quotient
identity or a truncated multiplication. In the Z discussion, \(w_j\),
\(W,z,E\) refer to these reflected column slices. Nonzero Z charge implies
\(w_j+w_{j+1}\ge1\) by `algebra.md`, Proposition 7. Its completeness result
is the same logical-class dependency as before. No symmetry identifying
(15) with (1) is asserted.

## PROPOSITION 5: Z signed overlap and backward branching between zeros

For \(2\le j\le18\), put

\[
\begin{split}
D_j&=a_j+x^2a_{j-1},\\
I^Z_j&=|\operatorname{supp}(s b_j)\cap\operatorname{supp}(D_j)|,\\
O^Z_j&=|\operatorname{supp}(x^2a_{j-2})\cap\operatorname{supp}(b_{j-2})|.
\end{split}
\]

The exact physical identity is

\[
\boxed{w_{j-2}=2\rho(b_j)+\operatorname{wt}(D_j)-2I^Z_j+2O^Z_j.}
\tag{16}
\]

If \(1\le r\le17\) and columns \(r-1,r+1\) are empty, then \(a_r=0\).
If also \(r\ge2\), then

\[
x^2a_{r-2}+b_{r-2}=s b_r,\qquad
\boxed{w_{r-2}=2\rho(b_r)+2O^Z_r.} \tag{17}
\]

Thus a nonempty column between zeros is **B-only** and forces an even
weight of at least two **two columns earlier**. The exceptional middle
column is \(r=1\), where no equation at index 1 is tested.

**Proof.** Rearrange (15) as
\(x^2a_{j-2}+b_{j-2}=s b_j+D_j\). The binary support identity used in
Proposition 1 and \(\operatorname{wt}(s p)=2\rho(p)\) give (16).
Equation (15) at \(r+1\) reduces to \(0=x^2a_r\). The polynomial domain
gives \(a_r=0\). At \(r\), both terms in \(D_r\) vanish, yielding (17). ∎

**FALSE local forward analogue.** A singleton between zeros need not force
weight two at \(r+2\) from the local equations. For \(2\le r\le16\), take
the five consecutive slices

\[
(a_{r-2},b_{r-2})=(0,s),\quad(0,0),\quad(0,1),\quad(0,0),\quad(1,0).
\tag{18}
\]

The equations at \(r,r+1,r+2\) hold: respectively \(s=s\), \(0=0\),
and \(0=1+1\). The forward slice is a singleton, while the backward
slice has weight two. This is a counterexample to an implication from those
local equations, not a claim of an extendible full cycle.

## PROPOSITION 6: the Z two-occupied-column gap costs at least four

Let \(0\le k\le15\), with empty columns \(k,k+3\) and not both
intermediate columns empty. Then

\[
\boxed{w_{k+1}+w_{k+2}\ge4.} \tag{19}
\]

**Proof.** Write the intermediate slices as \((p,q),(u,v)\). Equations
(15) at \(k+2,k+3\) give, separately from the X calculation,

\[
s v=u+x^2p,\qquad q=x^2(u+p). \tag{20}
\]

At \(x=1\), the first identity gives \(u(1)=p(1)\), so \(q(1)=0\).
If \(q\ne0\), then \(\operatorname{wt}(q)\ge2\). Also
\(\operatorname{wt}(p)+\operatorname{wt}(u)+\operatorname{wt}(v)\ge2\):
weight zero forces \(q=0\), and weight one cannot satisfy the nonzero-term
identity \(s v+u+x^2p=0\). The total is at least four.

If \(q=0\), then \(u=p\), and the first equation becomes
\(x(1+x)v=(1+x)^2p\). Cancel \(1+x\): \(xv=(1+x)p\).
Evaluation at zero gives \(p=xh\), and consequently

\[
p=u=xh,\qquad q=0,\qquad v=(1+x)h.
\]

Here \(h\ne0\). The total weight is
\(2\operatorname{wt}(h)+2\rho(h)\ge4\), as required. ∎

Taking \(h=1\) attains this local bound, with slices \((x,0),(x,1+x)\).
This satisfies (20) and the degree cap, without asserting a full-cycle
extension. The two-occupied-gap result has the same numerical constant as
the X result, but different polynomial equations and a different extremizer.

## PROPOSITION 7: three singleton slices cannot lie between zeros

In **either** sector's respective recurrence, if \(0\le k\le14\), slices
\(k,k+4\) are empty, and all three intervening slices are occupied, then

\[
\boxed{w_{k+1}+w_{k+2}+w_{k+3}\ge4.} \tag{21}
\]

**X proof.** Suppose instead that the three slices \((p,q),(u,v),(h,l)\)
are all singletons. The equations at \(k+2,k+3,k+4\) are

\[
u=q+y^2v,\qquad h=t p+v+q+y^2l,\qquad 0=t u+l+v. \tag{22}
\]

If \(q=0\), the first equation forces \(u=y^2v\), impossible for the
singleton pair \((u,v)\): its two polynomials would either both vanish
or both be nonzero. Thus \(q\) is a monomial and \(p=0\).
If \(u\ne0\), then it is a monomial and \(v=0\); the last equation
forces \(l=t u\) of weight two, contradicting the singleton third slice.
Hence \(u=0\), \(v\) is a monomial, and the last equation gives \(l=v\).
The third slice is therefore B-only, so \(h=0\). The middle equation
now says \(q=(1+y^2)v\), of weight two, contradicting the monomial \(q\).
This proves (21) for X.

**Z proof.** With the same names for the three column slices, their equations
are instead

\[
s v=u+x^2p,\qquad
s l=h+x^2u+x^2p+q,\qquad
v=x^2(h+u). \tag{23}
\]

Again suppose all three slices are singletons. If \(v\ne0\), then \(v\)
is a monomial and \(u=0\). The first equation forces \(x^2p=s v\),
which has weight two, impossible for \(p\) in the first singleton slice.
Thus \(v=0\) and \(u\) is a monomial. The last equation gives \(h=u\),
so \(l=0\). The first gives \(x^2p=u\), forcing \(p\ne0\) and \(q=0\).
But the middle equation then reads
\(0=u+x^2u+u=x^2u\), a contradiction. ∎

These proofs use the algebraic consequences of total weight three; they do
not enumerate polynomial slices, coordinate supports, or transfer states.
The assertion is only the lower bound four, with no sharpness claim.

## PROPOSITION 8: sharper deficit counting gives fourteen in both sectors

In either sector assume its respective recurrence and adjacent-slice
nonemptiness. Define \(z,E\) as in (9), now for that sector's slices.
Then the following stronger inequalities hold:

\[
\boxed{5E\ge8z-48,\qquad4E\ge5z-26,\qquad W\ge14.} \tag{24}
\]

**Proof.** If \(z\le1\), both deficit inequalities have negative right
sides and \(W\ge18\). Otherwise list successive zero positions as before.
Let \(G,H,K\) count their gaps of lengths two, three, and four respectively.

There is a useful strengthening of (12):

\[
\boxed{G\le E+1.} \tag{25}
\]

Indeed **every** occupied middle slice in a length-two gap forces a heavy
slice, even when that middle slice is already heavy. For X use the target
\(r+2\) from Proposition 2; for Z use \(r-2\) from Proposition 5. In
each sector these targets are distinct for distinct middle indices. There
is at most one exception, \(r=17\) for X or \(r=1\) for Z. Charge each
nonexceptional gap to one unit of excess at its target. This proves (25)
without also charging heavy middle slices, eliminating the unnecessary
factor two in (12).

Gap interiors are disjoint. Propositions 3 and 6 require excess at least
two in each length-three gap. Proposition 7 requires excess at least one
in each length-four gap. Consequently

\[
\boxed{2H+K\le E.} \tag{26}
\]

Using (11), (25), and \(2H\le E\) gives
\(4z-22\le2G+H\le2E+2+E/2\), proving \(5E\ge8z-48\).
To use the new cancellation obstruction (21), count all remaining gaps
with their minimum length five:

\[
18\ge2G+3H+4K+5(z-1-G-H-K),
\qquad3G+2H+K\ge5z-23.
\]

Apply (25) and (26) separately, with their stated multiplicities:

\[
5z-23\le3G+2H+K\le3(E+1)+E=4E+3.
\]

This proves \(4E\ge5z-26\). Possible overlap between the excess used in
(25) and (26) is already allowed by the coefficient four; no disjointness
between those two budgets is assumed. Substitute \(E=W-19+z\) to get
\(4W\ge50+z\). Also \(E\ge0\) gives \(z\ge19-W\). Hence

\[
5W\ge69,\qquad W\ge\lceil69/5\rceil=14.
\]

This is a counting argument for arbitrary slices, with the additional
physical cancellation obstruction (21) as an essential premise. ∎

## PROPOSITION 9: a zero cannot border four singletons in the forcing direction

For X, if row \(k\) is empty, \(0\le k\le14\), and rows
\(k+1,\ldots,k+4\) are all occupied, then

\[
\sum_{i=k+1}^{k+4}w_i\ge5. \tag{27}
\]

For reflected Z, if column \(R\) is empty, \(4\le R\le18\), and columns
\(R-4,\ldots,R-1\) are all occupied, then

\[
\sum_{j=R-4}^{R-1}w_j\ge5. \tag{28}
\]

There is no hypothesis about a zero at the other end of either four-slice
interval. These are directional statements, proved from different equations.

**X proof.** This is the user's proposed cancellation argument, written
without division by a monomial. Suppose all four slices are singletons,
and name them \((p,q),(u,v),(h,l),(m,n)\) in increasing row order.
The equations at \(k+2,k+3,k+4\), all in the tested range, are

\[
u+y^2v=q,\qquad
h+y^2l=t p+v+q,\qquad
m+y^2n=t u+l+v. \tag{29}
\]

For any singleton pair, the sum of one block and a monomial shift of the
other is a single monomial: exactly one block is nonzero. Thus the first
equation forces \(q\) to be a monomial and \(p=0\).
If the second slice were B-only, then \(u=0\) and \(q=y^2v\); the
second equation would give \(h+y^2l=(1+y^2)v\), of weight two, impossible
for the singleton third slice. Therefore the second slice is A-only,
with \(u=q\) and \(v=0\).

The third-slice equation is now \(h+y^2l=q\). If that slice is A-only,
then \(h=q,l=0\), and the fourth equation becomes
\(m+y^2n=tq\), whose right side has weight two. If instead the third
slice is B-only, then \(h=0,q=y^2l\), and the fourth equation becomes

\[
m+y^2n=tq+l=(1+y^3+y^4)l,
\]

whose right side has weight three. Both contradict the fourth singleton.
The three exponents are distinct; there is no quotient reduction or boundary
truncation that could cancel them. This proves (27).

**Z proof from (15).** Name the four singleton slices in **decreasing**
column order: \((p,q)\) at \(R-1\), \((u,v)\) at \(R-2\),
\((h,l)\) at \(R-3\), and \((m,n)\) at \(R-4\).
The equations at \(R,R-1,R-2\), all between 2 and 18, give

\[
x^2u+v=x^2p,\qquad
x^2h+l=s q+p+x^2u,\qquad
x^2m+n=s v+u+x^2h. \tag{30}
\]

The first left side is a monomial because the second slice is a singleton.
Thus \(p\) is a monomial and \(q=0\): the nearest slice to the zero is
A-only. If the second slice were A-only, the first equation would give
\(u=p,v=0\), and the second would give
\(x^2h+l=(1+x^2)p\), of weight two, contradicting the third singleton.
Hence the second slice is B-only, with \(u=0,v=x^2p\).

The third-slice equation reduces to \(x^2h+l=p\). If that slice is
B-only, then \(h=0,l=p\), and the fourth equation becomes
\(x^2m+n=s x^2p\), of weight two. If the third slice is A-only, then
\(l=0,x^2h=p\), and the fourth equation becomes

\[
x^2m+n=s x^2p+p=(1+x^3+x^4)p,
\]

of weight three. Either contradicts the fourth singleton. This proves (28)
directly from the reflected Z recurrence. ∎

The proof uses singleton block exclusivity and distinct monomial shifts,
not enumeration of coordinates, polynomial slices, or transfer states.
Keeping divisions out of the argument also covers edge cases: a required
shift that cannot fit the polynomial degree range is already impossible,
not a new admissible cancellation.

**Length-five gap consequence.** Between successive zero slices at distance
five, all four interior slices are occupied. Apply (27) from the left zero
for X or (28) from the right zero for Z. The interior weight is at least
five, hence its excess over four occupied slices is at least one. The
endpoints fit the tested ranges: the X left endpoint is at most 13, and
the Z right endpoint is at least 5.

## PROPOSITION 10: the new gap cost gives fifteen in both sectors

Assume the sector's recurrence and adjacent-slice nonemptiness as before.
Then

\[
\boxed{6E\ge6z-28,\qquad6W\ge86,\qquad W\ge15.} \tag{31}
\]

**Proof.** For \(z\le1\), the first inequality follows from \(E\ge0\),
and \(W\ge18\) implies the other two. Otherwise retain the gap counts
\(G,H,K\) of lengths two, three, four, and let \(L\) count length-five
gaps. All other successive zero gaps have length at least six. Their
total span is at most 18, so

\[
\begin{split}
18&\ge2G+3H+4K+5L+6(z-1-G-H-K-L),\\
4G+3H+2K+L&\ge6z-24.
\end{split} \tag{32}
\]

By (25), \(G\le E+1\), with its same single directional boundary
exception. Disjoint gap interiors and Propositions 3, 6, 7, and 9 give

\[
2H+K+L\le E.
\]

In particular,
\(3H+2K+L\le2(2H+K+L)\le2E\), since
\(2(2H+K+L)-(3H+2K+L)=H+L\ge0\). Therefore

\[
6z-24\le4G+3H+2K+L\le4(E+1)+2E=6E+4.
\]

The resulting \(6E\ge6z-28\) uses separate budgets with total coefficient
six; no disjointness between branch targets and gap-interior excess is
assumed. Substituting \(W=19-z+E\) gives

\[
6W\ge114-6z+6z-28=86,
\qquad W\ge\lceil86/6\rceil=15.
\]

The length-five cost is the new polynomial cancellation input. The earlier
fourteen-bound proof remains valid and is retained above. ∎

## PROPOSITION 11: a length-four gap has excess away from its incoming branch

**Independent review/formalization pending; outside the frozen draft.**
This is a new cancellation constraint, not a new weighting of the scalar
gap budgets. In the X recurrence, if \(0\le k\le14\), rows \(k,k+4\)
are empty, and rows \(k+2,k+3\) are occupied, then

\[
\boxed{w_{k+2}+w_{k+3}\ge3.} \tag{34}
\]

There is no weight restriction on row \(k+1\). In the reflected Z recurrence,
with empty columns \(R,R-4\), \(4\le R\le18\), and occupied columns
\(R-2,R-3\), the separate counterpart is

\[
\boxed{w_{R-2}+w_{R-3}\ge3.} \tag{35}
\]

There is no weight restriction on column \(R-1\). Thus, in each forcing
direction, the last two interior slices of a length-four gap cannot both
be singletons, even if the first interior slice has arbitrary weight.

**X proof.** Name the three interior slices \((p,q),(u,v),(h,l)\) in
increasing order. As in (22), their equations are

\[
u=q+y^2v,\qquad h=t p+v+q+y^2l,\qquad l=t u+v.
\]

Suppose the last two slices are singletons. If \(u\ne0\), then \(u\)
is a monomial, \(v=0\), and \(l=t u\) has weight two, impossible in
the third singleton. Hence \(u=0\), \(v\) is a monomial, and \(l=v\),
so \(h=0\). The first equation gives \(q=y^2v\); the second then reduces
to \(t p=v\). Evaluation at \(y=1\) gives \(0=1\). This contradiction
does not depend on the weight of \(p\) or \(q\).

**Z proof from its own equations.** Name the slices in decreasing column
order: \((p,q)\) at \(R-1\), \((u,v)\) at \(R-2\), and \((h,l)\)
at \(R-3\). The equations at \(R,R-1,R-2\) are

\[
x^2u+v=x^2p,\qquad x^2h+l=s q+p+x^2u,\qquad s v=u+x^2h.
\]

If \((u,v),(h,l)\) are singletons and \(v\ne0\), then \(u=0\) and
\(x^2h=s v\) has weight two, impossible for \(h\) in a singleton.
Thus \(v=0\), \(u\) is a monomial, and \(x^2h=u\). In particular
\(h\ne0\), so \(l=0\). The first equation gives \(p=u\), and the
second becomes \(u=s q+u+x^2u\), or \(s q=x^2u\). Evaluation at
\(x=1\) again gives \(0=1\). This proves (35). ∎

**Paired-gap consequence.** In X, let \(0\le k\le12\) and suppose
\(k,k+2,k+6\) are successive zero rows. The singleton assumption at the
middle of the short gap is unnecessary: by adjacent nonemptiness that
middle is nonempty, so Proposition 2 gives \(w_{k+3}\ge2\). Applying
(34) to the following length-four gap gives

\[
w_{k+3}\ge2,\qquad w_{k+4}+w_{k+5}\ge3,
\qquad
\boxed{w_{k+1}+w_{k+3}+w_{k+4}+w_{k+5}\ge6.} \tag{36}
\]

For Z, take successive zeros in decreasing order \(R,R-2,R-6\), with
\(6\le R\le18\). Proposition 5 and (35) give

\[
w_{R-3}\ge2,\qquad w_{R-4}+w_{R-5}\ge3,
\qquad
\boxed{w_{R-1}+w_{R-3}+w_{R-4}+w_{R-5}\ge6.} \tag{37}
\]

Thus the proposed total-weight-five pattern is impossible: the heavier first
slice of the longer gap cannot absorb all of that gap's excess. There must
be another unit of excess in its other two slices. These are disjoint sets
of physical coefficients. Equations (36)–(37) assert a lower bound of six,
not local sharpness or existence of a weight-six extension.
There is no boundary exception inside either pair: the X branch middle is
at most 13, and the Z branch middle is at least 5.

## PROPOSITION 12: short-gap runs and their exits, without double charging

**Independent review/formalization pending; outside the frozen draft.**
Orient the zero sequence in the forcing direction: increasing row index for
X, decreasing column index for reflected Z. A short run is a maximal block
of \(m\ge1\) consecutive zero gaps of length two. It has \(m\) nonempty
middle slices. The exit target is the first slice beyond the last zero in
this direction, when it is on the board. If a longer zero gap follows the
run, that target is its first interior slice; otherwise it is in the tail
after the final zero.

### Exact polynomial propagation inside a short run

In X the middle slices are A-only. If their polynomials in forcing order
are \(P_1,\ldots,P_m\), Proposition 2 and the recurrence at the next
middle slice give

\[
P_j=t^{j-1}P_1\quad(1\le j\le m),\qquad
a_e+y^2b_e=t^mP_1 \quad\text{at an on-board exit }e. \tag{38}
\]

Here \(P_1\ne0\). To see the internal step directly, both B polynomials
at the preceding middle and intervening zero vanish, and the next middle
is itself A-only, so its equation is exactly \(P_{j+1}=tP_j\).

In Z the middle slices are B-only. Write their polynomials in decreasing
index order as \(P_1,\ldots,P_m\). At a middle index \(r\), (15) becomes
\(s b_r=x^2a_{r-2}+b_{r-2}\), since \(a_r=a_{r-1}=0\). If \(r-2\)
is the next middle, it is B-only too, giving

\[
P_j=s^{j-1}P_1\quad(1\le j\le m),\qquad
x^2a_e+b_e=s^mP_1 \quad\text{at an on-board exit }e. \tag{39}
\]

These are separate polynomial deductions. They retain actual coefficient
weights, not just occupied-slice counts. With \(t\) or \(s\) denoted by
\(T+T^2\), the middle weight is exactly
\(\sum_{j=0}^{m-1}\operatorname{wt}((T+T^2)^jP_1)\), and exit weight
is at least \(\operatorname{wt}((T+T^2)^mP_1)\).
Every internal middle after the first therefore contributes at least one
unit of excess. If a length-four gap follows, Proposition 11 supplies at
least three weight in its other two slices, so the run plus that gap has
weight at least

\[
\boxed{\sum_{j=0}^{m}\operatorname{wt}((T+T^2)^jP_1)+3
       \ \ge\ 2m+4.} \tag{40}
\]

The occupied slices counted here number \(m+3\); hence their total excess
is at least \(m+1\). The last inequality uses weight at least one for the
seed and at least two for every positive power times that nonzero seed.

The sole missing-exit possibilities are exact: X ends with middle 17 and
zero 18, so the target would be 19; Z ends with middle 1 and zero 0, so the
target would be -1. These are the same exceptions as before. A run ending
at zero 17 in X still has a tested exit target at 18; a run ending at zero
1 in Z still has a tested exit at 0. A missing next zero does not by itself
remove the exit cost.

### A disjoint partition of the excess budget

Let \(G,H,K,L\) retain their gap-length meanings, and let \(R_2\) be the
number of maximal short runs. Write \(I_d\) for the number of those runs
whose following longer gap has length \(d\), and \(I_{\ge6}\) for the
number whose following gap has length at least six. Let \(T_{\rm tail}\)
count on-board exits into the tail after the last zero, and let
\(\varepsilon\) count missing exits. Each of these last two counts is zero
or one, and \(\varepsilon=1\) is possible only at the exceptional board
edge just identified. If there are no short runs, all these counts are zero.
Every short run has exactly one of these exit types, so

\[
R_2=I_3+I_4+I_5+I_{\ge6}+T_{\rm tail}+\varepsilon. \tag{41}
\]

The run interiors contribute at least \(G-R_2\) excess, by (38)–(39).
All longer-gap interiors together contribute at least \(2H+K+L\) from
the earlier gap lemmas. An incoming short run raises the length-four gap
cost from one to two units of excess by Proposition 11, adding \(I_4\).
An incoming run also forces one excess unit in each gap of length at least
six, where this baseline count assigned none, adding \(I_{\ge6}\).
Finally the tail exits contribute \(T_{\rm tail}\). These portions lie in
disjoint short-gap interiors, longer-gap interiors, and tails, respectively.
Within an incoming length-four gap, the two units are disjoint by (34) or
(35). Therefore

\[
\begin{split}
E&\ge G-R_2+2H+K+L+I_4+I_{\ge6}+T_{\rm tail}\\
 &=G+2H+K+L-I_3-I_5-\varepsilon. \tag{42}
\end{split}
\]

In particular, since \(I_3\le H\) and \(I_5\le L\),

\[
\boxed{E\ge G+H+K-\varepsilon\ge G+H+K-1.} \tag{43}
\]

This is not obtained by adding the old branch and gap budgets as if they
were disjoint. Equation (42) explicitly permits one shared excess unit at
each incoming length-three or length-five gap. The new polynomial lemma
eliminates that sharing for length-four gaps: their first slice and their
other two slices must each pay. Proposition 12 alone supplies no analogous
extra unit for an incoming length-five gap. The exact run polynomial
identities (38)–(39) retain further cancellation information for future use. ∎

Propositions 11–12 rule out the specified hard pattern and give a run-based
budget with explicit overlap and boundary accounting. On their own they do
not establish a global improvement beyond fifteen. The later propositions
below supply the additional polynomial input and the missing budget proof.

## PROPOSITION 13: exact classification of a cheap run exit

**Independent review/formalization pending; outside the frozen draft.**
This proves the proposed singleton-feed obstruction and handles arbitrary
terminal short-middle polynomials. A weight-two exit followed by two
singletons forces the feeding polynomial to have **three or four**, not
one or two, consecutive coefficients. Both directional proofs follow.

### X equations and classification

Let \(1\le r\le14\), with empty rows \(r-1,r+1\) and a nonempty middle
\((a_r,b_r)=(P,0)\). Name the next three slices
\((A_i,B_i)=(a_{r+2+i},b_{r+2+i})\), \(i=0,1,2\). The tested equations
at \(r+2,r+3,r+4\) give exactly

\[
A_0+y^2B_0=tP,\qquad A_1+y^2B_1=B_0,\qquad
A_2+y^2B_2=tA_0+B_0+B_1. \tag{44}
\]

Suppose the three slice weights are \(2,1,1\). The second identity makes
\(B_0\) a monomial. As the first slice has weight two, \(A_0\) is also
a monomial. If the second slice is B-only, then \(A_1=0\),
\(y^2B_1=B_0\), and the last right side has even coefficient parity:
\(tA_0\) has parity zero and \(B_0,B_1\) each have parity one. It cannot
equal the monomial \(A_2+y^2B_2\). This parity argument allows overlaps.

Thus the second slice is A-only: \(A_1=B_0,B_1=0\). For \(tA_0+B_0\)
to be a monomial, \(B_0\) must cancel one of the two distinct terms of
\(tA_0\). Therefore \(B_0=yA_0\) or \(B_0=y^2A_0\).
Writing \(A_0=y^a\), the feed equation gives respectively

\[
\boxed{P=y^{a-1}(1+y+y^2)
\quad\text{or}\quad
P=y^{a-1}(1+y+y^2+y^3),\qquad a\ge1.} \tag{45}
\]

Indeed \(a=0\) would give a nonzero constant coefficient in
\(A_0+y^2B_0=tP\), impossible since \(y\mid tP\). For \(a\ge1\),
cancel \(y(1+y)\) using
\(1+y^3=(1+y)(1+y+y^2)\) and
\(1+y^4=(1+y)(1+y+y^2+y^3)\).
In particular \(\operatorname{wt}(P)\in\{3,4\}\).

This verifies and strengthens the user's singleton calculation. For a
monomial feed \(P\), the only weight-two allocations compatible with a
singleton second slice are \((A_0,B_0)=(yP,P)\) or
\(A_0=y^2P,\ yB_0=P\). The third right side then has, relative to the
exponent of \(P\), supports \(\{0,2,3\}\), \(\{-2,0,2,3\}\),
\(\{-1,3,4\}\), or \(\{-3,-1,3,4\}\), as proposed. Every admissible
case has distinct exponents. A negative relative shift does not authorize
a negative actual exponent; if that polynomial does not exist, the case
is already impossible. Classification (45) proves more without needing
these four support calculations as a premise.

### Z equations and classification, derived separately

Let \(4\le r\le17\), with empty columns \(r-1,r+1\) and nonempty
middle \((a_r,b_r)=(0,P)\). Name the slices in decreasing order by
\((A_i,B_i)=(a_{r-2-i},b_{r-2-i})\), \(i=0,1,2\).
Equation (15) at \(r,r-1,r-2\), respectively, gives

\[
x^2A_0+B_0=sP,\qquad x^2A_1+B_1=x^2A_0,\qquad
x^2A_2+B_2=sB_0+A_0+x^2A_1. \tag{46}
\]

If these three slice weights are \(2,1,1\), the second identity forces
\(A_0\) to be a monomial, and the first slice's weight then makes \(B_0\)
a monomial. If the second slice is A-only, then \(A_1=A_0\), and the
last right side is \(sB_0+(1+x^2)A_0\), of even coefficient parity. It
cannot be a monomial. Thus the second slice is B-only, with
\(A_1=0,B_1=x^2A_0\). For \(sB_0+A_0\) to be a monomial, necessarily
\(A_0=xB_0\) or \(A_0=x^2B_0\). Writing \(B_0=x^b\), the feed gives

\[
\boxed{P=x^{b-1}(1+x+x^2)
\quad\text{or}\quad
P=x^{b-1}(1+x+x^2+x^3),\qquad b\ge1.} \tag{47}
\]

If \(b=0\), the feed equation has a nonzero constant coefficient on its
left, contradicting divisibility by \(x\). For \(b\ge1\), cancel
\(x(1+x)\) from the feed as above. This derives the same necessary feed
weight three or four from (46), without a sector-symmetry assumption. ∎

### Counterexample to an obstruction for every nonzero feed

The unrestricted local implication “every nonzero feed forbids the weights
\(2,1,1\)” is **FALSE**. For X, take

\[
P=1+y+y^2,\qquad
(A_0,B_0)=(y,y^2),\quad
(A_1,B_1)=(y^2,0),\quad
(A_2,B_2)=(y^3,0).
\]

The three identities (44) read \(y+y^4=t(1+y+y^2)\), \(y^2=y^2\),
and \(y^3=ty+y^2\). For Z, take

\[
P=1+x+x^2,\qquad
(A_0,B_0)=(x^2,x),\quad
(A_1,B_1)=(0,x^4),\quad
(A_2,B_2)=(0,x^3).
\]

Then (46) reads \(x^4+x=s(1+x+x^2)\), \(x^4=x^4\), and
\(x^3=sx+x^2\). These are exact local examples within the degree cap.
They are not asserted to extend to a full cycle or to a complete long gap
with only one excess unit. They refute only the unconditional local
obstruction. Each feeding middle has weight three and supplies spare excess.

### Long-gap exit alternative

Suppose a short run feeds a longer successive-zero gap of length \(d\ge4\).
Let \(P\) be the run's final middle polynomial and \(E_D\) the excess
inside the longer gap. Then

\[
\boxed{E_D\ge2\quad\text{or}\quad\operatorname{wt}(P)\ge3.} \tag{48}
\]

The first interior slice has even weight at least two by (6) or (17).
If \(E_D\le1\), it has weight exactly two and every other interior slice
is a singleton. There are at least three interior slices, so (45) or (47)
applies and gives feed weight three or four. All equations are tested: X
requires \(r+5\le18\) and Z requires \(r-5\ge0\) for such a gap,
stronger than the respective local ranges above. For a length-three gap,
the previously proved estimate is \(E_D\ge2\) without any feed condition.

## PROPOSITION 14: a run-exit budget giving seventeen

**Independent review/formalization pending; outside the frozen draft.**
Assume either explicit recurrence and adjacent-slice nonemptiness on the
same nineteen-slice index range. With \(E,z\) as before and
\(\varepsilon\in\{0,1\}\) counting the missing exit in the forcing
direction as in Proposition 12, one has

\[
\boxed{E\ge z-1-\varepsilon\ge z-2,\qquad
W\ge18-\varepsilon\ge17.} \tag{49}
\]

If there is no missing exit at the terminal board edge, the local bound
is eighteen. The frozen draft is not modified by this research result.

**Proof with an explicit partition of excess.** If \(z=0\), all nineteen
slices are occupied and the assertion follows. Otherwise there are \(z-1\)
successive-zero gaps. Let \(G\) count short gaps, \(M=z-1-G\) count all
longer gaps, and \(R_2\) count maximal short runs. Reserve these baseline
costs on disjoint physical slices.

In a short run of length \(m\), reserve one excess unit at each middle
after the first, totalling \(m-1\). They exist by (38) or (39). Across
all runs this reserves \(G-R_2\) units.

In each longer gap, reserve one unit in its interior, totalling \(M\).
Such a unit always exists: length three has at least two by Proposition 3
or 6; length four has at least one by Proposition 7 (also Proposition 11);
length at least five has at least one in its first four interior slices
in the forcing direction by Proposition 9. Total baseline is \(G-R_2+M\).

Now take a short run and its unique following longer gap, if it has one.
If that gap has length three, it has a second excess unit after its
reserved baseline. If its length is at least four, (48) says either that
same extra gap unit exists or its feeding terminal middle has weight at
least three. In the latter case that middle has at least two excess units.
The run baseline reserved **at most one** there: one if \(m\ge2\), zero
if \(m=1\). Thus at least one additional unit remains. Merely knowing
that this middle is heavy would not suffice; Proposition 13 gives weight
at least three.

Different short runs have different terminal middles and different following
longer gaps. Run interiors are disjoint from all longer-gap interiors.
Thus the selected extra unit cannot be either a reserved baseline unit or
an extra unit selected for another run.

If the final short run exits into an on-board tail instead of a longer gap,
its target has weight at least two and supplies an excess unit in that
tail, outside all baseline regions. Only a missing-exit run lacks this
required extra unit. There is at most one: its last middle is 17 in X or
1 in Z. Therefore there are at least \(R_2-\varepsilon\) extra units, and

\[
E\ge(G-R_2+M)+(R_2-\varepsilon)
 =G+M-\varepsilon=z-1-\varepsilon.
\]

Finally \(W=19-z+E\ge18-\varepsilon\ge17\). This also covers \(z=1\),
where there are no runs or gaps, \(\varepsilon=0\), and \(W\ge18\). ∎

The endpoint exception is exact: in X, \(\varepsilon=1\) means rows 16
and 18 are empty, with their nonempty middle at 17 terminating a short run.
In Z it means columns 0 and 2 are empty, with their nonempty middle at 1.
Otherwise \(\varepsilon=0\). A missing subsequent zero does not remove
the cost of an existing tail target at X row 18 or Z column 0.

This improvement uses a new polynomial classification and a disjoint
allocation above the baseline, not a reweighting of (42). It proves
seventeen, not twenty. The exceptional edge configuration and further
physical cancellation costs remain unresolved.

## PROPOSITION 15: valuation drift forbids six consecutive singleton slices

**Independent review/formalization pending; outside both frozen drafts.**
In either recurrence, no six consecutive physical slices can all have
weight one. This does not require zeros at either end. The mechanism is
a contradiction between the low exponent of a shifted correction and the
two higher exponents it would have to cancel.

For a nonzero polynomial \(p\), let \(\nu_0(p)\) denote its least
exponent. On a monomial this is its sole exponent. We first prove separate
five-slice obstructions, in the respective forcing directions.

**X five-slice obstruction.** Suppose five singleton slices, in increasing
order, have their first four block types A, B, A, B. Write their nonzero
monomials as \(P,Q,R,S\), followed by the arbitrary singleton \((U,V)\).
If their first index is \(k\), the equations at \(k+2,k+3,k+4\) give

\[
R=tP+Q,\qquad y^2S=Q,\qquad U+y^2V=tR+S. \tag{50}
\]

The first identity requires \(Q\) to cancel one term of \(tP\), with
\(R\) the other term. Thus
\(\nu_0(Q)\le\nu_0(P)+2\) and
\(\nu_0(R)\ge\nu_0(P)+1\). The second identity gives
\(\nu_0(S)=\nu_0(Q)-2\le\nu_0(P)\). Both terms of \(tR\) have
exponents at least \(\nu_0(P)+2\), strictly above that of \(S\).
There is no cancellation in \(tR+S\), so it has weight three. The last
left side is a monomial because \((U,V)\) is a singleton, a contradiction.
If a required shifted monomial has negative exponent, the earlier identity
is already impossible in the polynomial ring. For any such five-slice
window on the board, \(0\le k\le14\), all three equations are tested.

**Z five-slice obstruction from (15).** In decreasing column order,
suppose five singleton slices have first four block types B, A, B, A.
Call their monomials \(P,Q,R,S\), followed by \((U,V)\). With first
index \(r\), equations at \(r,r-1,r-2\) give

\[
R=sP+x^2Q,\qquad x^2S=Q,\qquad x^2U+V=sR+x^2S=sR+Q. \tag{51}
\]

The first identity makes \(x^2Q\) and \(R\) the two distinct terms of
\(sP\). Consequently \(\nu_0(Q)\le\nu_0(P)\) and
\(\nu_0(R)\ge\nu_0(P)+1\). Both terms of \(sR\) lie at exponents
at least \(\nu_0(P)+2\), so \(sR+Q\) has three terms. The last left
side is a monomial, a contradiction. A five-slice descending window has
\(4\le r\le18\), so \(r,r-1,r-2\) are all tested.

**Why six singletons force one of those windows.** For singleton slices
let \(\alpha_i=a_i(1)\), \(\beta_i=b_i(1)\) in \(\mathbb F_2\).
Exactly one block is a monomial, so \(\alpha_i+\beta_i=1\).
For X, evaluating any equation whose three slices are singletons at one
gives

\[
\alpha_i=\beta_{i-1}+\beta_{i-2}+\beta_i,
\qquad \alpha_{i-1}+\alpha_{i-2}=1. \tag{52}
\]

In a six-slice window \(k,\ldots,k+5\), the equations at
\(k+2,\ldots,k+5\) therefore force the first five block types to
alternate. If the first is A, the initial five-slice window has the
forbidden A,B,A,B start; if the first is B, the final five-slice window
has that start. Both contradict (50).

For Z, the evaluated equation is instead

\[
0=\alpha_i+\alpha_{i-1}+\alpha_{i-2}+\beta_{i-2},
\qquad \alpha_i+\alpha_{i-1}=1. \tag{53}
\]

It forces the last five types in increasing order, hence the first five
in decreasing forcing order, to alternate. Starting with B uses the first
descending five-slice window in (51); starting with A uses the second.
This proves the six-singleton obstruction in each sector. A six-slice
window begins at \(0\le k\le13\); the four equations used in the parity
step are exactly \(k+2,\ldots,k+5\), with no boundary exception. ∎

**Physical-weight consequences.** In any consecutive occupied interval of
length \(\ell\), partition its first \(6\lfloor\ell/6\rfloor\) slices
into disjoint blocks of six. Every such block costs at least seven weight;
remaining slices cost at least one each. Thus

\[
\boxed{W_{\rm interval}\ge\ell+\lfloor\ell/6\rfloor.} \tag{54}
\]

If the occupied intervals have lengths \(\ell_1,\ldots,\ell_h\), then
\(E\ge\sum_j\lfloor\ell_j/6\rfloor\). These excess costs are not
automatically disjoint from the run-exit budget and must not simply be
added to it. Nonetheless, this separate bound already gives

\[
\boxed{z=0\Longrightarrow W\ge22,\qquad
z=1\Longrightarrow W\ge20.} \tag{55}
\]

For \(z=0\), use \(\ell=19\). For \(z=1\), the two occupied intervals
(allowing a zero-length interval at a board edge) have lengths summing to
18. Their quotients on division by six sum to at least two: their two
remainders are at most ten in total, so the quotient sum, an integer, is
at least \(\lceil(18-10)/6\rceil=2\). Hence weight is at least \(18+2=20\).
Any hypothetical weight below twenty in this local problem must therefore
have at least two empty slices. This is not a global distance-twenty proof.

## PROPOSITION 16: width and root multiplicities restrict cheap exits

**Independent review/formalization pending; outside both frozen drafts.**
Use the indeterminate \(T\) for either sector and put \(t=T(1+T)\).
For nonzero \(p\), let \(\nu_1(p)\) be the multiplicity of the factor
\(1+T\). In a short run of \(m\) gaps with seed \(P\), the exact
polynomials are \(P_j=t^{j-1}P\), and

\[
\begin{split}
\nu_0(P_j)&=\nu_0(P)+j-1,\\
\nu_1(P_j)&=\nu_1(P)+j-1,\\
\deg P_j&=\deg P+2(j-1). \tag{56}
\end{split}
\]

The valuation identities follow by extracting the largest powers of
\(T\) and \(1+T\): the remaining factors evaluate nonzero at the
respective root, and their product still does so. Degree adds because
leading coefficients multiply nontrivially in the polynomial domain.
Thus width nineteen imposes the concrete restrictions

\[
\boxed{\deg P+2(m-1)\le18,\qquad
\nu_0(P)+\nu_1(P)+2(m-1)\le18.} \tag{57}
\]

For the second inequality, the coprime factors \(T\) and \(1+T\) imply
\(T^{\nu_0(P)}(1+T)^{\nu_1(P)}\mid P\), so their total degree is at
most \(\deg P\). No physical weight has been identified with these
degrees or multiplicities.

Now suppose the exit prefix has weights \(2,1,1\). Proposition 13 says
its feeding terminal polynomial \(P_m\) is a monomial shift of
\(1+T+T^2\) or \(1+T+T^2+T^3\). The former has \(\nu_1=0\),
since its value at one is one. The latter equals \((1+T)^3\), so it
has \(\nu_1=3\). Equation (56) therefore gives the stronger restrictions

\[
\begin{array}{ll}
P_m=T^c(1+T+T^2):&m=1,\\
P_m=T^c(1+T)^3:&m\le4,\quad
P=T^{c-m+1}(1+T)^{4-m},\quad c\ge m-1.
\end{array} \tag{58}
\]

In particular a short run of length at least five cannot have a cheap
\(2,1,1\) exit, whatever its seed weight. These restrictions arise from
root multiplicity in the exact recurrence, not from scalar gap counting.

**Extra surplus in a cheap longer gap.** If a longer gap fed by a short
run has excess exactly one, its prefix is \(2,1,1\), so (58) applies.
If \(m=1\), the terminal middle has weight at least three and its excess
is at least two, with no middle baseline reserved there. If \(m\ge2\),
only the four-term alternative is possible: the terminal middle has
excess three, with just one middle baseline unit reserved there. In both
cases at least **two**, rather than one, spare units remain in that run.

For example, let \(C\) count short runs whose following longer gap has
excess exactly one. The same disjoint regions as in Proposition 14 then
give the conditional refinement

\[
E\ge z-1-\varepsilon+C,
\qquad W\ge18-\varepsilon+C. \tag{59}
\]

This is only a conditional surplus estimate; \(C\) can be zero. No bound
twenty follows without additional control of other exits and endpoints.
For a missing exit, (57) uses the last physical middle only. There is no
license to impose a degree restriction on an untested slice beyond the board. ∎

## PROPOSITION 17: a tight missing-exit run has only one, two, or three gaps

**Independent review/formalization pending; outside both frozen drafts.**
For a missing-exit run of length \(m\), let its seed be \(P\ne0\) and
let \(E_R\) be the excess in its middle slices. Then

\[
\boxed{E_R=m-1\quad\Longleftrightarrow\quad
\operatorname{wt}(P)=1\ \text{and}\ 1\le m\le3.} \tag{60}
\]

**Proof.** Positive powers \(t^jP\) have weight at least two. Thus a
seed of weight at least two already contributes an extra unit beyond the
baseline \(m-1\). If \(P\) is a monomial, the first four weights are
\(1,2,2,4\), directly from

\[
t=T+T^2,\quad t^2=T^2+T^4,\quad
t^3=T^3+T^4+T^5+T^6.
\]

Consequently the baseline is exact for \(m\le3\); for \(m\ge4\),
the fourth middle alone supplies two further units. This proves (60). ∎

If a full physical sequence had weight exactly seventeen, Proposition 14
would force \(\varepsilon=1\) and equality in its budget. The missing-exit
run is a disjoint block assigned only \(m-1\) baseline units, so it must
satisfy (60). Thus a putative weight-seventeen sequence has a monomial seed
in a terminal short run of at most three gaps. More explicitly:

- For X, the terminal zero is 18, the run starts at zero \(18-2m\),
  and the seed middle is \(19-2m\), with \(m\in\{1,2,3\}\).
- For Z, the terminal zero is 0, the run starts at zero \(2m\), and
  the seed middle is \(2m-1\), with the same allowed lengths.

For a seed \(T^j\), the width bound further requires
\(0\le j\le18-2(m-1)\). These are necessary endpoint conditions, not
enumerated supports or constructions of full cycles. They preserve the
untested exit exception exactly. The adjoining longer gap or initial tail
must still be analyzed; the argument does not exclude all these cases.

## PROPOSITION 18: an incoming length-three gap costs at least five

**Independent review/formalization pending; outside both frozen drafts.**
The first candidate saving is already proved in Proposition 16: a cheap
run exit leaves at least two spare run units, not just one, by the
root-at-one multiplicity of the terminal polynomial. The second candidate
also holds, with distinct forward and backward proofs below.

Use \(T\) for the indeterminate and \(t=T+T^2\). Let a nonempty short
run feed a successive-zero gap of length three. Let \(P\ne0\) be the
last short-middle polynomial. Name the two interior slices of the longer
gap \((p,q),(u,v)\), in forcing order, and write their total weight as
\(V=\operatorname{wt}(p)+\operatorname{wt}(q)+\operatorname{wt}(u)
+\operatorname{wt}(v)\). Then

\[
\boxed{V\ge5,\qquad E_D=V-2\ge3.} \tag{61}
\]

If \(V=5\), the feed \(P\) is a monomial shift of
\(1+T+T^2\) or \(1+T+T^2+T^3\), and the two slice weights are
exactly \(2,3\).

### X proof

Let the short-middle index be \(r\), with zero rows at \(r-1,r+1\)
and the next zero at \(r+4\). The two gap interiors are at \(r+2,r+3\).
The equations at \(r+2,r+3,r+4\) give

\[
p+T^2q=tP,\qquad u=q+T^2v,\qquad tp+q+v=0. \tag{62}
\]

At \(T=1\), they imply
\(p(1)=q(1)=v(1)\) and \(u(1)=0\).
If \(u\ne0\), it has even weight at least two. If \(V\le4\), the
remaining three polynomials \(p,q,v\) have total weight at most two.
Their equal parities cannot all be odd, so all are even. At most one can
be nonzero, of weight two. But a single nonzero term cannot satisfy
\(tp+q+v=0\), and if all vanish then \(u=0\). This is a contradiction.

If \(u=0\), the same domain cancellation as in Proposition 3 gives

\[
p=(1+T)h,\qquad q=T^3h,\qquad v=Th
\]

for some \(h\ne0\). Nonvanishing follows from the nonzero feed.
The extra feed parity \(p(1)=q(1)\) forces \(h(1)=0\), so
\(\operatorname{wt}(h)\ge2\). Thus
\(V=2\operatorname{wt}(h)+2\rho(h)\ge6\). This proves (61).

For equality \(V=5\), necessarily \(u\ne0\). The even weight of
\(u\) is two or four. The other three weights have a common parity;
their sum is odd, so all three are odd. They must each equal one, while
\(\operatorname{wt}(u)=2\). Thus \(p,q,v\) are monomials, and
\(q+v=tp\) makes \(q\) and \(v\) the distinct terms \(Tp,T^2p\).
Accordingly \(q=Tp\) or \(q=T^2p\). Writing \(p=T^a\), the feed
in (62) gives

\[
P=T^{a-1}(1+T+T^2)
\quad\text{or}\quad
P=T^{a-1}(1+T+T^2+T^3),\qquad a\ge1. \tag{63}
\]

The condition \(a\ge1\) follows from the feed's constant coefficient,
and the two forms follow by cancelling \(T(1+T)\), as in Proposition 13.

### Z proof from its actual backward equations

Now let the feeding middle be at \(r\), with zero columns \(r+1,r-1\)
and the next zero in forcing order at \(r-4\). Put \((p,q)\) at
\(r-2\) and \((u,v)\) at \(r-3\). The equations at \(r,r-1,r-2\)
are

\[
T^2p+q=tP,\qquad v=T^2(p+u),\qquad tq=p+T^2u. \tag{64}
\]

At one these give \(p(1)=q(1)=u(1)\) and \(v(1)=0\).
If \(v\ne0\) and \(V\le4\), its weight is at least two and the
three other weights sum to at most two. Their common parity is even, so
at most one of \(p,q,u\) is nonzero. This contradicts
\(tq+p+T^2u=0\); if all vanish then so does \(v\).

If \(v=0\), then \(u=p\) and \(tq=(1+T^2)p\). Cancelling
\(1+T\) gives \(Tq=(1+T)p\), so

\[
p=u=Th,\qquad q=(1+T)h,\qquad h\ne0.
\]

The feed parity \(p(1)=q(1)\) forces \(h(1)=0\), and again
\(V=2\operatorname{wt}(h)+2\rho(h)\ge6\).
For equality \(V=5\), the same parity reasoning gives
\(\operatorname{wt}(v)=2\) and monomials \(p,q,u\).
The relation \(tq=p+T^2u\) forces \(p=Tq\) or \(p=T^2q\).
Writing \(q=T^b\), the feed in (64) gives

\[
P=T^{b-1}(1+T+T^2)
\quad\text{or}\quad
P=T^{b-1}(1+T+T^2+T^3),\qquad b\ge1. \tag{65}
\]

This proves the separate backward assertion. All equations are tested:
the X pair has \(1\le r\le14\); the Z pair has \(4\le r\le17\).
No equation outside the board is added. ∎

**Local sharpness check, not a full-cycle extension.** With
\(P=1+T+T^2\), X admits
\((p,q)=(T,T^2)\), \((u,v)=(T^2+T^5,T^3)\) in (62).
For Z, the same feed admits \((p,q)=(T^2,T)\),
\((u,v)=(T,T^3+T^4)\) in (64). Both have weights \(2,3\), and direct
substitution verifies every displayed local equation. They fit the degree
cap. Nothing here asserts extendibility to a full nineteen-slice cycle.

## PROPOSITION 19: combined savings with disjoint block accounting

**Independent review/formalization pending; outside both frozen drafts.**
Retain the run partition of Proposition 14. Let

- \(H\) count all length-three zero gaps;
- \(I_3\) count those immediately preceded by a short run in forcing order;
- \(J\) count those incoming length-three gaps whose interior weight is five;
- \(C\) count short runs whose following longer gap has excess exactly one;
- \(\sigma\) be the missing-exit run's actual excess minus its baseline
  \(m-1\), or zero if there is no missing-exit run.

All these counts are nonnegative, \(J\le I_3\le H\), and \(\sigma\ge0\).
The categories counted by \(C\) and \(I_3\) are disjoint by (61).
Then

\[
\boxed{E\ge z-1-\varepsilon+C+H+I_3+J+\sigma,\qquad
W\ge18-\varepsilon+C+H+I_3+J+\sigma.} \tag{66}
\]

**Proof.** The baseline remains \(G-R_2+M\), reserving one unit at every
noninitial short middle and one inside each longer gap. The original proof
then paid one extra for every run with an exit. We now specify additional
units on the same disjoint run-plus-gap blocks, rather than adding budgets
that may count the same coefficients.

For each cheap longer gap counted by \(C\), Proposition 16 supplies at
least two spare run units, so there is one extra beyond that run's original
one-unit payment.

For an incoming length-three gap, if its interior weight is at least six,
its excess is at least four. After its one-unit longer-gap baseline, at
least three units remain. This is two more than the one-unit run-exit
payment in Proposition 14.

If instead its weight is five, its excess is three, leaving two units after
the longer-gap baseline. By (63) or (65), the terminal feed has three or
four consecutive coefficients. The multiplicity argument in Proposition 16
therefore supplies at least two more spare units in the run: three terms
force run length one, while four terms leave two spare units even after a
noninitial-middle baseline. In total there are at least four extra units,
three more than the original one-unit payment. Thus all incoming length-three
blocks supply an improvement of at least \(2I_3+J\).

Every unpaired length-three gap has excess at least two by Proposition 3
or 6, with only one baseline unit reserved. These give a further
\(H-I_3\) units, in distinct unpaired gap interiors. The missing-exit run
was assigned no exit payment, so all its surplus \(\sigma\) remains
available. Its middles are disjoint from every run-plus-longer-gap block.

Adding only these disjoint improvements to Proposition 14 gives
\(C+(2I_3+J)+(H-I_3)+\sigma=C+H+I_3+J+\sigma\), proving (66).
No six-singleton cost has been added here: such a cost could overlap these
regions and needs its own allocation. ∎

**Consequences for proposed weights seventeen and eighteen.**

- Any incoming length-three gap has \(H\ge1,I_3\ge1\), hence forces
  \(W\ge19\). It rules out both seventeen and eighteen.
- If such a gap has weight five, then also \(J\ge1\), and \(W\ge20\).
- An incoming length-three gap also gives \(W\ge20\) whenever
  \(\varepsilon=0\), even without the equality-five hypothesis.
- Weight seventeen would require \(\varepsilon=1\) and
  \(C=H=I_3=J=\sigma=0\). Its missing-exit run must therefore have a
  monomial seed and length at most three, as in Proposition 17.
- If \(W\le18\), then there can be no incoming length-three gap. For
  \(\varepsilon=0\), all the displayed savings must vanish. For
  \(\varepsilon=1\), their sum is at most one.

### Why the Proposition 19 savings alone did not exclude every case

The following scalar profile satisfies the budgets through Proposition 19
and the six-singleton restriction. In X, put zero weights at
\(0,6,12,16,18\), weight two at \(3,9,14\), and weight one at every
other index. Then \(W=17,z=5,E=3\). The zero gaps are \(6,6,4,2\).
The only short run is the final single short gap with its missing exit;
thus \(\varepsilon=1\), \(H=I_3=J=C=0\), and its singleton middle
permits the run requirement \(\sigma=0\). Each longer gap has one
excess unit. Its occupied intervals have lengths \(5,5,3,1\), so no
six consecutive occupied singletons occur. The length-four gap's two
farther interior slices include the weight-two slice at 14, as required
by Proposition 11. The longer gaps' first four interiors also contain
their weight-two slice, as required by Proposition 9.

Reversing the indices gives the corresponding Z scalar profile: zero
weights at \(0,2,6,12,18\), weight two at \(4,9,15\), and weight one
elsewhere. It meets the same directionally interpreted conditions.
Increasing any existing weight-two slice to three gives a scalar
weight-eighteen profile satisfying these conditions as well.

These are **not polynomial cycles or logical operators**. They show only
that the scalar conditions through Proposition 19 do not exclude these
seventeen/eighteen patterns. The later polynomial classification in
Propositions 22–24 does exclude the displayed profiles, through their
one-excess gaps of length at least five. It does not rule out all other
seventeen/eighteen patterns. Neither frozen draft is strengthened by these
research checkpoints.

## PROPOSITION 20: conditional endpoint coupling to the monomial-period lattice

**Independent review/formalization pending; outside both frozen drafts.**
This section uses only the charge-factor and monomial-period results in
`analytical/notes/charge-factors.md`, Propositions 1–2, as additional input.
It does not use that note's path or bridge arguments. Its factor input is
the charge algebra \(C=\mathbb F_2[x^{\pm1},y^{\pm1}]/(f,g)\), where
\(f=x+x^2+y^2\), \(g=1+x^2(y+y^2)\), and the monomial equality criterion

\[
[x^iy^j]=[1]\quad\Longleftrightarrow\quad
(i,j)\in\Lambda,
\qquad\Lambda=\mathbb Z(16,-3)+\mathbb Z(3,13). \tag{67}
\]

This criterion is supplied at PROPOSITION grade by the factor route: the
two field coordinates of \(x^iy^j\) are
\(\alpha^{i+3j}\) and \(\beta^{i+26j}\), with exact orders 7 and 31.
Both displayed lattice generators annihilate these exponents; their
determinant is 217, the index of that congruence kernel. Monomials are
units, so equality between two monomial labels is equivalent to their
exponent difference lying in \(\Lambda\). This does not assert anything
about the weight of a general sum of labels.

### Exact extraction of the two endpoint labels

Consider an X sequence satisfying the explicit recurrence and adjacent
nonemptiness, with \(W=17\). Proposition 17 supplies a missing-exit run
of \(m\in\{1,2,3\}\) short gaps, with monomial seed \(y^b\) at
row \(r=19-2m\). Its final middle at row 17 is
\(a_{17}=t^{m-1}y^b\), where \(t=y+y^2\); \(b_{17}=0\), and
row 18 is empty. In particular

\[
0\le b\le18-2(m-1). \tag{68}
\]

For the full syndrome \(S=ga+fb\), the recurrence makes all row slices
2 through 18 zero. The low and high parts are therefore exactly

\[
\begin{split}
S_{\rm lo}&=a_0+y^2b_0+x(a_1+b_0+y^2b_1),\\
S_{\rm hi}&=x^{19}t^m y^b. \tag{69}
\end{split}
\]

The high formula uses only rows 17 and 18 in the convolution; it imposes
no equation at row 19. Since \([S]=0\) and \(x^2t=1\) in \(C\),

\[
[S_{\rm lo}]=[S_{\rm hi}]=[x^{19-2m}y^b]. \tag{70}
\]

Suppose explicitly that the low two rows contain exactly one physical
qubit, \(w_0+w_1=1\), at physical column \(a\), \(0\le a\le18\).
The following table lists its low label. In the row-0 B case, use
\(y^2+x=x^2\) from \(f=0\), rather than treating its two low syndrome
terms as two independent charges.

| Sole qubit in rows 0 and 1 | Low charge label | Label exponents \((u,v)\) |
|---|---|---|
| A at row 0, column \(a\) | \([y^a]\) | \((0,a)\) |
| B at row 0, column \(a\) | \([x^2y^a]\) | \((2,a)\) |
| A at row 1, column \(a\) | \([xy^a]\) | \((1,a)\) |
| B at row 1, column \(a\) | \([xy^{a+2}]\) | \((1,a+2)\) |

This is an algebraic classification of a stipulated single qubit, not an
assumption that all low boundaries have this form. Combining the table
with (70) and (67) gives

\[
(19-2m-u,\ b-v)\in\Lambda. \tag{71}
\]

### Inverse bounds, not a lattice-point enumeration

For any \((d,e)=(16n+3q,-3n+13q)\in\Lambda\), the inverse is

\[
n=\frac{13d-3e}{217},\qquad
q=\frac{3d+16e}{217}. \tag{72}
\]

All displacements in (71) have \(11\le d\le17\) and \(|e|\le20\),
by (68), the physical range of \(a\), and the table's possible shift two.
Thus

\[
0<\frac{83}{217}\le n\le\frac{281}{217}<2.
\]

As \(n\) is an integer, \(n=1\). The first lattice coordinate now
requires \(d\equiv1\pmod3\). Substituting \(d=19-2m-u\) gives
\(m\equiv u\pmod3\), which has a unique solution in \(1\le m\le3\).
Finally \(e=(13d-217)/3\). Consequently:

| Sole low qubit | Forced \(m\) | Forced physical relation | Allowed physical exponents |
|---|---|---|---|
| A at row 0 | 3 | \(b=a-16\) | \(16\le a\le18,\ 0\le b\le2\) |
| B at row 0 | 2 | \(b=a-16\) | \(16\le a\le18,\ 0\le b\le2\) |
| A at row 1 | 1 | \(b=a-3\) | \(3\le a\le18,\ 0\le b\le15\) |
| B at row 1 | 1 | \(b=a-1\) | \(1\le a\le18,\ 0\le b\le17\) |

In particular, in the user's row-1 A case, the proposed displacement is
\((18-2m,b-a)\). The same inverse bound forces \(n=1\), and congruence
forces \(m=1\), yielding \((16,-3)\). The possible row displacements
14 and 12 at \(m=2,3\) cannot lie in \(\Lambda\) with transverse
displacement of absolute value at most 20. This proves the proposed
width exclusion without generating a list of lattice points. ∎

### Scope of the monomial hypothesis

For an unrestricted low boundary, (69) reduces in \(C\) only to

\[
[S_{\rm lo}]=[a_0+x^2b_0+xa_1+xy^2b_1]. \tag{73}
\]

If more than one low qubit is present, this is a sum of labels and cannot
be replaced by the table without an additional proof. Proposition 20 alone
does not force \(w_0+w_1=1\); Proposition 29 later derives that condition
for tight weight seventeen using additional tail and gap-budget results.
The conclusions of this section are conditional endpoint restrictions,
not an exclusion of all weight-seventeen sequences. Nor is this table a dual-sector result:
the period lattice is not invariant under exchanging its axes, and the
reflected Z endpoint labels would require a separate derivation.

## PROPOSITION 21: the forced exponent drop requires physical B support

**Independent review/formalization pending; outside both frozen drafts.**
In each of the four cases in Proposition 20, the terminal seed column
\(b\) is strictly smaller than the initial physical column \(a\).
This has a concrete consequence for physical coefficients, not just for
charge labels. There must be an occupied B qubit at some row \(i\) and
column \(c\) satisfying

\[
\boxed{2\le i\le r-2,\qquad
c+\left\lfloor\frac{r-1-i}{2}\right\rfloor\le b,
\qquad r=19-2m.} \tag{74}
\]

In particular \(c\le b<a\): this B qubit lies strictly below the low
qubit's column exponent and is outside the first two rows. In the two
cases where the initial qubit is itself B-type, it is an additional B
qubit, not that initial coefficient.

**Proof.** The odd-channel recurrence unrolls to the following identity
at the terminal seed row \(r\). Write \(B(y)=1+y^2t=1+y^3+y^4\).
The preceding zero row has \(b_{r-1}=0\), and the A-only seed has
\(b_r=0\). Hence

\[
\begin{split}
y^b=a_r={}&t^{(r-1)/2}a_1+t^{(r-3)/2}b_1\\
&+\sum_{\substack{2\le i\le r-3\\ i\ {
m even}}}
     t^{(r-1-i)/2}b_i\\
&+\sum_{\substack{3\le i\le r-2\\ i\ {
m odd}}}
     t^{(r-2-i)/2}B(y)b_i. \tag{75}
\end{split}
\]

To verify it, substitute (1) along odd indices from 3 through \(r\).
Each even \(b_i\) contributes once, at equation \(i+1\). Each internal
odd \(b_i\) contributes at equations \(i\) and \(i+2\), with combined
coefficient \(t^{(r-2-i)/2}(1+y^2t)\). The initial \(b_1\) contributes
only at equation 3, because \(a_1\) is the prescribed seed and there is
no equation at index 1. This proves every term of (75).

In the stipulated low boundary, \(a_1\) and \(b_1\) are either zero or
the monomial \(y^a\). As \(a>b\), the first two terms in (75) have no
coefficient at exponent \(b\). Every multiplier in the two sums has
least exponent
\(\lfloor(r-1-i)/2\rfloor\): \(t\) has least exponent one and
\(B(y)\) has constant coefficient one. If all occupied coefficients
\(y^c\) of all those \(b_i\) satisfied the strict reverse of (74),
both sums would have zero coefficient at exponent \(b\). That contradicts
the left side \(y^b\). Cancellation can remove contributions but cannot
create a coefficient below every summand's least exponent. Thus at least
one actual B coefficient obeys (74). ∎

For the specifically proposed row-1 A case this reads

\[
\exists\,B(i,c)\text{ occupied}:\quad
2\le i\le15,\qquad
c+\left\lfloor\frac{16-i}{2}\right\rfloor\le a-3. \tag{76}
\]

**A second, disjoint B coefficient in the row-1 A case.** Here
\(a_1=y^a,b_1=0,r=17\). The homogeneous term \(t^8y^a\) in (75) has
leading exponent \(a+16\), whereas the left side \(y^{a-3}\) has much
smaller degree. Some B contribution must cancel the coefficient at
\(a+16\). The even-index multiplier in (75) has degree \(16-i\), and
the odd-index multiplier has degree \(19-i\), since \(\deg B(y)=4\).
It follows that a B coefficient \(y^c\) occurs satisfying at least one
of the following two inequalities:

\[
\begin{array}{ll}
2\le i\le14,\ i\text{ even}:&c\ge a+i,\\
3\le i\le15,\ i\text{ odd}:&c\ge a+i-3.
\end{array} \tag{77}
\]

Indeed, if every B coefficient times its multiplier had degree strictly
less than \(a+16\), none could cancel the homogeneous leading term.
No positivity assumption about binary sums is used. In particular this
coefficient has \(c\ge a\), while the coefficient in (76) has
\(c\le a-3\). They are distinct physical B qubits, proving

\[
\boxed{\sum_{i=0}^{18}\operatorname{wt}(b_i)\ge2}
\quad\text{under the row-1 A hypotheses of Proposition 20.} \tag{78}
\]

Width nineteen also makes (77) an early-row restriction: the even witness
must have \(i\le18-a\), or the odd witness \(i\le21-a\), because
\(c\le18\). These are necessary inequalities, not a listing of supports.

The valuation drop of three therefore cannot be supplied by homogeneous
A propagation from the low monomial. It requires B forcing in both of
the disjoint column regions just identified. For the row-0 cases the
analogous drop is sixteen, with the final seed in column at most two, which
confines the needed coefficient still more sharply through (74). These
support restrictions and the two-B requirement do not strengthen the global
bound on \(W\). They do not say that the indicated qubits can complete a
cycle, or that all of them together cost enough to prove
twenty. The two-label and heavier low-boundary cases remain outside the
monomial endpoint comparison.

## PROPOSITION 22: exact minimum length-four gaps and their outgoing costs

**Independent review/formalization pending; outside both frozen drafts.**
Write \(s=T^2\), \(t=T+T^2\). In X, take zero endpoints \(k,k+4\),
\(0\le k\le14\), and three occupied interiors \((p,q),(u,v),(h,l)\)
in increasing order. If their total weight is four, the unique form is

\[
\boxed{(p,q)=(0,s v),\quad(u,v)=(0,v),\quad(h,l)=(v,v),
\qquad v\text{ a monomial}.} \tag{79}
\]

In Z, take zero endpoints \(R,R-4\), \(4\le R\le18\), and name the
interiors \((p,q),(u,v),(h,l)\) in decreasing order. Total weight four
forces instead

\[
\boxed{(p,q)=(s h,0),\quad(u,v)=(s h,0),\quad(h,l)=(h,s^2h),
\qquad h\text{ a monomial}.} \tag{80}
\]

Both have directional weights \(1,1,2\); their block contents differ.

**X proof.** The three local equations are

\[
u=q+s v,\qquad h=t p+v+q+s l,\qquad l=t u+v. \tag{81}
\]

Total four on three occupied slices means exactly one weight-two slice.
If it is first, the last two are singletons, already excluded by
Proposition 11. Directly, a second A singleton forces \(l=tu\) of weight
two, while a second B singleton forces \(l=v,h=0,q=sv\), and then
\(tp=v\), impossible by evaluation at one.

If the weight-two slice is second, a first A singleton gives \(q=0\),
\(u=sv\), and hence monomials \(u,v\). Then
\(l=(1+st)v=(1+T^3+T^4)v\) has weight three, contradicting the final
singleton. A first B singleton has monomial \(q\), but \(u+sv=q\)
has even parity on its left because the second physical weight is two.
This is impossible.

The first two slices are therefore singletons. Equation \(u+sv=q\)
forces \(q\) to be a monomial and \(p=0\). If the second slice is
A-only, then \(u=q,v=0\), \(l=tq\) has weight two, and \(h=0\).
The middle equation would give \((1+st)q=0\), impossible in the domain.
Thus the second slice is B-only, with \(q=sv\). The remaining equations
give \(l=v,h=v\), proving (79). Substitution verifies sufficiency for
the three displayed equations.

**Z proof from the backward recurrence.** The corresponding equations are

\[
su+v=sp,\qquad sh+l=tq+p+su,\qquad tv=u+sh. \tag{82}
\]

A weight-two first slice with the last two singleton is excluded by
Proposition 11's separate Z proof. If the second slice has weight two,
a first A singleton contradicts parity in \(su+v=sp\). A first B
singleton gives \(p=0,v=su\), with \(u,v\) monomials. The last equation
then gives \(sh=(1+st)u\) of weight three, impossible for the final
singleton.

The first two are therefore singletons. The first equation makes \(p\)
a monomial and \(q=0\). If the second is B-only, then \(u=0,v=sp\),
and \(h=tp\) has weight two. Thus \(l=0\), and the middle equation
would give \(stp=p\), impossible. If the second is A-only, then
\(u=p,v=0\), \(sh=p\), and the middle equation gives \(l=sp=s^2h\).
This proves (80), which also satisfies all three equations. ∎

**Outgoing slice and exact exceptions.** For X, if \(k+5\le18\), write
the next slice after the ending zero as \((A,B)\). Its tested equation is

\[
A+sB=th+l=(1+T+T^2)v. \tag{83}
\]

For Z, if \(R-5\ge0\), the equation at \(R-3\) gives the next slice
in decreasing order as

\[
sA+B=tl+h=(1+T^5+T^6)h. \tag{84}
\]

Each right side has weight three, so the physical outgoing weight is at
least three. More precisely it is three plus twice the support overlap
between the two shifted blocks, so it is odd; it need not be exactly three.
There is no such assertion when the X gap ends at row 18
(its target would be 19), or when the Z gap ends at column 0 (its next
equation would be at index 1). The coefficient range is also exact:
(79) requires the exponent of \(v\) at most 16, and (80) that of \(h\)
at most 14. If the next gap is short, its middle is A-only in X or B-only
in Z, so (83) or (84) is its actual seed polynomial, of weight three.
In the Z short-gap case this further requires \(\deg h\le12\).

## PROPOSITION 23: longer gaps cannot have only one excess unit

**Independent review/formalization pending; outside both frozen drafts.**
Every successive-zero gap of length \(d\ge5\), with all interiors
occupied, satisfies

\[
\boxed{W_D\ge d+1,\qquad E_D=W_D-(d-1)\ge2.} \tag{85}
\]

Put \(s=T^2\) and \(t=T+T^2\). Proposition 9 already gives
\(E_D\ge1\) from the first four occupied interiors. This is a polynomial
cancellation result in each recurrence, not a count of transfer states.
The remaining low-weight hypothesis to exclude is that, if
\(E_D=1\), one interior slice has weight two and all others are
singletons. Proposition 9 forces this unique weight-two slice into one
of the first four interior positions in forcing order. There are at least
four occupied interiors. The fifth position is either the ending zero
(when \(d=5\)) or a singleton. Thus its folded weight is at most one.
We rule out the four positions below with arbitrary polynomial exponents.
No six-singleton bound or upper bound on \(d\) is needed.

Name the first three interiors \((p,q),(u,v),(h,l)\), the fourth
\((M,N)\), and the fifth \((A,B)\). For X, put
\(Q_i=a_i+s b_i\) in these local indices. With the initial zero at
local index 0, the equations used are

\[
Q_2=q,\quad Q_3=tp+v+q,\quad
Q_4=tu+l+v,\quad Q_5=th+N+l. \tag{86}
\]

For Z, local indices increase in decreasing physical column order, and
\(Q_i=s a_i+b_i\). Its distinct equations are

\[
Q_2=sp,\quad Q_3=tq+p+su,\quad
Q_4=tv+u+sh,\quad Q_5=tl+h+sM. \tag{87}
\]

These are tested equations whenever needed, including when the fifth slice
is the ending zero. For X, a gap starting at \(k\) has
\(0\le k\le18-d\); the indices used are \(k+2,\ldots,k+5\), all
between 2 and 18. For Z, the decreasing-order gap starts at
\(d\le R\le18\); the original equation indices are
\(R,R-1,R-2,R-3\), all at least \(d-3\ge2\) and at most 18.
Thus even the endpoint gaps ending at X row 18 or Z column 0 are covered.
No additional boundary exception is needed for this lemma.

### X elimination of the unique weight-two position

**Position 1.** Since \(Q_2=q\) is a monomial, \(q\) is a monomial
and weight two of \((p,q)\) makes \(p\) a monomial too. A second
B singleton makes \(Q_3=tp+v+q\) even in parity, impossible for a
singleton. Thus \((u,v)=(q,0)\), and
\(Q_3=tp+q=F\) is a monomial. Necessarily \(q,F\) are the two
distinct terms of \(tp\). If the third slice is A-only, \(l=0\) and
\(Q_4=tq\) has weight two. If it is B-only, \(l=F/s\) and
\(Q_4=tq+F/s\) has weight three: the exponent of \(F/s\) is at
most that of \(p\), while both terms of \(tq\) are at least two higher.
Either contradicts the fourth singleton.

**Position 2.** Parity in \(u+sv=q\) excludes a first B singleton.
Thus \(p\) is a monomial, \(q=0\), and \(u=sv\) with \(u,v\)
monomials. The third folded slice is \(tp+v\), a monomial. Whether
that singleton is A-only or B-only, \(l\) is zero or a monomial.
But \(Q_4=(1+st)v+l\) is a three-term polynomial plus zero or one
monomial. Its weight is at least two, contradicting the fourth singleton.

**Position 3.** The first equation gives a first B singleton, \(p=0\).
A second A singleton would make \(Q_3=q\) odd in parity, inconsistent
with physical weight two. Hence \(u=0,q=sv\), with \(v\) monomial,
and \(Q_3=(1+s)v\). If \(h,l\) were both monomials, \(Q_4=l+v\)
would have even parity and could not be a singleton. The two remaining
possibilities are

\[
(h,l)=((1+s)v,0)\quad\text{or}\quad(0,v/s+v).
\]

In the first, \(Q_4=v\), so \(N=0\) or \(v/s\).
Then \(Q_5=t(1+s)v+N\) has weight at least three, since
\(t(1+s)=T+T^2+T^3+T^4\). In the second, \(Q_4=v/s\), so
\(N=0\) or \(v/s^2\). Then \(Q_5=N+v/s+v\) has respectively
two or three distinct terms. Neither can be the zero or singleton fifth
slice. All displayed divisions are conditional polynomial identities;
an inadmissible negative exponent already rules out that case.

**Position 4.** The first three singletons must start
\((p,q)=(0,q)\), \((u,v)=(q,0)\): a second B singleton would give a
two-term \(Q_3\). The third folded slice is \(q\). If it is B-only,
then \(Q_4=tq+q/s\) has three terms, impossible for weight two.
Thus \((h,l)=(q,0)\), and

\[
M+sN=tq,\qquad Q_5=tq+N.
\]

If the fourth slice is A-only, then \(N=0,M=tq\), and \(Q_5=tq\)
has weight two. If it is B-only, then \(M=0,N=tq/s\), and

\[
Q_5=tq+tq/s=(T^{-1}+1+T+T^2)q
\]

has four distinct terms whenever this division is polynomially admissible.
If the fourth slice is mixed, \(M,N\) are monomials and \(M+sN=tq\)
forces \(sN\) to be one of the two terms of \(tq\). The exponent of
\(N\) is then at most that of \(q\), strictly below both terms of
\(tq\); hence \(Q_5=tq+N\) has weight three. In all three cases its
weight exceeds one, excluding both a closing zero and a singleton fifth
slice. Equivalently, at a closing zero \(N=tq\) already exhausts the
fourth slice's weight two, forcing \(M=0\), but then \(stq=tq\),
impossible in the polynomial domain.

### Z elimination from the separate equations (87)

**Position 1.** The second singleton makes \(p\) a monomial, and the
first weight two makes \(q\) a monomial. A second A singleton gives
\(Q_3=tq+(1+s)p\) even in parity, impossible. Hence
\((u,v)=(0,sp)\) and \(Q_3=tq+p=F\), with \(p,F\) the distinct
terms of \(tq\). A third B singleton makes \(Q_4=tsp\) have weight
two. A third A singleton has \(sh=F\) and makes \(Q_4=tsp+F\) have
weight three: the terms of \(tsp\) are strictly above the exponent of
\(F\). Neither permits a fourth singleton.

**Position 2.** Parity in \(su+v=sp\) forces \(p=0\), so \(q\) is
a monomial and \(v=su\), with \(u,v\) monomials. The third folded
slice is \(tq+su\), a monomial; thus \(sh\) is zero or a monomial.
But \(Q_4=(1+st)u+sh\) has weight at least two, not one.

**Position 3.** The first two singletons force \(p\) monomial and
\(q=0\). A second B singleton would give odd \(Q_3=p\), impossible
for the weight-two third slice. Therefore \((u,v)=(p,0)\) and
\(Q_3=(1+s)p\). Mixed monomials \(h,l\) would make \(Q_4=p+sh\)
even, impossible. The remaining possibilities are

\[
(h,l)=(0,(1+s)p)\quad\text{or}\quad(p/s+p,0).
\]

In the first, \(Q_4=p\) and \(sM=0\) or \(p\), so
\(Q_5=t(1+s)p+sM\) has at least three terms. In the second,
\(Q_4=sp\) and \(sM=0\) or \(sp\), so \(Q_5=p/s+p+sM\)
has two or three distinct terms. Neither is zero or a monomial.

**Position 4.** The first three singletons force
\((p,q)=(p,0)\), \((u,v)=(0,sp)\), and \(Q_3=p\).
A third A singleton would give \(Q_4=tsp+p\) of weight three, so the
third slice is B-only, \((h,l)=(0,p)\). Thus

\[
sM+N=tsp,\qquad Q_5=tp+sM.
\]

If the fourth slice is A-only, then \(N=0,M=tp\), and
\(Q_5=(1+s)tp\) has four distinct terms. If it is B-only, then
\(M=0,N=tsp\), and \(Q_5=tp\) has weight two. If it is mixed,
\(M,N\) are monomials and \(sM+N=tsp\) forces \(sM\) to be one
of the two terms of \(tsp\). Both possible exponents of \(sM\) are
strictly above those of \(tp\), so \(Q_5=tp+sM\) has three distinct
terms. The separate backward outcomes are therefore four, two, and three,
again excluding both possibilities for the fifth slice.

All four positions have been excluded in each recurrence. Since every
longer gap already has at least one excess unit, this proves (85). ∎

The candidate's four-position argument has thus been checked directly in
both recurrences. In particular the fourth-position weight counts are
\(2,4,3\) for X and \(4,2,3\) for Z, in A-only, B-only, mixed order.
This refines the presentation of the same proposition, not a new distance
claim or a second independent proof certificate. Only symbolic weight
allocations and arbitrary monomial shifts are used; no supports or states
were enumerated.

**Consequence for earlier cheap-exit statements.** The local \(2,1,1\)
prefix examples in Proposition 13 remain valid, but they cannot extend
to an entire longer zero gap with just one excess unit. A length-four
gap with one excess unit has first interior weight one by (79)–(80), so
it cannot be fed by a short run's heavy exit. Length-three gaps have
excess at least two, and (85) covers all remaining lengths. Therefore

\[
\boxed{\text{Every longer gap fed by a short run has }E_D\ge2.} \tag{88}
\]

In particular the full-gap count \(C\) from Propositions 16 and 19 is
always zero. This does not invalidate those conditional inequalities; it
shows that their cheap-full-gap alternative is unrealizable.

## PROPOSITION 24: unreserved run surplus and tight-seventeen structure

**Independent review/formalization pending; outside both frozen drafts.**
For each maximal short run of length \(m\), define its middle surplus
\(\Delta_R=E_R-(m-1)\ge0\), and put \(\Delta=\sum_R\Delta_R\).
Let \(U\) count longer gaps that are neither immediately preceded by a
short run nor a weight-four length-four gap. Let \(Q_{\rm tail}\) count
weight-four length-four gaps that are the final zero gap and have an
on-board slice beyond their ending zero in forcing order. Then

\[
\boxed{E\ge z-1-\varepsilon+\Delta+U+2Q_{\rm tail},\qquad
W\ge18-\varepsilon+\Delta+U+2Q_{\rm tail}.} \tag{89}
\]

**Proof.** For \(z\ge1\), partition into short-run middles, longer-gap
interiors, and tails. If \(G\) is the number of short gaps and \(R_2\)
the number of short runs, their middle excess is exactly
\(G-R_2+\Delta\). Let \(M=z-1-G\) count longer gaps, \(Q\) count
weight-four length-four gaps, and \(I\) count longer gaps immediately
preceded by short runs. The cheap gaps cannot be incoming by (88), so
\(U=M-Q-I\). All noncheap longer gaps cost at least two, whereas the
\(Q\) cheap gaps cost one. Their total excess is at least \(2M-Q\).
If \(T_{\rm tail}\) counts short runs with an on-board tail exit,
\(R_2=I+T_{\rm tail}+\varepsilon\). Those targets cost at least one
excess each. A tail after a final cheap length-four gap instead costs at
least two by (83)–(84); it is disjoint from the preceding type of tail.
Consequently

\[
\begin{split}
E&\ge G-R_2+\Delta+2M-Q+T_{\rm tail}+2Q_{\rm tail}\\
 &=z-1-\varepsilon+\Delta+(M-Q-I)+2Q_{\rm tail}.
\end{split}
\]

This is (89). If \(z=0\), all counts vanish and \(W\ge19\) suffices. ∎

In this allocation every short-run exit into a longer gap is paid inside
that gap using (88). Thus **all** middle surplus \(\Delta\), including
the initial middle's excess, remains unreserved. This is a new allocation;
it must not be added to (66) as if their surplus terms were disjoint.

If a cheap length-four gap is followed by a short run, (83) or (84) makes
that run's seed weight three. Its first middle alone gives
\(\Delta_R\ge2\). Hence this configuration forces \(W\ge19\), or
\(W\ge20\) if \(\varepsilon=0\). It excludes both seventeen and
eighteen. If the cheap gap is followed by a longer gap, that gap has first
weight at least three and is noncheap and unpaired, so it contributes to
\(U\). A cheap final gap with an on-board tail gives \(W\ge20\), since
then \(\varepsilon=0\) and \(Q_{\rm tail}=1\). A cheap gap ending at
the board edge has no such outgoing cost; in that case also
\(\varepsilon=0\), because the last gap is not short.

**Necessary structure at weight seventeen.** Equality \(W=17\) requires
\(\varepsilon=1\), \(\Delta=U=Q_{\rm tail}=0\). No cheap length-four
gap can occur: a following short run would give \(\Delta\ge2\); a
following longer gap would give \(U\ge1\); and if it were the last gap,
\(\varepsilon\) would be zero. Hence every longer gap is noncheap and,
as \(U=0\), is immediately preceded by a short run. The gap sequence
therefore starts with a short run, alternates single longer gaps with
short runs, and ends with the missing-exit short run.

The same proof as (60) applies to every run: \(\Delta_R=0\) forces a
monomial seed and run length at most three. Each nonfinal run is followed
by a longer gap of excess exactly two; any larger excess would make the
global inequality strict. Such a run has length at most two, since a
three-gap monomial run has exit polynomial \(t^3P\) of weight four,
already forcing gap excess at least three. Incoming length-three gaps
are excluded by Proposition 18, so all longer gaps here have length at
least four. The initial tail has no excess left in the equality budget;
it consists of singletons and has length at most five by Proposition 15.
These are necessary conditions, not a construction or a global exclusion
of weight seventeen. The earlier scalar profile with gaps \(6,6,4,2\)
is now excluded by the new polynomial gap costs.

There must be at least one longer gap in a weight-seventeen sequence. If
all gaps belonged to the final short run, its length would be at most
three, leaving an initial tail of at least twelve occupied singleton
slices before its first zero in forcing order. This contradicts
Proposition 15.

At weight eighteen, (89) also limits the cheap length-four cases exactly.
If \(\varepsilon=1\), then \(\Delta+U+2Q_{\rm tail}\le1\). A cheap
gap can only be followed by a longer gap, so \(U=1\), \(\Delta=0\),
and there can be at most one such cheap gap. It cannot be followed by a
short run or an on-board tail, and it cannot end at the terminal edge
because that would make \(\varepsilon=0\). If \(\varepsilon=0\),
then \(\Delta=U=Q_{\rm tail}=0\), and any cheap gap must itself end
at the terminal board edge. Again there is at most one. These are only
necessary arrangements; the exact polynomial constraints in the remaining
two-excess longer gaps are not discharged here.
Proposition 27 below further excludes the \(\varepsilon=1\) cheap-gap
arrangement at weight eighteen; this paragraph records the intermediate
consequences of (89) alone.

## PROPOSITION 25: dyadic packet weight and the seven-gap exclusion

**Independent review/formalization pending; outside both frozen drafts.**
This section imports the binary-digit valuation inequality, and only that
inequality, from `analytical/notes/valuation-energy.md`, Proposition 2:
for a nonzero polynomial \(P\in\mathbb F_2[T]\),

\[
\operatorname{wt}(P)\ge2^{\operatorname{pop}(\nu_1(P))}. \tag{90}
\]

Here \(\nu_1(P)\) is the multiplicity of \(1+T\), and
\(\operatorname{pop}\) counts one bits of a nonnegative integer. The
input has pending independent-review/formalization status. Its proof was
read directly; neither its script nor any support search was run.

For clarity, the proof of (90) is by induction on polynomial degree, not
by inspecting a table of residues. Write
\(P=E(T^2)+T O(T^2)\), with
\(\operatorname{wt}(P)=\operatorname{wt}(E)+\operatorname{wt}(O)\).
At \(T=1+V\),

\[
P(1+V)=(E+O)(1+V^2)+V O(1+V^2).
\]

The two summands have even and odd orders, respectively, so their leading
orders cannot cancel. If \(\nu_1(P)=2h\), then
\(\nu_1(E+O)=h\), and
\(\operatorname{wt}(P)\ge\operatorname{wt}(E+O)\ge2^{\operatorname{pop}(h)}\).
If \(\nu_1(P)=2h+1\), then \(\nu_1(O)=h\) and
\(\nu_1(E+O)>h\), allowing \(E+O=0\). Hence \(\nu_1(E)=h\)
also, and induction gives
\(\operatorname{wt}(P)\ge2\cdot2^{\operatorname{pop}(h)}\).
The nonzero polynomials to which induction is applied have smaller degree;
constants start the argument. These are exactly the two binary-digit
identities needed for (90).

Put \(t=T(1+T)\) and \(\beta=\nu_1(P)\). Then
\(\nu_1(t^jP)=\beta+j\). For any \(a\ge0\), this gives

\[
\boxed{\sum_{j=0}^{6}\operatorname{wt}(t^{a+j}P)\ge19.} \tag{91}
\]

**Proof without residue enumeration.** For any integer \(n\ge0\), its
lowest three binary bits give
\(2^{\operatorname{pop}(n)}\ge2^{\operatorname{pop}(n\bmod8)}\).
The seven consecutive integers \(\beta+a,\ldots,\beta+a+6\) have
seven distinct residues modulo eight. Summing over all three-bit strings
gives

\[
\sum_{r=0}^{7}2^{\operatorname{pop}(r)}=(1+2)^3=27.
\]

Each bit contributes either a factor one or a factor two; this proves the
sum without listing the residues. The omitted residue contributes at most
\(2^3=8\), leaving at least \(27-8=19\). Apply (90) termwise to the
seven distinct physical polynomials. ∎

**Physical seven-gap consequence.** In either sector, choose any seven
consecutive short gaps within a short run. Their seven middle polynomials
are exact consecutive powers of \(t\) by (38) or (39), and their physical
weights are precisely those coefficient weights, since each middle has
only its active block. The packet therefore costs at least nineteen.

Including its eight zero slices, this subrun occupies fifteen consecutive
board positions. There are four positions outside, split into tails of
lengths \(L,R\) with \(L+R=4\). Each tail is adjacent to an empty
endpoint of the subrun. Adjacent nonemptiness therefore requires at least
\(\lceil L/2\rceil\) and \(\lceil R/2\rceil\) qubits in those
tails: pair consecutive positions starting at their common zero boundary,
so the nearest tail slice is forced occupied. The outside positions are
disjoint from all seven middle slices, and their total cost is at least
two. Consequently

\[
\boxed{\text{A short run of length at least seven forces }W\ge21.}
\tag{92}
\]

This argument applies equally to a seven-gap subrun of a longer run; it
does not weaken to twenty there. Any additional middle slices are among
the four outside positions and are counted only by the outside bound,
not charged again. The direction of propagation does not affect this
geometric tail count. A missing exit at X row 19 or Z column -1 creates
no exception to (92), because both endpoints of the chosen subrun are
physical zero slices. Width nineteen also implies that a run has at most
nine gaps, from its span \(2m+1\), but no list of possible run placements
is needed.

**Six gaps with an on-board exit, independently of the surplus budget.**
For a six-gap run with an actual exit target, the six middle polynomials
are \(P,tP,\ldots,t^5P\), and the exit's folded polynomial is \(t^6P\).
Its physical weight is at least that coefficient weight, so these seven
disjoint slices again cost at least nineteen. They span fourteen positions
including the seven intervening/boundary zeros. There are five outside
positions: the initial tail is attached to a zero and costs at least
\(\lceil L/2\rceil\), while the tail after the occupied exit costs at
least \(\lfloor R/2\rfloor\). As \(L+R=5\), their sum is at least
two. Hence such a run also gives \(W\ge21\).
This last argument does require an on-board exit; the case with a missing
exit is handled below by a different, explicit surplus allocation. No
degree-18 restriction is imposed on the folded exit polynomial, which can
have degree up to 20.

## PROPOSITION 26: shorter packets and the unreserved run budget

**Independent review/formalization pending; outside both frozen drafts.**
The same binary-digit argument gives, for every nonzero \(P\),

\[
\boxed{\sum_{j=0}^{3}\operatorname{wt}(t^jP)\ge9,\qquad
\sum_{j=0}^{5}\operatorname{wt}(t^jP)\ge15.} \tag{93}
\]

For four terms, the lowest two bits traverse all four residues and their
total is \((1+2)^2=9\). For six terms, the lowest three bits omit exactly
two of the eight residues. At most one residue has all three bits equal
to one, contributing eight; every different residue contributes at most
four. Thus the two omitted contributions total at most twelve, leaving
\(27-12=15\). This is again an inequality for arbitrary \(\nu_1(P)\),
not a finite table of valuations.

Let a short run have \(m\) middle polynomials, middle weight \(W_R\),
and the surplus used in Proposition 24,

\[
\Delta_R=E_R-(m-1)=W_R-(2m-1).
\]

For \(m\ge4\), the first four middles cost at least nine, and each
remaining middle has weight at least two. Hence
\(W_R\ge9+2(m-4)=2m+1\) and \(\Delta_R\ge2\).
For \(m\ge6\), the first six cost at least fifteen, giving
\(W_R\ge15+2(m-6)=2m+3\) and \(\Delta_R\ge4\).
For \(m\ge7\), (91) similarly gives \(\Delta_R\ge6\).

These quantities are already part of the **unreserved** sum \(\Delta\)
in (89). Substituting them there, rather than adding packet weight to an
already counted total, gives

\[
\begin{array}{ll}
\text{some run has }m\ge4:&W\ge20-\varepsilon\ge19,\\
\text{some run has }m\ge6:&W\ge22-\varepsilon\ge21,\\
\text{some run has }m\ge7:&W\ge24-\varepsilon\ge23.
\end{array} \tag{94}
\]

The stronger bounds in (94) explicitly depend on the research gap-cost
and allocation Propositions 22–24 as well as the valuation input. They
are not consequences of simply adding a packet cost to the frozen
seventeen bound. In particular the missing-exit six-gap case in (94)
uses its four surplus middle units; it does not invent an untested exit.

**Consequences for the remaining run lengths.**

- If \(W\le20\), every short run has length at most five.
- If \(W\le20\), at most one run has length four or five: two such
  disjoint runs would give \(\Delta\ge4\), hence \(W\ge21\).
- If \(W\le18\), every short run has length at most three.
- If \(W\le19\) and \(\varepsilon=0\), every short run has length
  at most three. A four- or five-gap run under \(W\le19\) requires
  the missing-exit configuration somewhere in the sequence.

For several disjoint short runs, these surplus bounds may be summed over
their distinct middle sets: each run of length four or five contributes
at least two to \(\Delta\), and each run of length six or more contributes
at least four. Overlapping windows within a single run may not be summed
without a separate partition. None of these statements uses a linear
valuation/weight estimate; \(t^8=T^8+T^{16}\) still has weight only two.
The bounds concern packets, not monotone growth of an individual slice. ∎

## PROPOSITION 27: a cheap length-four gap forces more cost in a following longer gap

**Independent review/formalization pending; outside both frozen drafts.**
The concrete current gap conclusions are (79)–(84) and (85): the unique
one-excess length-four forms have directional weights \(1,1,2\), their
tested outgoing folded polynomial has weight three, and every gap of
length at least five has excess at least two. The following further
constraint uses those exact outgoing polynomials.

After a one-excess length-four gap, three consecutive outgoing slices in
forcing order cannot have physical weights \(3,1,\le1\). The last
slice may therefore be either a proposed singleton or a closing zero.

**X proof.** Put \(s=T^2\), \(t=T+T^2\). If \(z\) is the monomial
in (79), write the next three slices after the ending zero as
\((p,q),(u,v),(h,l)\). Their equations are

\[
p+s q=(1+T+T^2)z,\qquad
u+s v=q,\qquad h+s l=tp+q+v. \tag{95}
\]

Assume the first two physical weights are three and one. The second
equation makes \(q\) a monomial, so \(p\) has weight two. In the first
equation, the monomial \(sq\) must cancel exactly one of the three
terms on the right, giving

\[
sq=\lambda z,\quad p=(1+T+T^2+\lambda)z,
\qquad\lambda\in\{1,T,T^2\}. \tag{96}
\]

This is support matching against three fixed terms with an arbitrary
monomial shift, not an enumeration of physical supports. If the second
slice is A-only, then \(v=0\), and \(tp+q\) is, respectively,

\[
(T^{-2}+T^2+T^4)z,\quad
(T^{-1}+T+T^2+T^3+T^4)z,\quad
(1+T+T^3)z.
\]

These have three, five, and three distinct terms. If the second slice is
B-only, then \(v=q/s\). Now \(tp+q+q/s\) has even parity. It is
nonzero: the exponent of \(q/s\) is at most \(\deg z-2\), below both
the exponent of \(q\) and every exponent of \(tp\), the latter being
at least \(\deg z+1\). Thus it has weight at least two. In either case
the folded third slice cannot have weight at most one. Divisions here are
conditional polynomial identities; a negative actual exponent excludes
that allocation rather than permitting a Laurent physical slice.

**Z proof from its separate equations.** Let \(z\) be the monomial in
(80), and name the next three slices in decreasing column order. Their
equations are instead

\[
sp+q=(1+T^5+T^6)z,\qquad
su+v=sp,\qquad sh+l=tq+p+su. \tag{97}
\]

Physical weights three and one force \(p\) monomial and \(q\) of
weight two. Hence

\[
sp=\lambda z,\quad q=(1+T^5+T^6+\lambda)z,
\qquad\lambda\in\{1,T^5,T^6\}. \tag{98}
\]

If the second slice is B-only, \(u=0\), and \(tq+p\) is respectively

\[
(T^{-2}+T^6+T^8)z,\quad
(T+T^2+T^3+T^7+T^8)z,\quad
(T+T^2+T^4+T^6+T^7)z.
\]

These have three, five, and five distinct terms. If the second slice is
A-only, then \(u=p\), and the folded third slice is
\(tq+(1+s)p\), of even parity. For \(\lambda=1\), its two summands
have disjoint supports \(\{6,8\}+\deg z\) and
\(\{-2,0\}+\deg z\). For either other value of \(\lambda\), the
first summand has four terms and the second has two, so they cannot cancel
to zero. In all cases the resulting weight is at least two, proving the
backward obstruction independently. ∎

**Tested ranges.** If the cheap X gap ends at zero \(K\), the equations
in (95) are at \(K+1,K+2,K+3\). They are available whenever the next
gap has length at least three and lies on the board. For Z, a cheap gap
ending at zero \(K\) gives (97) from equations at \(K+1,K,K-1\).
A following gap of length at least three in decreasing order ensures
\(K\ge3\), so these are all tested. Thus the conclusion also covers a
following length-three gap that closes at the board edge. It makes no
claim when there are fewer than three further physical positions.

Consequently, if the next gap is longer than a short gap, its interior
excess satisfies

\[
\boxed{E_{\rm next}\ge3.} \tag{99}
\]

Indeed its first slice has odd physical weight at least three by (83) or
(84). If that weight exceeds three, it is at least five and already gives
four excess units. Otherwise, an excess of at most two in the entire
following gap would force weights three and one on its first two slices,
and weight zero or one on the third, contrary to (95)–(98). This argument
works for a following gap of length three or any larger length.

**Disjoint accounting refinement.** Let \(D\) count cheap length-four
gaps immediately followed by a longer gap. Each following gap is unpaired
with a short run, is noncheap, and is one of the gaps counted by \(U\)
in Proposition 24. Distinct transitions have distinct following-gap
interiors. The proof of (89) reserved two excess units in each such gap;
(99) supplies at least one more, in that same gap above its reservation.
Thus a valid replacement for (89) is

\[
\boxed{W\ge18-\varepsilon+\Delta+U+D+2Q_{\rm tail},
\qquad D\le U.} \tag{100}
\]

This does not add overlapping inequalities: it strengthens the actual
long-gap contribution from two to three on the \(D\) distinct regions
in the proof of (89). If a cheap gap is followed by a short run, its
weight-three seed instead contributes \(\Delta\ge2\); if it is
followed only by an on-board tail, \(2Q_{\rm tail}\ge2\). Therefore
every cheap length-four gap with a tested outgoing slice forces
\(W\ge20-\varepsilon\ge19\). In particular, at weight eighteen any
cheap length-four gap must end at the terminal board edge, where no
outgoing slice is tested and \(\varepsilon=0\). The former possibility
of a cheap gap followed by an unpaired longer gap at weight eighteen is
now excluded by the additional \(D\) cost.

No unconditional eighteen, nineteen, or twenty lower bound is asserted:
sequences with no cheap gap and all longer-gap excesses at least two
remain to be controlled. Neither frozen draft is modified by this result.

## PROPOSITION 28: the initial singleton tail before a monomial short-run seed

**Independent review/formalization pending; outside both frozen drafts.**
This section concerns only the initial tail, not the interiors of the
excess-two longer gaps assigned to `tight-gap-transport.md`.
At \(W=17\), Proposition 24 shows that the first zero is followed by a
short run with a monomial seed, while every slice before that zero is a
singleton. Let \(\tau\) be the number of those initial singleton slices,
in the forcing direction. Then

\[
\boxed{0\le\tau\le2.} \tag{101}
\]

Moreover their blocks and monomials are forced as follows. Write \(P=T^a\)
for the first short-middle polynomial, and \(s=T^2,t=T+T^2\).

| Direction | \(\tau\) | Initial tail, in forcing order | First zero | First short middle |
|---|---:|---|---:|---|
| X | 0 | none | row 0 | row 1: \((P,0)\) |
| X | 1 | row 0: \((0,P)\) | row 1 | row 2: \((P,0)\) |
| X | 2 | rows 0,1: \((0,P),(0,P)\) | row 2 | row 3: \((P,0)\) |
| reflected Z | 0 | none | column 18 | column 17: \((0,P)\) |
| reflected Z | 1 | column 18: \((P,0)\) | column 17 | column 16: \((0,P)\) |
| reflected Z | 2 | columns 18,17: \((sP,0),(P,0)\) | column 16 | column 15: \((0,P)\) |

These are necessary local forms; no full-sequence extension is asserted.
In the last row of the table, physical degree additionally requires
\(a\le16\); otherwise the bound is \(a\le18\).

**X proof.** Let the first zero be row \(k=\tau\), and the following
short middle be \((P,0)\) at \(k+1\). There is another zero at \(k+2\).
If \(k\ge1\), the tested equation at \(k+1\) gives

\[
P=t a_{k-1}+b_{k-1}. \tag{102}
\]

The slice \(k-1\) is a singleton. An A-only singleton would make the
right side have weight two, so it must be \((0,P)\). If \(k\ge2\),
the equation at the zero row \(k\) gives
\(t a_{k-2}+b_{k-2}=P\), forcing the preceding singleton to be
\((0,P)\) also.

If \(k\ge3\), apply the equation at \(k-1\), now an interior B-only
singleton. It gives

\[
t a_{k-3}+b_{k-3}=(1+s)P. \tag{103}
\]

The left side, coming from a singleton, is either one monomial or two
monomials with consecutive exponents. The right side is two monomials
whose exponents differ by two. Equality is impossible. Hence \(k\le2\),
and the preceding deductions give all three X rows of the table.
The equation at \(k+1\) was used only for \(k\ge1\), at \(k\) only
for \(k\ge2\), and at \(k-1\) only for \(k\ge3\). Thus no equation
at index 0 or 1 has been assumed.

**Z proof from its actual recurrence.** Let the first zero in decreasing
column order be \(K=18-\tau\). The first short middle at \(K-1\)
is \((0,P)\), with a second zero at \(K-2\), so \(K\ge2\).
If \(\tau\ge1\), the equation at \(K+1\) gives

\[
P=t b_{K+1}+a_{K+1},
\]

forcing the closest tail singleton to be \((P,0)\). If \(\tau\ge2\),
the equation at \(K+2\) gives

\[
t b_{K+2}+a_{K+2}=sP,
\]

forcing the preceding singleton to be \((sP,0)\). If \(\tau\ge3\),
the equation at \(K+3\) then gives

\[
t b_{K+3}+a_{K+3}=s(1+s)P. \tag{104}
\]

Again a singleton produces either one monomial or two consecutive ones,
whereas the right side has exponent difference two. This is impossible.
Each used index lies between \(K+1\ge3\) and 18; it is invoked only
when that many physical tail slices exist. This proves (101) and the
separate Z forms. ∎

This argument does not need to classify any longer gap. In particular,
the exclusion of tails of length three or more is a boundary consequence
of singleton weights and a monomial first short seed, not an assumed
global monomial-charge condition.

## PROPOSITION 29: four remaining tight-seventeen boundary forms

**Independent review/formalization pending; outside both frozen drafts.**
Use the charge algebra and monomial-period criterion (67), with the same
pending-review factor dependency stated in Proposition 20. Let the first
short-run seed have exponent \(a\), and let the final missing-exit run
have length \(m\) and monomial seed exponent \(b\). Under \(W=17\),
Propositions 24 and 28 give

\[
0\le\tau\le2,\quad1\le m\le3,\quad
0\le a\le18,\quad0\le b\le18-2(m-1). \tag{105}
\]

The complete necessary boundary classification is:

| Sector | Initial tail length \(\tau\) | Final run length \(m\) | Initial physical data | Final seed | Exponent range |
|---|---:|---:|---|---|---|
| X | 0 | 1 | row 0 zero; A at row 1 is \(y^a\) | A at row 17 is \(y^{a-3}\) | \(3\le a\le18\) |
| X | 1 | 2 | B at row 0 is \(y^a\); row 1 zero; A at row 2 is \(y^a\) | A at row 15 is \(y^{a-16}\) | \(16\le a\le18\) |
| reflected Z | 0 | 1 | column 18 zero; B at column 17 is \(x^a\) | B at column 1 is \(x^{a+13}\) | \(0\le a\le5\) |
| reflected Z | 1 | 2 | A at column 18 is \(x^a\); column 17 zero; B at column 16 is \(x^a\) | B at column 3 is \(x^{a-3}\) | \(3\le a\le18\) |

Thus tail length two and final run length three are excluded. These are
necessary endpoint conditions only; they do not construct or exclude the
intervening excess-two gaps.

### Labels extracted from actual singleton short middles

For X, a short-middle A monomial \(y^a\) at row \(j\), preceded by a
zero row, has charge label \([x^jy^a]\). To verify this without a
boundary assumption, truncate the operator to rows below cut \(j+1\).
Its outgoing syndrome tail is \(x^{j+2}t y^a\); since \(x^2t=1\)
in the charge algebra, its class is \([x^jy^a]\). The truncated full
syndrome lies in \((f,g)\), so its outgoing tail class equals the low
boundary charge. This is the exact conserved-cut identity, applied to
the specified physical middle.

For reflected Z, write the same full syndrome \(S=ga+fb\) in columns.
At a column cut \(k\), its outgoing tail from the columns below the cut is

\[
y^k(s a_{k-1}+s a_{k-2}+b_{k-2})
 +y^{k+1}(s a_{k-1}+b_{k-1}),\qquad s=x^2. \tag{106}
\]

This follows by extracting the last two columns in the products with
\(g=1+s y+s y^2\) and \(f=x+x^2+y^2\). For a B-only short middle
\(x^a\) at column \(j=k-1\), with its preceding column empty, (106)
is simply \(y^{j+2}x^a\). Its class again equals the low-column charge,
because the truncated full syndrome is in \((f,g)\). The extra shift
of two in this Z label is essential; it is not an X/Z symmetry assumption.

Both the first and final run seeds are such physical monomial middles.
Consequently their charge labels are equal:

\[
\begin{array}{ll}
\mathrm X:&[x^{\tau+1}y^a]=[x^{19-2m}y^b],\\
\mathrm Z:&[x^a y^{19-\tau}]=[x^b y^{2m+1}].
\end{array} \tag{107}
\]

All cuts used here lie between 2 and 19. This derivation remains valid
when the physical initial tail has two qubits: their summed boundary
charge is forced to equal the first seed's label by the recurrence.
It does not replace an arbitrary two-label boundary by a monomial.

### X inverse-lattice bounds

Put \(d=18-2m-\tau\). Then \(10\le d\le16\), and (107) says
\((d,b-a)\in\Lambda\). Write this as
\((d,b-a)=(16n+3q,-3n+13q)\). Since \(|b-a|\le18\),

\[
0<\frac{76}{217}\le n=\frac{13d-3(b-a)}{217}
\le\frac{262}{217}<2.
\]

Thus \(n=1\), \(d\equiv1\pmod3\), and
\(b-a=(13d-217)/3\). The transverse width bound also gives
\(13d\ge217-54=163\), hence \(d\ge13\). Therefore \(d\) is
13 or 16. The equation \(2m+\tau=18-d\), with (105), gives only

\[
(\tau,m,d,b-a)=(0,1,16,-3)
\quad\text{or}\quad(1,2,13,-16). \tag{108}
\]

The physical exponent ranges in the table follow from nonnegative \(b\)
and (105). This uses interval bounds and integer congruences, not a
search over lattice points or supports.

### Separate Z inverse-lattice bounds

For Z, (107) gives \((a-b,d)\in\Lambda\), with the same \(d\) range.
The other inverse coordinate is now the useful one:

\[
0<\frac{106}{217}\le q=\frac{3(a-b)+16d}{217}
\le\frac{310}{217}<2.
\]

Thus \(q=1\), \(d=13-3n\), and \(a-b=16n+3\).
The bound \(|a-b|\le18\) implies
\(-21/16\le n\le15/16\), so the integer \(n\) is \(-1\) or 0.
These yield \(d=16\) or 13 respectively. Solving for \(\tau,m\)
as above gives

\[
(\tau,m,d,b-a)=(0,1,16,13)
\quad\text{or}\quad(1,2,13,-3). \tag{109}
\]

This proves the Z rows of the table with the actual oriented lattice
coordinates. In particular the sign and magnitude of the transverse shift
differ from X. No axis-exchange invariance of \(\Lambda\) was used. ∎

### Boundary handoff to excess-two gap transport

The following interface uses only the already established tight-budget
structure and the new boundary analysis, without duplicating the gap
classification assigned to Ampere:

- The initial tail has length zero or one, with exactly the data in the
  table. Thus the first two slices in forcing order contain exactly one
  qubit. For X this is \(w_0+w_1=1\); for reflected Z it is
  \(w_{18}+w_{17}=1\). This condition is now derived for tight seventeen,
  not imposed on arbitrary cycles or arbitrary charges.
- Every short-run seed is a monomial. Nonfinal short runs have length
  one or two; the final missing-exit run has length one or two as selected
  by the table. The sequence alternates short runs and single longer gaps,
  every longer gap having excess exactly two and length at least four.
  At least one longer gap occurs, by Proposition 24.
- If the initial run has length \(\ell\), width gives
  \(a+2(\ell-1)\le18\). In the X tail-one case, \(\ell=2\) therefore
  forces \(a=16\); for \(a=17,18\) that initial run has length one.
- In forcing order the distance from the first zero to the terminal zero
  is \(18-\tau\). Short gaps contribute even lengths. Hence the sum
  of the longer-gap lengths has parity \(\tau\). In either tail-one
  case, at least one longer gap has odd length, necessarily at least five.
  In a tail-zero case, the number of odd-length longer gaps is even.

The shifts in (108)–(109) are constraints on the monomial seeds that any
successful excess-two transport classification must meet. No feasibility
claim is made for any table row, and no global exclusion of seventeen,
eighteen, nineteen, or proof of twenty follows from this boundary work alone.
All results remain PROPOSITION pending further independent review and Lean
formalization. Neither frozen draft nor `tight-gap-transport.md` is changed.

## Updated logical consequence and limits of the counting mechanism

**PROPOSITION — independent review/formalization pending.** Using the
charge conservation and completeness of `algebra.md`, Propositions 7–8,
the explicit finite rectangular model satisfies

\[
\boxed{d_X\ge17,\qquad d_Z\ge17,\qquad d_{\rm Pauli}\ge17.} \tag{33}
\]

Each nontrivial sector class has nonzero charge, hence adjacent-slice
nonemptiness in its respective coordinates. Apply Proposition 14. For Z,
reflection/block exchange preserves weight and transports the original
cycle equations to (15); its reflected charge vanishes on reflected Z
stabilizers. Thus the bound applies to every representative modulo the
appropriate stabilizers, just as in the X argument following (14).
Any nontrivial CSS Pauli class has a nontrivial X or Z component, whose
weight does not exceed the union support of the Pauli. This proves the last
bound. All charge and input-identification dependencies retain their stated
review gaps. The frozen self-contained draft still proves only fifteen;
this research improvement is not part of that review packet.

**Earlier counting obstruction, now excluded by a new local lemma.** Give X rows weight
zero exactly at \(1,6,11,16,18\), and every other row weight one. This is a
scalar weight profile with \(W=14,z=5,E=0\). It obeys adjacent nonemptiness;
its zero gaps have lengths \(5,5,5,2\). Its only length-two gap has middle
17, precisely the untested forward exception. There are no length-three or
length-four gaps. Thus it satisfies all the gap-cost and branching-weight
conditions used in Proposition 8. Reversing the indices gives a Z profile
with zeros \(0,2,7,12,17\), whose only short-gap middle is the backward
exception 1. It satisfies the corresponding Z conditions as well.

These remain explicit counterexamples to inferring weight fifteen (or twenty)
from **Proposition 8's scalar conditions alone**. They are not polynomial
cycles. Proposition 9 now excludes them: each has three length-five gaps
with four singleton interiors, whereas each such gap needs positive excess.
Equivalently, they have \(L=3,E=0\), violating the new inequality
\(2H+K+L\le E\). This identifies the actual new cancellation mechanism
that permits fifteen, rather than merely reweighting the old constraints.
No argument reaching twenty is supplied.

The degree cap and literal check ranges identify these polynomial problems
with the code. The inequalities still do not exploit all of the width-19
constraint. A universal assertion that incoming signed overlaps are paid
for by disjoint excess remains unproved and is **CONJECTURE** if proposed.
Distance twenty remains **CONJECTURE**; no extension to punctured 566 is
asserted.

Validation: hand derivation of both distinct recurrences and their local
identities; direct substitution of the local examples; explicit endpoint
checks (forward exception 17 versus backward exception 1); excess
multiplicity accounting in (25)–(26) and (32); and the directional tested
indices \(k+2,k+3,k+4\) versus \(R,R-1,R-2\) for Proposition 9;
separate derivations of (44) and (46), parity and factorization checks for
(45) and (47), direct substitution of both multiterm-feed examples, and
the baseline/extra-unit partition in Proposition 14; the separate feed-parity
arguments and weight-five equality cases in (62)–(65); and the disjoint
run-plus-gap refinements in (66); exact endpoint syndrome extraction in
(69); the inverse-lattice interval and congruence argument in (71)–(72);
and the odd-channel unrolling and extreme-coefficient arguments in (75)–(78);
separate verification of the length-four equality forms in (79)–(82),
the tested outgoing indices in (83)–(84), and all four symbolic heavy-position
contradictions in (86)–(87); and the disjoint partition giving (89).
The even/odd proof of the valuation inequality was read in
`valuation-energy.md`; the dyadic packet sums, attached-tail occupancy
bounds, and substitution into the already unreserved \(\Delta\) budget
were checked by hand in Propositions 25–26. Neither that source note nor
its arithmetic-check script was modified or executed.
The outlet-polynomial substitutions (95)–(98), their tested indices, and
the disjoint following-gap reservation in (99)–(100) were also checked by hand.
The initial-tail equations (102)–(104), separate column-cut formula (106),
and both inverse-lattice interval arguments (108)–(109) were checked directly.
This boundary work neither reads nor modifies Ampere's gap-transport file.
Only the stated factor propositions were imported from `charge-factors.md`;
that note and its symbolic script were not changed or executed. Both frozen
source hashes were rechecked without modifying either draft.
No enumeration or Lean was run.
Independent review and formalization remain outstanding for every proposition.
