#set page(paper: "a4", margin: 22mm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.1")
#let wt = math.op("wt")

#align(center)[
  #text(17pt, weight: "bold")[Planar 722: research outside the review draft]
  #v(5pt)
  Recurrences, weight bounds, and deferred quantum interpretation \
  Research notes · 11 November 2026
]

*Status and scope.* All derived claims are PROPOSITION, with the named gap
independent review/formalization pending. Distance 20 is CONJECTURE.
None is THEOREM (refereed complete). These notes are not part of the frozen
DRAFT.typ review packet and are not eligible for a final PROOF until fully
refereed and formalized. Proposition numbering 3 and 4 is retained from the
original draft to preserve references in research discussions.

*Conventions.* Use the explicit finite model of DRAFT.typ:
$F=bb(F)_2$, $Q={0,dots,18} times {0,dots,18}$, $V=F^722$,
$f=x+x^2+y^2$, $g=1+x^2 y+x^2 y^2$. The two qubit blocks are A and B.
The row spaces of the truncated X and Z check matrices are $S_X,S_Z$.
Weight counts physical coefficients; $P$ restricts to $Q$.

= A new physical-weight recurrence

*PROPOSITION 3 (forced propagation; independent review/formalization pending).*
For an X operator $(u,v)$ in $V$, write
$u=sum_(i=0)^18 u_i (y)x^i$ and $v=sum_(i=0)^18 v_i (y)x^i$.
It is a cycle, meaning orthogonal to every Z row, if and only if
$ u_i=t u_(i-2)+F_i quad (2<=i<=18), $
where
$ t=y+y^2, quad F_i=v_(i-1)+v_(i-2)+y^2 v_i. $
In particular, for $r=0,1$ and $1<=m<= floor((18-r)/2)$,
$ u_(r+2m)=t^m u_r+sum_(ell=1)^m t^(m-ell) F_(r+2ell). $

*Proof.* The overlap with the Z row at $(i,j)$ is the coefficient of
$x^i y^j$ in $g u+f v$. Its possible second exponents all lie between 0
and 20, exactly the retained Z anchor range. Thus vanishing of the retained
syndrome is equivalent to vanishing of entire polynomial slices for
$i=2,dots,18$. Expanding that coefficient gives the first identity.
For the second, the case $m=1$ is the first identity; substituting the
formula for $m-1$ gives the stated sum, proving it by induction. $square$

*PROPOSITION 4 (one-block weight bound; independent review/formalization pending).*
Every nonzero X cycle supported on A alone has physical weight at least 29.
This is a bound on all such cycles, without a logical nontriviality assumption.
The value 29 is attained by a cycle.

*Proof.* With $v=0$, the two parity channels are
$ u_(2m)=t^m u_0 quad (0<=m<=9), quad
  u_(1+2m)=t^m u_1 quad (0<=m<=8). $
If $u_0$ is nonzero, the degree of $u_18=t^9 u_0$ is $18+"deg" u_0$,
by the elementary polynomial fact in DRAFT.typ. It is at most 18, so $u_0=1$. If $u_1$ is nonzero,
the same reasoning at row 17 gives $"deg" u_1<=2$. Conversely these seed
constraints suffice: all propagated slices have nonnegative degrees at
most 18, and the displayed recurrence ensures the cycle equations.

Multiplication by $y^m$ does not change coefficient count, so it suffices
to count $(1+y)^m p$. Up to a monomial factor, the nonzero polynomials of
degree at most two have exactly the four forms
$1$, $1+y$, $1+y^2=(1+y)^2$, and $1+y+y^2$.
Indeed a one-term seed is a monomial; a two-term seed has exponent
difference 1 or 2; a three-term seed must have all degrees 0,1,2.
The relevant coefficient counts are as follows.

#table(
  columns: (1.5fr, 1fr, 1fr, 1fr, 1fr),
  align: center,
  table.header([$m$], [$p=1$], [$p=1+y$], [$p=1+y^2$], [$p=1+y+y^2$]),
  [0], [1], [2], [2], [3],
  [1], [2], [2], [4], [2],
  [2], [2], [4], [2], [4],
  [3], [4], [2], [4], [4],
  [4], [2], [4], [4], [6],
  [5], [4], [4], [8], [4],
  [6], [4], [8], [2], [6],
  [7], [8], [2], [4], [8],
  [8], [2], [4], [4], [6],
  [Sum], [29], [32], [34], [43],
)

For completeness the table is a small polynomial identity calculation:
in characteristic two $(1+y)^(2^a)=1+y^(2^a)$, as follows by repeated
squaring and cancellation of cross terms. Expressing $m$ in binary
therefore gives $(1+y)^m=product_(a: "bit"_a(m)=1)(1+y^(2^a))$.
Distinct subsets give distinct exponents, namely the integers whose binary
bits are subsets of those of $m$. This proves the first column. The next
two columns use exponents $m+1$ and $m+2$. For the last column take the
symmetric difference of that exponent set with its translates by 1 and 2.
Explicitly its supports, for $m=0,dots,8$, are
```
{0,1,2}; {0,3}; {0,1,3,4}; {0,2,3,5};
{0,1,2,4,5,6}; {0,3,4,7}; {0,1,3,5,7,8};
{0,2,3,4,5,6,7,9}; {0,1,2,8,9,10}.
```
These explicit expansions verify every entry without any distance search.
For the even channel one more slice is needed: at $m=9$ the seed 1 gives
four coefficients. Thus its nonzero weight is $29+4=33$. The two channels
occupy disjoint rows, so their weights add. A nonzero odd channel has weight
at least 29, and a nonzero even channel has weight 33. This proves the bound.
Taking $u_0=0,u_1=1$ attains 29, explicitly
$ u=sum_(m=0)^8 x^(1+2m)y^m (1+y)^m, quad v=0. $
No claim that this cycle is a nontrivial logical is needed or made. $square$

= Distance-20 mission: what this checkpoint changes

*CONJECTURE.* Both nontrivial logical sectors of the explicit finite model
have minimum weight at least 20. the main proposition in DRAFT.typ does not imply this.

Proposition 4 excludes all A-only X cycles of weights 1 through 28.
Hence any hypothetical X logical of weight below 20 must involve the B
block. Proposition 3 identifies exactly how that block can suppress the
unforced growth: each $v_i$ contributes $y^2 v_i$ to $F_i$ and contributes
$v_i$ to each of $F_(i+1)$ and $F_(i+2)$ when those indices are retained.
Cancellation must be charged to these physical B coefficients; merely
counting nonzero slices of the homogeneous recurrence would be invalid.

The next mathematical target is a cancellation inequality for the forced
recurrence, modulo the X check space, with cost
$sum_(i=0)^18 (wt(u_i)+wt(v_i))$. It must rule out nontrivial mixed-block
cycles of cost at most 19, and an opposite-sector argument is also needed.
This target is open. It is more specific than a boundary-quotient dimension
calculation: the transfer multiplier, seed degree constraints, forcing
positions, and an exact unforced weight bound are now explicit. No
exhaustive-search certificate, UFD bulk argument, or Lean computation is
part of this draft.

== Separation from input recognition

The definition and all propositions above stand independently of external
data. The companion geometry notes record a direct sparse match to the
submitted 722 matrices and list the upstream revision and input hash.
That match is graded PROPOSITION with independent replay pending. It is
not a hypothesis of the main proposition in DRAFT.typ and is not used in its proof. Likewise
the submitted weight-20 witness is an upper bound and supplies no part of
the conjectured lower bound. This draft is an analytic checkpoint toward
distance 20, not a completed distance proof.


= Deferred quantum interpretation

*PROPOSITION (independent review and formalization bridge pending).*
Assuming the finite-model commutation and ranks from DRAFT.typ, the common
positive stabilizer eigenspace has complex dimension $2^8$. The proof below
is preserved for later use. No formal bridge from the binary quotient to
this Hilbert-space construction has been established in this task; it is
therefore excluded from the review draft.

For the quantum interpretation, take the complex Hilbert space with
orthonormal basis $e_q$, indexed by $q$ in $F^722$. Define
$ X(u)e_q=e_(q+u), quad
  Z(v)e_q=(-1)^(v dot q)e_q. $
These formulas imply $Z(v)X(u)=(-1)^(u dot v)X(u)Z(v)$. Since the two
row spaces are orthogonal, the operators $X(u)Z(v)$ for
$(u,v)$ in $S_X times S_Z$ form a commuting group under addition of labels.
Their average
$ E=2^(-714) sum_(u in S_X) sum_(v in S_Z) X(u)Z(v) $
is a projection onto the common positive eigenspace: each group element
fixes the average, while on a vector fixed by all elements the average acts
as identity. In particular $E^2=E$. A nonidentity term has trace zero.
If $u!=0$, it permutes every basis vector to a different one. If $u=0$
and $v!=0$, pair basis labels $q$ and $q+e_j$ at a coordinate where $v_j=1$;
their diagonal signs cancel. The identity term has trace $2^722$.
Thus $"tr" E=2^8$. Finally any idempotent splits the space as its image
plus kernel, since $w=E w+(w-E w)$ and their intersection is zero; in the
resulting basis its trace equals its image dimension. Trace is independent
of basis: direct summation gives $"tr"(A B)="tr"(B A)$, hence conjugation
by any invertible change-of-basis matrix preserves it. This proves the
deferred quantum dimension assertion. $square$
