#set page(paper: "a4", margin: (x: 22mm, y: 20mm), numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#let F = $bb(F)_2$

#align(center)[
  #text(size: 17pt, weight: "bold")[Boundary charge proves distance at least nine]
  #v(4pt)
  An explicit rectangular CSS model on 722 qubits \
  Frozen document-review checkpoint v1 · 11 November 2026
]

*Claim grades.* THEOREM means refereed complete; PROPOSITION means a claim
with a named gap; CONJECTURE means an unproved mathematical claim; FALSE
means a refuted claim. Every result proved in this document has grade
*PROPOSITION*, with the named gap *independent review/formalization pending*.
This source and its matching PDF are the checkpoint for three independent
hostile document-only reviewers; their reviews are not yet completed.
No claim is graded THEOREM. The word “proof” below describes the supplied
mathematical argument, not a completed referee report or a Lean replay.

= Main proposition and explicit model

*PROPOSITION 1 (main result; independent review/formalization pending).*
For the two rectangular check matrices defined in this section,
$
H_X H_Z^T=0, quad
"rank"(H_X)="rank"(H_Z)=357, quad k=8,
$
and both sector distances and the CSS Pauli distance satisfy
$
d_X >= 9, quad d_Z >= 9, quad d_"Pauli" >= 9.
$
This proposition concerns the explicit matrices below. No JSON file,
external note, computational rank, numerical search, enumerated error
certificate, or cited result is a hypothesis. Recognition of any external
submitted matrix is a separate task. Distance twenty remains open.

All coefficients are in $F=bb(F)_2$. Put
$
Q={0,dots,18} times {0,dots,18}, quad
f=x+x^2+y^2, quad g=1+x^2 y+x^2 y^2.
$
There are two physical coordinates $A(i,j)$ and $B(i,j)$ at each $(i,j)$
in $Q$, ordered as $A(i,j)=19i+j$ and $B(i,j)=361+19i+j$.
Thus $V=F^722$ is identified with pairs $(u,v)$ of polynomials supported
in $Q$. Their physical weight is the number of nonzero coefficients in
the two components, added together. Let $T$ discard monomials outside
$Q$, componentwise. For a finite Laurent polynomial set
$overline(h)(x,y)=h(x^(-1),y^(-1))$.

In increasing lexicographic anchor order, the checks are exactly
$
H_X [(a,b),:]=T(x^a y^b (f,g)),
quad -2<=a<=18, quad 0<=b<=16;
$
$
H_Z [(c,d),:]=T(x^c y^d (overline(g),overline(f))),
quad 2<=c<=18, quad 0<=d<=20.
$
Each matrix has $21 dot 17=357$ rows.
Let $S_X$ and $S_Z$ be their row spans, and set
$K_X=S_Z^perp$, $K_Z=S_X^perp$ for the usual binary dot product.
Once commutation is established, the sector logical spaces are
$K_X/S_X$ and $K_Z/S_Z$. Define
$
d_X=min{ "wt"(w):w in K_X without S_X}, quad
d_Z=min{ "wt"(w):w in K_Z without S_Z}.
$
Both sets are nonempty by the dimension calculation below.
A CSS Pauli cycle is a pair $(w_X,w_Z)$ in $K_X times K_Z$.
It is trivial exactly when $(w_X,w_Z)$ belongs to $S_X times S_Z$.
Its weight is the cardinality of the union of the two physical supports;
$d_"Pauli"$ is the minimum weight of a nontrivial such pair. These are
the algebraic definitions used in Proposition 1.

= Elementary algebra and dimension facts

*PROPOSITION 2 (tools used below; independent review/formalization pending).*
The following elementary polynomial and finite-dimensional facts hold.

*Polynomial domains and extreme exponents.* A nonzero polynomial over
$F$ has leading coefficient 1. The leading term of a product is the
product of its leading terms, so $F[z]$ has no zero divisors. The proof
works over any coefficient ring without zero divisors. Applying it to
polynomials in one variable with coefficients in the polynomial ring in
the other proves that $F[x,y]$ is a domain. Minimum exponents add as well:
the coefficient at the minimum possible exponent is the product of the
two extreme coefficients. Multiplying finite Laurent polynomials by
monomials reduces these assertions to the polynomial case. Thus extreme
exponents add in either variable, also for finite Laurent polynomials.

*Division by a monic polynomial.* Let $D$ be a coefficient ring and let
$m(z)$ be monic of degree $d>0$. If a polynomial $a(z)$ has degree
$n>=d$ and leading coefficient $c$, subtract $c z^(n-d)m(z)$.
This strictly lowers the degree. Repetition terminates, giving
$a=m h+e$ with $deg e<d$. For uniqueness, a nonzero multiple of a monic
degree-$d$ polynomial has degree at least $d$: its leading coefficient
is the nonzero leading coefficient of the multiplier. The difference of
two remainders has degree less than $d$, so cannot be such a nonzero
multiple. Hence both quotient and remainder are unique. In particular
$F[y]/(m)$ has basis $1,y,dots,y^(d-1)$ when $m$ is monic of degree $d$.

*Finite-dimensional linear algebra.* A linearly independent list extends
to a basis by adjoining vectors outside its span until that span is the
space. Extending a subspace basis proves
$dim(U/W)=dim U-dim W$. For a linear map, choose preimages of a basis of
its image; together with a basis of its kernel they form a basis of its
domain, proving rank-nullity. A proper subspace admits a nonzero linear
functional vanishing on it, by prescribing values on an extended basis.
Independent vectors $s_1,dots,s_m$ in $F^n$ give independent functionals
$v mapsto s_i dot v$: a relation among the functionals evaluated on
coordinate unit vectors is exactly a relation among the $s_i$.
Their combined map onto $F^m$ is surjective, since otherwise a nonzero
functional annihilating its image contradicts that independence.
Consequently their common orthogonal space has dimension $n-m$.
Finally, inclusion of two finite-dimensional subspaces of the same
dimension implies equality, again by basis extension. $square$

= Commutation and the two check ranks

*PROPOSITION 3 (independent review/formalization pending).*
The matrices in Section 1 commute and both have rank 357.

== Commutation for every pair of anchors

For untruncated X and Z translates at anchors $(a,b)$ and $(c,d)$,
the overlap parity on the A block is the coefficient at
$x^(c-a)y^(d-b)$ of $f g$. Indeed an intersection corresponds to support
exponents $s$ of $f$ and $t$ of $g$ satisfying
$(a,b)+s=(c,d)-t$. The B overlap is that coefficient of $g f$.
Their sum is zero in characteristic two.
Every full X translate used here has all column coordinates in $[0,18]$.
Every full Z translate used here has all row coordinates in $[0,18]$.
Every intersection is therefore in $Q$: truncation removes no
intersection. All finite overlaps are zero, proving commutation.

== X independence

Write the coefficient polynomial of an X combination as
$
h=sum_(i=-2)^18 x^i h_i (y), quad "supp"(h_i) subset.eq {0,dots,16}.
$
Suppose $T(f h,g h)=0$. No column truncation occurs in these products.
Put $t=y+y^2$. For each $0<=i<=18$, the entire row polynomial vanishes:
$
h_(i-2)+h_(i-1)+y^2 h_i=0, quad h_i=t h_(i-2).
$
Put $B=1+y^2 t=1+y^3+y^4$. Substitution gives
$h_(i-1)=B h_(i-2)$. At $i=0,1$ it follows that
$h_(-1)=B h_(-2)$ and $h_0=B^2 h_(-2)$, while
$h_0=t h_(-2)$. Therefore
$
(B^2+t)h_(-2)=(1+y+y^2+y^6+y^8)h_(-2)=0.
$
The displayed multiplier is nonzero in the domain $F[y]$.
Thus $h_(-2)=h_(-1)=0$, and $h_i=t h_(i-2)$ forces all remaining
coefficients to vanish. The 357 X rows are independent.

== Z independence

Reflect the square by $(i,j) mapsto (18-i,18-j)$ and exchange the two
blocks. This is a permutation of physical coordinates. It sends a Z
row at $(c,d)$ to $T(x^(18-c)y^(18-d)(f,g))$.
Thus a vanishing Z combination becomes $T(f h,g h)=0$ with
$
h=sum_(j=-2)^18 y^j h_j (x), quad "supp"(h_j) subset.eq {0,dots,16}.
$
No row truncation occurs. Put $a=x+x^2$ and $b=1+x^2 a$.
For $0<=j<=18$ the equations are
$
h_(j-2)=a h_j, quad
h_j+x^2 h_(j-1)+x^2 h_(j-2)=0,
$
so $x^2 h_(j-1)=b h_j$.
At $j=0,1$ these imply $x^4 h_(-1)=b^2 h_1$.
Since $h_(-1)=a h_1$,
$
(b^2+x^4 a)h_1=(1+x^5+x^8)h_1=0.
$
The domain $F[x]$ gives $h_1=0$. The second relation at $j=1$ gives
$h_0=0$ through $x^2 h_0=b h_1$; the first at $j=0,1$ gives
$h_(-2)=h_(-1)=0$.
For $j>=2$, induction in $a h_j=h_(j-2)$, with $a!=0$, gives
every remaining $h_j=0$. All 357 Z rows are independent.
Reflection was used only as a coordinate permutation, not asserted to be
a symmetry of the code. This completes Proposition 3. $square$

By Proposition 2 and commutation,
$
dim K_X=dim K_Z=722-357=365,
quad dim S_X=dim S_Z=357.
$
Both logical quotients therefore have dimension eight, and $k=8$.
In particular each contains $2^8$ cosets, with only one zero coset.
There is a cycle outside its stabilizer space in each sector. Both sets
defining $d_X$ and $d_Z$ are nonempty finite sets of vectors with positive
integer weights, so their minima exist. Taking a nontrivial sector cycle
and the zero vector in the other sector also makes the Pauli minimization
set nonempty; it too is finite and has an attained minimum.

= Elementary bulk exactness without unique factorization

*PROPOSITION 4 (independent review/formalization pending).*
For polynomials $u,v$ in $F[x,y]$,
$
g u+f v=0 quad <==> quad
(u,v)=(f h,g h) " for a unique " h in F[x,y].
$
Among pairs supported in $Q$, this kernel has dimension $17^2=289$.

*Proof.* Regard the ring as $F[y][x]$. The polynomial
$f=x^2+x+y^2$ is monic in $x$. Proposition 2 gives a unique division
$
u=f h+r_0+r_1 x, quad r_0,r_1 in F[y].
$
If $g u+f v=0$, then $f$ divides $g u$, and hence divides
$g(r_0+r_1 x)$. Modulo $f$ we have $x^2=x+y^2$ and
$
g equiv B+t x, quad t=y+y^2, quad B=1+t y^2.
$
The remainder of the product has constant and linear coefficients
$
B r_0+t y^2 r_1=0, quad
t r_0+(B+t)r_1=0.
$
Multiply the first equation by $B+t$ and the second by $t y^2$,
and add; the result is $r r_0=0$. Multiply the first by $t$ and the
second by $B$, and add; the result is $r r_1=0$, where
$
r=B(B+t)+t^2 y^2=B^2+t=1+y+y^2+y^6+y^8.
$
This is nonzero, so $r_0=r_1=0$ in the domain $F[y]$.
Thus $u=f h$. Substitution into the original equation gives
$f(g h+v)=0$. The domain property gives $v=g h$.
Conversely $(f h,g h)$ has syndrome $g f h+f g h=0$.
Uniqueness follows from $f h=f h'$ and $f!=0$.

For a nonzero $h$, the minimum exponents of $f$ are zero and maximum
exponents are two in each variable. Extreme-exponent addition shows that
$f h$ supported in $Q$ forces $h$ supported in $[0,16]^2$.
Conversely every $h$ in that square gives both $f h$ and $g h$ in $Q$.
The multiplier map is injective; its domain has the 289 monomials
$x^i y^j$, $0<=i,j<=16$, as basis.
This proves the dimension assertion. Every such pair is a combination
of the fully supported X checks, although only its kernel dimension is
needed below. $square$

= The degree-eight charge algebra and its two bases

*PROPOSITION 5 (independent review/formalization pending).*
Let
$
cal(A)=F[y]/(r), quad r=1+y+y^2+y^6+y^8.
$
The quotient identifies two polynomials exactly when their difference is
a polynomial multiple of $r$. Addition and multiplication preserve that
relation, so they define the quotient algebra operations.
Use the same letter $y$ for its residue class, and define in this algebra
$
t=y+y^2, quad B=1+y^2 t, quad
X=1+y^2+y^5+y^6.
$
Then $y$ and $X$ are units, $f(X,y)=g(X,y)=0$, and both lists
$
1,y,dots,y^7 quad "and" quad 1,X,dots,X^7
$
are bases of $cal(A)$.

*Proof of the identities and first basis.* The monic division result
gives dimension eight and basis $1,y,dots,y^7$.
The polynomial identities
$
r=B^2+t=1+t+y^4 t^2,
quad y(1+y+y^5+y^7)=1+r
$
show that
$
t^(-1)=1+y^4 t=1+y^5+y^6,
quad y^(-1)=1+y+y^5+y^7
$
in the quotient. Consequently $X=t^(-1)+y^2=B/t$.
Since $B^2=t$ in the quotient,
$X^2=t^(-1)$. This makes $X$ a unit, with inverse $X t$, and gives
$
X+X^2+y^2=0, quad 1+X^2(y+y^2)=0.
$
These are the required equations $f(X,y)=g(X,y)=0$.

*Proof of the second basis.* Work first in $F[x,y]$ and set
$L=g+x^2 f=1+x^3+x^4+x^2 y$. Direct expansion gives
$
L^2+x^4 f=1+x^5+x^8=:p(x).
$
Substitute $(X,y)$ to get $p(X)=0$. Multiplying this relation by
$X^(-1)$ gives
$
X^(-1)=X^7+X^4.
$
The equation $L(X,y)=0$, divided by $X^2$, gives
$
y=X^(-2)+X+X^2.
$
It follows that $y$ is a polynomial in $X$, using the displayed polynomial
expression for $X^(-1)$. Every element of $cal(A)$ is a polynomial in
$y$, hence a polynomial in $X$. Division by the monic $p$, of degree
eight, reduces it to a linear combination of $1,X,dots,X^7$.
These eight spanning vectors in an eight-dimensional space are a basis:
a dependence would remove one vector from the spanning list, contradicting
the dimension. $square$

Define a residue map $rho:F[x,y] arrow cal(A)$ by substitution
$rho(x)=X$, $rho(y)=y$. The identities just proved show
$rho(g u+f v)=0$ for all $u,v$. When Laurent expressions are used, substitution
extends because both images are units. No identification with a Laurent
ideal quotient, and no unique-factorization result, is needed.

= X boundary image and complete X charge

*PROPOSITION 6 (independent review/formalization pending).*
The low-boundary residue defined below induces an isomorphism
$K_X/S_X arrow cal(A)$.

== Full-syndrome image and its ambient coefficient space

For a physical pair $w=(u,v)$ define
$sigma(w)=g u+f v$. Its coefficient at $(c,d)$ is exactly the overlap
with the full Z translate anchored there. Restricting that check to $Q$
does not change its overlap with $w$. Therefore
$
w in K_X quad <==> quad
[x^c y^d]sigma(w)=0
" for " 2<=c<=18, 0<=d<=20.
$
The syndrome is supported in $[0,20]^2$, because the operator lies in
$Q$ and both generator supports lie in $[0,2]^2$.
Hence a cycle has syndrome only in the two coefficient spaces
$
E_l=op("span"){ x^i y^j:i in {0,1}, 0<=j<=20},
$
$
E_h=op("span"){ x^i y^j:i in {19,20}, 0<=j<=20}.
$
They each have dimension 42; their disjoint monomial supports give a
direct sum $E=E_l ⊕ E_h$ of dimension 84.
Let $D=sigma(K_X)$ inside this fixed space.
The kernel of $sigma$ on all physical pairs has dimension 289 by
Proposition 4. It lies in $K_X$, since zero full syndrome implies
zero finite syndrome. Consequently
$
dim D=365-289=76.
$

Define $phi:E arrow cal(A)$ by $phi(ell+h)=rho(ell)+rho(h)$.
The low vectors $1,y,dots,y^7$ lie in $E_l$ and map to a basis.
The high vectors $x^19,x^19 y,dots,x^19 y^7$ lie in $E_h$ and
map to a basis multiplied by the unit $X^19$. Thus each restriction
is onto. In particular $op("rank") phi=8$ and $dim ker phi=84-8=76$.
All syndromes have residue zero, so $D subset.eq ker phi$.
Both are subspaces of the same $E$, with the same dimension. Therefore
$
D=ker phi.
$

== Stabilizers have zero low charge

For $w in K_X$ write uniquely $sigma(w)=ell+h$ in the preceding
direct sum, and define $c_X (w)=rho(ell)$.
To check vanishing on $S_X$, consider every allowed X anchor:

- If $0<=a<=16$, the translate is fully supported; its full syndrome is
  $g f x^a y^b+f g x^a y^b=0$.
- If $a=-2$ or $a=-1$, its retained physical rows are at most 1, so
  its full syndrome has rows at most 3. It is a finite cycle by
  commutation, so its coefficients in rows 2 and 3 vanish.
  Its full syndrome is its low part. Its residue is zero because it is
  of the form $g u+f v$.
- If $a=17$ or $a=18$, its retained physical rows are at least 17.
  Its syndrome has no terms in rows 0 or 1, so its low charge is zero.

These cases cover every X generator. Linearity proves
$S_X subset.eq ker c_X$.

== Surjectivity and injectivity on the quotient

Given $a in cal(A)$, choose $ell in E_l$ and $h in E_h$ with
$rho(ell)=rho(h)=a$, using the two surjective restrictions.
Then $phi(ell+h)=a+a=0$. Since $D=ker phi$, there exists a physical
cycle $w$ with $sigma(w)=ell+h$. It has $c_X (w)=a$.
Thus $c_X:K_X arrow cal(A)$ is onto.
Its kernel has dimension $365-8=357$ and contains $S_X$, whose
dimension is 357. Hence $ker c_X=S_X$.
The induced quotient map is well-defined because it kills $S_X$;
it is onto by surjectivity of $c_X$ and injective by the kernel equality.
This proves Proposition 6. $square$

= Z boundary image and complete Z charge

*PROPOSITION 7 (independent review/formalization pending).*
The reflected low-column charge defined here induces an isomorphism
$K_Z/S_Z arrow cal(A)$.

== Reflection and all tested coefficients

On physical polynomials define
$J(h)=x^18 y^18 overline(h)$, and on physical pairs define
$M(u,v)=(J(v),J(u))$. This is a coordinate permutation, its square is
the identity, and it preserves physical weight.
Let $K'_Z=M(K_Z)$ and $S'_Z=M(S_Z)$, which have dimensions 365 and 357.
For a physical Z pair $w=(u,v)$, its full X-check syndrome is
$sigma_Z (w)=overline(f)u+overline(g)v$.
For $w'=(u',v')=M(w)$,
$
sigma(w')=g u'+f v'=x^18 y^18 overline(sigma_Z (w)).
$
The original tested X anchors are $[-2,18] times [0,16]$.
Under the exponent reflection they become $[0,20] times [2,18]$.
It follows that
$
w' in K'_Z quad <==> quad
[x^i y^j]sigma(w')=0
" for " 0<=i<=20, 2<=j<=18.
$
As $w'$ is a physical pair, its syndrome lies in $[0,20]^2$.
Its only possible remaining terms are in
$
E'_l=op("span"){ x^i y^j:0<=i<=20, j in {0,1}},
$
$
E'_h=op("span"){ x^i y^j:0<=i<=20, j in {19,20}}.
$
Both spaces have dimension 42 and their direct sum $E'$ has dimension 84.
Put $D'=sigma(K'_Z)$. Proposition 4 applies to these polynomial pairs:
the full-syndrome kernel in the square has dimension 289, and lies in
$K'_Z$ because its tested coefficients are zero. Hence $dim D'=76$.

== Total residue and the dual image

Define $phi':E' arrow cal(A)$ by $phi'(ell+h)=rho(ell)+rho(h)$.
The vectors $1,x,dots,x^7$ in $E'_l$ map to the second basis of
Proposition 5. The vectors $y^19,y^19 x,dots,y^19 x^7$ in $E'_h$
map to that basis multiplied by the unit $y^19$.
Thus both restrictions of $phi'$ are onto. It has rank eight and
kernel dimension 76.
Every syndrome is killed by $rho$, so $D' subset.eq ker phi'$.
These are subspaces of $E'$ of the same dimension, proving
$D'=ker phi'$.

== All reflected stabilizers have zero low-column residue

For $w' in K'_Z$, define $c'_Z (w')$ as the residue of the
$E'_l$ component of $sigma(w')$.
A Z generator at $(c,d)$ becomes
$T(x^(18-c)y^(18-d)(f,g))$ under $M$.
Its anchors therefore have row coordinate $a in [0,16]$ and column
coordinate $b in [-2,18]$. In particular it is fully supported in rows.
Every such reflected generator is in $K'_Z$ by commutation and the
definition of $M$. There are three cases:

- For $0<=b<=16$, it is fully supported and has zero full syndrome.
- For $b=-2$ or $b=-1$, its physical columns are at most 1.
  Its full syndrome has columns at most 3. Membership in $K'_Z$
  forces columns 2 and 3 to vanish. Its full syndrome equals its
  low-column part, and its residue is zero by $rho(g u'+f v')=0$.
- For $b=17$ or $b=18$, its physical columns are at least 17,
  so its full syndrome has no low-column terms.

All generators therefore have zero $c'_Z$, and
$S'_Z subset.eq ker c'_Z$.

== Surjectivity and the original Z quotient

For any $a in cal(A)$, choose $ell in E'_l$ and $h in E'_h$
both of residue $a$. Their sum has total residue zero, so belongs to
$ker phi'=D'$. There is $w' in K'_Z$ with this full syndrome and
$c'_Z (w')=a$. Thus $c'_Z$ is onto.
Its kernel has dimension $365-8=357$ and contains the
357-dimensional $S'_Z$, so these spaces are equal.
Define on original Z cycles $c_Z (w)=c'_Z (M(w))$.
The invertible permutation $M$ gives surjectivity of $c_Z$ and
$ker c_Z=S_Z$. Hence it induces the claimed isomorphism.
This proves Proposition 7 without assuming an X/Z symmetry of the code.
$square$

= Row and column transport inequalities

*PROPOSITION 8 (independent review/formalization pending).*
For every nontrivial X logical, if $w_i$ is its weight in physical row
$i$ and $W=sum_(i=0)^18 w_i$, then
$
w_i+w_(i+1)>=1 " for " 0<=i<=17,
quad W>=9+ceil((w_0+w_18)/2).
$
For every nontrivial Z logical, the corresponding assertions hold with
physical column weights.

== X cuts: exact flux and weight count

Write a physical X cycle as
$u=sum_(i=0)^18 x^i u_i (y)$ and
$v=sum_(i=0)^18 x^i v_i (y)$.
Its syndrome is $ell+h$ in $E_l ⊕ E_h$.
For each $2<=k<=19$, retain only physical rows $i<k$, calling the
result $(u^(<k),v^(<k))$. Since $g=1+x^2t$ and $f=y^2+x+x^2$,
coefficient multiplication gives
$
g u^(<k)+f v^(<k)=ell+F_k,
$
where
$
F_k=x^k (t u_(k-2)+v_(k-2)+v_(k-1))
    +x^(k+1)(t u_(k-1)+v_(k-1)).
$
Below the cut the truncated syndrome equals the full syndrome: all
generator exponents are nonnegative. Its rows 2 through $k-1$ vanish.
Above the cut only the last two retained rows contribute, giving precisely
the displayed $F_k$. These facts prove the identity also at $k=2$ and
$k=19$, without dropping endpoint terms.
Applying $rho$ gives
$
rho(F_k)=rho(ell)=c_X (u,v).
$
For a nontrivial logical this value is nonzero by Proposition 6.
If physical rows $k-2$ and $k-1$ were both empty, every coefficient in
$F_k$ would be zero, a contradiction. Hence
$w_i+w_(i+1)>=1$ for every $0<=i<=17$.
Summing all eighteen inequalities counts the outer rows once and all
other rows twice:
$
18<=sum_(i=0)^17(w_i+w_(i+1))=2W-w_0-w_18.
$
Since $W$ is an integer, the claimed X weight inequality follows.

== Z cuts: explicit flux after reflection

Let $w$ be an original Z cycle and write $M(w)=(u',v')$, with
$
u'=sum_(j=0)^18 y^j a_j (x), quad
v'=sum_(j=0)^18 y^j b_j (x).
$
Its full syndrome is $ell'+h'$ in $E'_l ⊕ E'_h$.
For $2<=k<=19$ truncate this pair to columns $j<k$.
Now use $g=1+x^2y+x^2y^2$ and $f=x+x^2+y^2$.
The full syndrome of the truncated pair is $ell'+G_k$, where
$
G_k=y^k (x^2 a_(k-2)+x^2 a_(k-1)+b_(k-2))
    +y^(k+1)(x^2 a_(k-1)+b_(k-1)).
$
To see all terms, the degree-one term of $g$ carries $a_(k-1)$
to column $k$; its degree-two term carries $a_(k-2)$ to $k$
and $a_(k-1)$ to $k+1$. The degree-two term of $f$ carries
$b_(k-2)$ to $k$ and $b_(k-1)$ to $k+1$.
The remaining terms stay below the cut, where they equal the full
syndrome. Tested columns 2 through $k-1$ vanish. This proves the
identity for every listed cut, including the two endpoints.
Its residue gives
$
rho(G_k)=rho(ell')=c'_Z (M(w))=c_Z (w).
$
If $w$ is a nontrivial Z logical, Proposition 7 makes this value nonzero.
Two consecutive empty columns of $M(w)$ would make $G_k=0$.
Thus its column weights $w'_j$ satisfy
$w'_j+w'_(j+1)>=1$ for $0<=j<=17$. Summing gives
$2W-w'_0-w'_18>=18$, because $M$ preserves total weight.
If $w_j$ are the original column weights, the reflection and block
exchange give $w'_j=w_(18-j)$. Every adjacent original column pair
therefore also has total weight at least one, and
$w'_0+w'_18=w_18+w_0$. This proves the claimed Z inequality. $square$

= Completion of the main proposition and remaining scope

Proposition 3 proves the stated commutation and ranks, and the ensuing
dimension calculation proves $k=8$. Proposition 8 applies to every
nontrivial sector logical, not just a selected representative:
its charge cannot vanish by Propositions 6 and 7, and adding stabilizers
does not change its charge. Each sector weight is consequently at least
nine.

For a nontrivial CSS Pauli cycle $(w_X,w_Z)$, it is impossible that both
$w_X in S_X$ and $w_Z in S_Z$. At least one component is a nontrivial
sector logical and has weight at least nine. The union of the two physical
supports contains that component's support, so its Pauli weight is at least
nine. This completes the proof of Proposition 1. $square$

*CONJECTURE / open mission.* The stronger assertion that both sector
distances are at least twenty is not proved here. The eighteen adjacent
two-strip inequalities establish nine; they are not a proof of twenty
or an assertion that twenty is close. Charge completeness is settled by
the supplied dimension-and-lifting argument at PROPOSITION grade, while
a stronger physical coefficient-weight inequality remains necessary.

*Review boundary.* This document contains all mathematical premises for
the explicit finite model. It uses elementary monic division, coefficient
recurrences, polynomial identities, and finite-dimensional linear algebra.
It uses no UFD argument, citation, external rank computation, numerical
certificate, or formal proof replay. Independent review and formalization
of this complete proposed argument remain outstanding. No claim about
the 566 target follows from this checkpoint.
