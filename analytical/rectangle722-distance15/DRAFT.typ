#set page(paper: "a4", margin: (x: 22mm, y: 17mm), numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.60em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#let F = $bb(F)_2$
#let wt = math.op("wt")
#let runs = math.op("runs")

#align(center)[
  #text(size: 17pt, weight: "bold")[Boundary charge and cancellation prove distance at least fifteen]
  #v(4pt)
  An explicit rectangular CSS model on 722 qubits \
  Combined proof draft · 11 November 2026
]

*Grade: PROPOSITION for this combined document; final independent review and capstone verification pending.*

= Main theorem and explicit model

*PROPOSITION 1 (main result).*
For the two rectangular check matrices defined in this section,
$
H_X H_Z^T=0, quad
"rank"(H_X)="rank"(H_Z)=357, quad k=8,
$
and both sector distances and the CSS Pauli distance satisfy
$
d_X >= 15, quad d_Z >= 15, quad d_"Pauli" >= 15.
$
This theorem concerns the explicit matrices below. No JSON file,
external note, computational rank, numerical search, enumerated error
certificate, or cited result is a hypothesis. Recognition of any external
submitted matrix is a separate task.

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
$K_X/S_X$ and $K_Z/S_Z$. Set $k=dim(K_X/S_X)$; the two quotient
dimensions are proved equal below. Define
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

*PROPOSITION 2 (tools used below).*
The following elementary polynomial and finite-dimensional facts hold.

*Polynomial domains and extreme exponents.* A nonzero polynomial over
$F$ has leading coefficient 1. If the largest nonzero exponents of two
factors are $r$ and $s$, the only pair contributing at exponent $r+s$ is
$(r,s)$; its coefficient is the product of the two nonzero leading
coefficients. All other exponent pairs have smaller sum. Thus the product
has largest exponent $r+s$ and is nonzero, so $F[z]$ has no zero divisors. The proof
works over any coefficient ring without zero divisors. Applying it to
polynomials in one variable with coefficients in the polynomial ring in
the other proves that $F[x,y]$ is a domain. Minimum exponents add as well:
the coefficient at the minimum possible exponent is the product of the
two extreme coefficients. Multiplying finite Laurent polynomials by
monomials reduces these assertions to the polynomial case. Thus extreme
exponents add in either variable, also for finite Laurent polynomials.

*Division by a monic polynomial.* Let $D$ be a commutative coefficient ring and let
$m(z)$ be monic of degree $d>0$. If a polynomial $a(z)$ has degree
$n>=d$ and leading coefficient $c$, subtract $c z^(n-d)m(z)$.
This strictly lowers the degree. Repetition terminates, giving
$a=m h+e$ with $deg e<d$. For uniqueness, a nonzero multiple of a monic
degree-$d$ polynomial has degree at least $d$: its leading coefficient
is the nonzero leading coefficient of the multiplier. The difference of
two remainders has degree less than $d$, so cannot be such a nonzero
multiple. Hence both quotient and remainder are unique. In particular
$F[y]/(m)$ has basis $1,y,dots,y^(d-1)$ when $m$ is monic of degree $d$.

*Finite-dimensional linear algebra.* A basis of size $r$ identifies a binary
vector space with $F^r$, which has $2^r$ elements. Consequently any two
bases have the same size; this defines dimension. A linearly independent list extends
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

*PROPOSITION 3.*
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

*PROPOSITION 4.*
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

*PROPOSITION 5.*
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

*PROPOSITION 6.*
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

*PROPOSITION 7.*
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

*PROPOSITION 8.*
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


#pagebreak()
= A local polynomial strip bound

*PROPOSITION 9 (local strip bound).* Let $(a_i,b_i)_(i=0)^18$ be polynomial pairs over $bb(F)_2$, with
each nonzero polynomial of degree at most 18. Assume either of these two
systems, with all equalities in the indicated polynomial ring:

*Forward system F*, in $bb(F)_2[y]$:
$ a_i=(y+y^2)a_(i-2)+b_(i-1)+b_(i-2)+y^2b_i
  quad (2<=i<=18). $ <forward>

*Backward system B*, in $bb(F)_2[x]$:
$ (x+x^2)b_i=a_i+x^2a_(i-1)+x^2a_(i-2)+b_(i-2)
  quad (2<=i<=18). $ <backward>

For a polynomial $p$, let $wt(p)$ count its nonzero coefficients, including
$wt(0)=0$. Define
$ w_i=wt(a_i)+wt(b_i), quad W=sum_(i=0)^18 w_i. $
Suppose also that
$ w_i+w_(i+1)>=1 quad (0<=i<=17). $ <adjacent>
Then
$ W>=15. $ <main-bound>

All polynomial equalities are exact: no quotient relation, periodic
identification, or truncation of products is permitted. The proof does not
need the degree cap beyond the statement; it is valid for arbitrary finite
polynomial slices satisfying the same equations and index ranges.

*Proof organization.* Lemmas 1–4 establish the local costs. The gap-counting section below
combines them by counting gaps between zero slices and completes the proof.

= Polynomial facts and a branch between zeros

For the local calculations only, rename the indeterminate in either
system as $T$, and put $t=T+T^2$. This renames a variable, not a recurrence.
A slice is empty if $w_i=0$, a singleton if $w_i=1$, and heavy if $w_i>=2$.
A singleton pair has exactly one nonzero block, which is a monomial.
In particular $u+T^2v$ and $T^2u+v$ each have weight one whenever
$(u,v)$ is a singleton.

If $runs(p)$ counts maximal consecutive runs of exponents in the support of
$p$, with $runs(0)=0$, then
$ wt(t p)=wt((1+T)p)=2runs(p). $ <runs>
Indeed a run from exponent $c$ to $d$ contributes exactly $T^c+T^(d+1)$
to $(1+T)p$. Successive runs are separated by a zero coefficient, so if one ends at $d$
the next starts at least at $d+2$. Thus endpoints from distinct runs are distinct. A monomial shift
does not change weight. Thus $wt(t p)>=2$ for $p!=0$.
The support of $u+v$ is contained in the union of the two supports, proving
$wt(u+v)<=wt(u)+wt(v)$. Evaluation at 1 sums every nonzero coefficient,
so $p(1)$ is the parity of $wt(p)$. If $p(0)=0$, its constant coefficient
is zero; shifting every remaining exponent down by one gives a polynomial
$h$ with $p=T h$. Finally, if two nonzero polynomials have highest exponents
$r,s$, the coefficient at $r+s$ in their product comes only from that pair
and equals 1. Their product is nonzero. Thus the polynomial ring is a domain,
and nonzero factors can be cancelled.

*Lemma 1 (directional branch).* Suppose $1<=r<=17$ and slices $r-1,r+1$
are empty. In system F, $b_r=0$; if $r<=16$ and slice $r$ is nonempty,
then $w_(r+2)>=2$. In system B, $a_r=0$; if $r>=2$ and slice $r$ is
nonempty, then $w_(r-2)>=2$.

*Forward proof.* Applying @forward at $r+1$ gives $0=b_r$.
At $r+2$, when this index is at most 18, it gives
$ a_(r+2)+T^2b_(r+2)=t a_r. $
The sum of the two physical block weights is at least the weight of their
sum, hence at least $2runs(a_r)>=2$ when $a_r!=0$.

*Backward proof.* Applying @backward at $r+1$ gives $0=T^2a_r$,
so $a_r=0$. Applying @backward at $r$, when $r>=2$, gives
$ T^2a_(r-2)+b_(r-2)=t b_r. $
The same coefficient-weight inequality gives $w_(r-2)>=2runs(b_r)>=2$.
This proves both assertions. $square$

There is exactly one possible exceptional middle index per direction:
$r=17$ in F would require equation 19, and $r=1$ in B would require
equation 1. Neither equation is among the hypotheses. No branch cost is
asserted at these exceptions.

= Local costs inside gaps

*Lemma 2 (two occupied slices between zeros).* If $0<=k<=15$, slices
$k,k+3$ are empty, and the intermediate slices are not both empty, then
$ w_(k+1)+w_(k+2)>=4. $

*Forward proof.* Write the intermediate slices as $(p,q),(u,v)$.
Equations at $k+2,k+3$ are
$ u=q+T^2v, quad t p+q+v=0. $
Evaluation at $T=1$ gives $u(1)=0$. If $u!=0$, then $wt(u)>=2$.
Also $wt(p)+wt(q)+wt(v)>=2$: weight zero forces $u=0$, and weight one
leaves a single nonzero term in $t p+q+v=0$. Thus the total is at least four.
If $u=0$, then $q=T^2v$ and $t p=(1+T^2)v$. Cancelling $1+T$ yields
$T p=(1+T)v$. Evaluation at zero shows that $v=T h$ for a polynomial $h$;
then $p=(1+T)h$ and $q=T^3h$. Nonemptiness gives $h!=0$, and total weight
is $2wt(h)+2runs(h)>=4$.

*Backward proof.* The equations for the same named slices are instead
$ t v=u+T^2p, quad q=T^2(u+p). $
Evaluation at one gives $q(1)=0$. If $q!=0$, its weight is at least two.
The remaining weight $wt(p)+wt(u)+wt(v)$ is at least two, since weight
zero forces $q=0$ and weight one cannot satisfy $t v+u+T^2p=0$.
If $q=0$, then $u=p$ and $t v=(1+T^2)p$. Cancelling $1+T$ gives
$T v=(1+T)p$. Hence $p=T h$, $u=T h$, $v=(1+T)h$ for $h!=0$.
The total is again $2wt(h)+2runs(h)>=4$. $square$

*Lemma 3 (three occupied slices between zeros).* If $0<=k<=14$, slices
$k,k+4$ are empty, and all three intermediate slices are occupied, then
$ w_(k+1)+w_(k+2)+w_(k+3)>=4. $

*Forward proof.* A failure would make all three pairs $(p,q),(u,v),(h,l)$
singletons. The equations at $k+2,k+3,k+4$ are
$ u=q+T^2v, quad h=t p+v+q+T^2l, quad 0=t u+l+v. $
If $q=0$, the first equation forces both $u,v$ to vanish or both to be
nonzero, contradicting the second singleton. Thus $q$ is a monomial and
$p=0$. If $u!=0$, then $v=0$ and the last equation gives $l=t u$ of
weight two, contradicting the third singleton. Consequently $u=0$, $v$
is a monomial, and $l=v$, so $h=0$. The middle equation now gives
$q=(1+T^2)v$, of weight two, a contradiction.

*Backward proof.* The equations for the three singleton slices are
$ t v=u+T^2p, quad t l=h+T^2u+T^2p+q, quad v=T^2(h+u). $
If $v!=0$, it is a monomial and $u=0$, so the first equation forces
$T^2p=t v$ of weight two, impossible in the first singleton. Hence $v=0$
and $u$ is a monomial. The last equation gives $h=u$, so $l=0$. The first
gives $T^2p=u$, so $q=0$. The middle equation is then
$0=u+T^2u+u=T^2u$, a contradiction. $square$

*Lemma 4 (four occupied slices next to a zero).* In system F, an empty
slice $k$, with $0<=k<=14$, followed by four occupied slices satisfies
$ sum_(i=k+1)^(k+4) w_i>=5. $
In system B, an empty slice $R$, with $4<=R<=18$, preceded by four
occupied slices satisfies
$ sum_(i=R-4)^(R-1) w_i>=5. $
Neither assertion requires another empty slice at the other end.

*Forward proof.* If all four slices $(p,q),(u,v),(h,l),(m,n)$ are
singletons in increasing index order, the equations at $k+2,k+3,k+4$ are
$ u+T^2v=q, quad h+T^2l=t p+v+q, quad m+T^2n=t u+l+v. $
The first left side is a monomial, so $q$ is a monomial and $p=0$.
If the second slice were B-only, then $u=0,q=T^2v$, and the second
equation would give $h+T^2l=(1+T^2)v$ of weight two, a contradiction.
Thus the second slice is A-only, with $u=q,v=0$.
The third equation to solve for a slice is now $h+T^2l=q$.
If the third slice is A-only, then $h=q,l=0$, and the fourth-slice
equation has right side $t q$, of weight two. If it is B-only, then
$h=0,q=T^2l$, and that right side is
$t q+l=(1+T^3+T^4)l$, of weight three. Both contradict the fourth
singleton, whose left side $m+T^2n$ is a monomial.

*Backward proof.* Name singleton slices $(p,q),(u,v),(h,l),(m,n)$ in
decreasing order at $R-1,R-2,R-3,R-4$. The equations at $R,R-1,R-2$ are
$ T^2u+v=T^2p, quad T^2h+l=t q+p+T^2u, quad T^2m+n=t v+u+T^2h. $
The first left side is a monomial, so $p$ is a monomial and $q=0$.
If the second slice were A-only, then $u=p,v=0$, and the second equation
would give $T^2h+l=(1+T^2)p$ of weight two. Thus the second slice is
B-only, with $u=0,v=T^2p$. The next equation is $T^2h+l=p$.
If the third slice is B-only, then $h=0,l=p$, and the last right side is
$t T^2p$, of weight two. If it is A-only, then $l=0,T^2h=p$, and the
last right side is $(1+T^3+T^4)p$, of weight three. Neither is the monomial
$T^2m+n$ required by the fourth singleton. $square$

In a gap of length five between successive zero slices, all four interior
slices are occupied. Lemma 4 applies from the left endpoint in F and from
the right endpoint in B. These endpoints satisfy $k<=13$ and $R>=5$,
respectively. Thus such a gap has interior weight at least five.
All monomials counted in the proofs have distinct exponents; none may be
discarded if an exponent exceeds 18. Such an identity would violate the
hypotheses rather than supply a further cancellation.

#pagebreak()
= Gap counting and completion of the local strip proof

Let $z$ be the number of zero slices, and let
$ E=sum_(i: w_i>0)(w_i-1)=W-(19-z). $
This is a nonnegative integer. If $z<=1$, then $W>=18$, so assume $z>=2$.
List zero positions as $q_1<dots<q_z$. By @adjacent, every gap
$q_(j+1)-q_j$ is at least two and every interior slice of a successive-zero
gap is occupied. Let $G,H,K,L$ count gaps of lengths two, three, four,
and five respectively.

*Branch budget.* The middle slice $r$ of a length-two gap is nonempty.
By Lemma 1 it forces a heavy slice at $r+2$ in F or $r-2$ in B, with at
most one exception (respectively $r=17$ or $r=1$). Distinct middle indices
have distinct targets. Each target contributes at least one unit to $E$,
irrespective of whether the middle slice is itself heavy. Therefore
$ G<=E+1. $ <branch-budget>

*Interior budget.* A length-three gap costs at least two units of excess
by Lemma 2. A length-four gap costs at least one by Lemma 3, and a
length-five gap at least one by Lemma 4. Interiors of distinct successive-zero
gaps are disjoint. Hence
$ 2H+K+L<=E. $ <interior-budget>

*Span budget.* The total span $q_z-q_1$ is at most 18. All uncounted gaps
have length at least six, so
$ 18 &>=2G+3H+4K+5L+6(z-1-G-H-K-L), \
  4G+3H+2K+L &>=6z-24. $ <span-budget>

Since $3H+2K+L<=2(2H+K+L)<=2E$, combining @branch-budget,
@interior-budget, and @span-budget yields
$ 6z-24<=4G+3H+2K+L<=4(E+1)+2E=6E+4. $
The two excess budgets may overlap: the coefficient six explicitly allows
this. No disjointness between branch targets and gap interiors was used.
Consequently
$ 6E>=6z-28, quad
  6W=114-6z+6E>=86. $
Since $6 dot 14=84<86<=90=6 dot 15$, integer weight gives
$W>=ceil(86/6)=15$, completing the local strip proof.
$square$


= Application to the physical rectangle and completion

*X sector.* Let $w=(u,v)$ be any nontrivial X logical. Expand its two
physical blocks in rows as
$u=sum_(i=0)^18 x^i a_i(y)$ and $v=sum_(i=0)^18 x^i b_i(y)$.
Each slice has degree at most 18. Its full syndrome vanishes at every
row $2<=i<=18$ by Proposition 6. Extracting that row from
$g u+f v$, using $g=1+x^2(y+y^2)$ and $f=x+x^2+y^2$, gives
$
0=a_i+(y+y^2)a_(i-2)+b_(i-1)+b_(i-2)+y^2b_i.
$
In characteristic two, moving $a_i$ to the other side leaves the forward
system of Proposition 9. Proposition 8 gives adjacent-row nonemptiness. The sum of
the slice coefficient weights is exactly the physical weight of $w$:
each A or B coordinate lies in exactly one row. Thus Proposition 9 proves
$"wt"(w)>=15$. The argument applies to every nontrivial representative,
without choosing a minimum or changing its weight by a stabilizer.

*Z sector.* Let $w$ be any nontrivial Z logical and write its reflected
pair $M(w)=(u',v')$ in columns:
$u'=sum_(j=0)^18 y^j a_j(x)$ and $v'=sum_(j=0)^18 y^j b_j(x)$.
Reflection and block exchange preserve the square and physical weight,
so every slice has degree at most 18. Proposition 7 identifies the tested
columns of $g u'+f v'$ as $2<=j<=18$. The coefficient in one such column is
$
0=a_j+x^2a_(j-1)+x^2a_(j-2)+(x+x^2)b_j+b_(j-2).
$
Rearranging in characteristic two gives precisely the backward system of
Proposition 9. The Z-cut argument of Proposition 8 gives adjacent nonemptiness for
these reflected columns. Their total coefficient weight equals the weight
of $M(w)$, hence equals the original physical weight of $w$. Proposition 9
therefore proves $"wt"(w)>=15$ for every nontrivial Z representative.

*Mixed Pauli sector.* A nontrivial pair $(w_X,w_Z)$ has a nontrivial X or
Z component, since otherwise it belongs to $S_X times S_Z$. That component
has weight at least fifteen by the preceding two paragraphs. Its support
is contained in the union defining the Pauli support, so the Pauli weight
is at least fifteen. The minima exist by the earlier dimension argument.

Proposition 3 supplies commutation and both ranks 357. The dimension
calculation immediately after Proposition 3 supplies $k=8$. The sector and Pauli arguments
above prove all the remaining assertions of Proposition 1. $square$
