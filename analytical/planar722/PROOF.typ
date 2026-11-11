#set page(paper: "a4", margin: 22mm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.1")
#let F = $bb(F)_2$

#align(center)[
  #text(17pt, weight: "bold")[An explicit rectangular CSS model on 722 qubits]
  #v(5pt)
  Commutation, independent boundary checks, and quotient dimension \
  Analytic proof · 11 November 2026
]

*Grade: THEOREM. Independently refereed and formalized in Lean.*

*THEOREM 1 (main result).*
For the two matrices defined in Section 1,
$ H_X H_Z^T=0, quad "rank"(H_X)="rank"(H_Z)=357. $
Writing $S_X$ and $S_Z$ for their row spaces, the quotient
$S_Z^perp / S_X$ has dimension $8$. Here $k=8$ denotes this binary
quotient dimension.

= Main result and explicit finite model

All vector and polynomial arithmetic is over #F. Let
$ Q = {0, dots, 18} times {0, dots, 18}. $
There are two qubits per cell, denoted $A(i,j)$ and $B(i,j)$, with indices
$19i+j$ and $361+19i+j$. Thus the physical vector space is $V=F^722$,
where here and below $F=bb(F)_2$. Encode a vector by a pair of polynomials
$(u,v)$ with exponents in $Q$, one for each block. The coefficients are its physical bits.

Finite Laurent polynomials allow integer exponents. Put
$ f=x+x^2+y^2, quad g=1+x^2 y+x^2 y^2, $
and write $overline(p)(x,y)=p(x^(-1),y^(-1))$. Let $P$ delete every monomial
whose exponent pair is outside $Q$, in each component separately. Define
two binary matrices by their rows, in lexicographic anchor order:
$
 H_X [(a,b),:] = P(x^a y^b (f,g)),
 quad -2 <= a <= 18, quad 0 <= b <= 16;
$
$
 H_Z [(c,d),:] = P(x^c y^d (overline(g),overline(f))),
 quad 2 <= c <= 18, quad 0 <= d <= 20.
$
Rank means dimension of the row span. For a subspace $S$, write
$S^perp={w in V: s dot w=0 " for every " s in S}$, where the dot product
is the sum of coordinate products in $F$. Both matrices have $357$ rows and
$722$ columns. Equivalently a row bit is
1 exactly when the indicated shifted support contains that qubit and the
qubit lies in $Q$. No external file or construction algorithm is part of
this definition.

The proof follows in Sections 2–5.
All auxiliary algebra and dimension facts needed for it are proved there.

= Polynomial facts used in the proof

*THEOREM 2 (elementary algebra).*
The rings $F[z]$ and $F[z,z^(-1)]$ have no zero divisors. In either ring,
extreme exponents of a nonzero product add. Polynomial equality is
coefficientwise, and multiplication is finite coefficient convolution.

*Proof.* A polynomial is by definition a finite coefficient function on
nonnegative integer exponents; a Laurent polynomial uses integer exponents.
Addition is coefficientwise and multiplication is convolution. If $p$ and
$q$ have largest nonzero exponents $r$ and $s$, the coefficient at $r+s$
in $p q$ is the product of their two leading coefficients. The only pair
of exponents attaining this sum is $(r,s)$; its coefficient is 1 in $F$.
Thus the product is nonzero, with largest exponent $r+s$. If the smallest
nonzero exponents are $r_0$ and $s_0$, every exponent in the first factor is
at least $r_0$ and every exponent in the second is at least $s_0$. The only
pair with sum $r_0+s_0$ is $(r_0,s_0)$, whose coefficient product is nonzero.
Thus the smallest exponent of the product is $r_0+s_0$. It also proves the statement over any
coefficient ring without zero divisors, using a nonzero product of extreme
coefficients. Iterating this observation allows polynomials in $x$ with
coefficients in $F[y]$, and vice versa. In particular a nonzero polynomial
times an unknown polynomial can vanish only if the unknown vanishes.
No unique factorization or assertion about polynomial ideals is needed. $square$

= Commutation without a corner assumption

Consider first the untruncated rows on the integer lattice. The overlap
parity of the A components at anchors $(a,b)$ and $(c,d)$ is the coefficient
of $x^(c-a)y^(d-b)$ in $f g$: an intersection is a pair of support exponents
$s$ in $f$, $t$ in $g$, with $(a,b)+s=(c,d)-t$. The B overlap is the same
coefficient in $g f$. Their sum is zero because convolution commutes and
$1+1=0$ in $F$.

Every full X row has all its second coordinates between 0 and 18, because
$0<=b<=16$ and all second support exponents of $f,g$ lie between 0 and 2.
Every full Z row has all its first coordinates between 0 and 18, because
$2<=c<=18$ and all first support exponents of $overline(g),overline(f)$ lie between
$-2$ and 0. Consequently any intersection of a full X row and a full Z row
already belongs to $Q$. Truncating both rows removes no intersection.
Their finite overlap is therefore zero. This proves $H_X H_Z^T=0$ for
every allowed pair of anchors; no corner completion is assumed.

= Independence by two one-dimensional recurrences

== X checks

Let a linear combination of X rows have anchor polynomial
$ h(x,y)=sum_(i=-2)^18 h_i (y)x^i, quad "supp"(h_i) subset.eq {0,dots,16}. $
Suppose its vector $P(f h,g h)$ is zero. Neither product has a second
coordinate outside 0 through 18. Thus for each $i=0,dots,18$ all coefficients
in the first-coordinate slice vanish, as polynomials in $F[y]$:
$ h_(i-2)+h_(i-1)+y^2 h_i=0, quad (y+y^2)h_(i-2)+h_i=0. $
Write $t=y+y^2$ and $b=1+y^2 t=1+y^3+y^4$. Substitution gives
$ h_(i-1)=b h_(i-2). $
At $i=0,1$ this says $h_(-1)=b h_(-2)$ and
$h_0=b^2 h_(-2)$, whereas the second original equation gives
$h_0=t h_(-2)$. Hence
$ (b^2+t)h_(-2)=(1+y+y^2+y^6+y^8)h_(-2)=0. $
The displayed multiplier is nonzero. Theorem 2 gives $h_(-2)=0$,
then $h_(-1)=0$. Induction in $h_i=t h_(i-2)$ gives $h_i=0$ for
all $0<=i<=18$. Every anchor coefficient is zero. Therefore the 357
X rows are independent.

== Z checks

Reflect physical coordinates by $(i,j) mapsto (18-i,18-j)$ and exchange
the two blocks. This is a permutation, so a vector vanishes before it
exactly when it vanishes after it. It sends a Z row at $(c,d)$ to
$P(x^(18-c)y^(18-d)(f,g))$. Thus a vanishing Z combination becomes
$P(f h,g h)=0$ with
$ h(x,y)=sum_(j=-2)^18 h_j (x)y^j, quad "supp"(h_j) subset.eq {0,dots,16}. $
This permutation is used to prove independence, not asserted to preserve
the code's check sets. No first-coordinate truncation occurs in these
products. Set $a=x+x^2$. For $j=0,dots,18$ vanishing gives
$ h_(j-2)+a h_j=0, quad h_j+x^2 h_(j-1)+x^2 h_(j-2)=0. $
With $b=1+x^2 a=1+x^3+x^4$, substitution yields
$ x^2 h_(j-1)=b h_j. $
The equations at $j=0,1$ imply $x^4 h_(-1)=b^2 h_1$. The first original
equation at $j=1$ gives $h_(-1)=a h_1$. Therefore
$ (b^2+x^4 a)h_1=(1+x^5+x^8)h_1=0. $
Theorem 2 forces $h_1=0$. The relation at $j=1$ then gives $h_0=0$;
the first equations give $h_(-2)=h_(-1)=0$. For $j>=2$, induction in
$a h_j=h_(j-2)$ gives $h_j=0$, because $a$ is nonzero. Hence all 357
Z rows are independent. This completes the rank part of Theorem 1.

= Quotient dimension

We supply the finite linear algebra explicitly.
The span of an independent list of $r$ vectors has dimension $r$: unique
coordinates identify it with $F^r$. It has $2^r$ elements, so two bases
of the same binary vector space necessarily have the same size. This also
justifies the dimension convention. An independent list in a finite vector
space extends to a basis by repeatedly adjoining a vector outside its span;
the process stops because the space has finitely many vectors. For a subspace
$U$ of dimension $r$ in $F^n$, extend a basis of $U$ to a basis of $F^n$.
The images of the added vectors form a basis of the quotient, proving
$"dim"(F^n/U)=n-r$.

The dot product on $F^n$ is nondegenerate: a nonzero vector has a coordinate
1 and pairs nontrivially with that coordinate's unit vector. If rows
$z_1,dots,z_r$ are independent, the functionals
$v mapsto z_i dot v$ are independent, since any linear relation between
them, evaluated on all unit vectors, is the same relation between the rows.
Their combined map $T:F^n arrow F^r$ is onto. Indeed, if its image were a
proper subspace, extend a basis of that image to a basis of $F^r$ and choose
a nonzero linear functional zero on the image, by prescribing its values
on this basis. In standard coordinates that functional is a nonzero linear
combination of the $r$ coordinates, contradicting their independence.

Choose preimages of a basis of $F^r$. Together with a basis of $"ker" T$
they form a basis of $F^n$: applying $T$ proves independence, and subtracting
the appropriate preimages proves spanning. Thus $"dim"("ker" T)=n-r$.
Apply this to $H_Z$: $"dim" S_Z^perp=722-357=365$. Commutation proved
$S_X subset.eq S_Z^perp$; the quotient basis argument gives
$"dim"(S_Z^perp/S_X)=365-357=8$.

This completes Theorem 1. $square$
