#set page(paper: "a4", margin: 22mm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#let wt = math.op("wt")

#align(center)[
  #text(17pt, weight: "bold")[A local polynomial strip bound]
  #v(4pt)
  Self-contained hand proof · 11 November 2026
]

= Main theorem

*THEOREM (weight at least fifteen).* Let $(a_i,b_i)_(i=0)^18$ be polynomial pairs over $bb(F)_2$, with
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

*Grade: THEOREM. All statements below are independently refereed and formalized in Lean.*

All polynomial equalities are exact: no quotient relation, periodic
identification, or truncation of products is permitted. The proof does not
need the degree cap beyond the statement; it is valid for arbitrary finite
polynomial slices satisfying the same equations and index ranges.

*Proof organization.* Lemmas 1–4 establish the local costs. Section 4
combines them by counting gaps between zero slices and completes the proof.

= Polynomial facts and a branch between zeros

For the local calculations only, rename the indeterminate in either
system as $T$, and put $t=T+T^2$. This renames a variable, not a recurrence.
A slice is empty if $w_i=0$, a singleton if $w_i=1$, and heavy if $w_i>=2$.
A singleton pair has exactly one nonzero block, which is a monomial.
In particular $u+T^2v$ and $T^2u+v$ each have weight one whenever
$(u,v)$ is a singleton.

If $rho(p)$ counts maximal consecutive runs of exponents in the support of
$p$, with $rho(0)=0$, then
$ wt(t p)=wt((1+T)p)=2rho(p). $ <runs>
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
sum, hence at least $2rho(a_r)>=2$ when $a_r!=0$.

*Backward proof.* Applying @backward at $r+1$ gives $0=T^2a_r$,
so $a_r=0$. Applying @backward at $r$, when $r>=2$, gives
$ T^2a_(r-2)+b_(r-2)=t b_r. $
The same coefficient-weight inequality gives $w_(r-2)>=2rho(b_r)>=2$.
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
is $2wt(h)+2rho(h)>=4$.

*Backward proof.* The equations for the same named slices are instead
$ t v=u+T^2p, quad q=T^2(u+p). $
Evaluation at one gives $q(1)=0$. If $q!=0$, its weight is at least two.
The remaining weight $wt(p)+wt(u)+wt(v)$ is at least two, since weight
zero forces $q=0$ and weight one cannot satisfy $t v+u+T^2p=0$.
If $q=0$, then $u=p$ and $t v=(1+T^2)p$. Cancelling $1+T$ gives
$T v=(1+T)p$. Hence $p=T h$, $u=T h$, $v=(1+T)h$ for $h!=0$.
The total is again $2wt(h)+2rho(h)>=4$. $square$

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
= Gap counting and completion of the main proof

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
$W>=ceil(86/6)=15$, completing the main proof.
$square$

