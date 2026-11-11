#set page(paper: "a4", margin: 22mm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.65em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#let wt = math.op("wt")

#align(center)[
  #text(17pt, weight: "bold")[A polynomial run-exit bound]
  #v(4pt)
  Self-contained hand proof · 11 November 2026
]

= Main theorem

*THEOREM (weight at least seventeen).* Let $(a_i,b_i)_(i=0)^18$ be polynomial pairs over $bb(F)_2$, each
nonzero polynomial having degree at most 18. Assume either of these exact
polynomial systems:

*Forward system F*, in $bb(F)_2[y]$:
$ a_i=(y+y^2)a_(i-2)+b_(i-1)+b_(i-2)+y^2b_i
  quad (2<=i<=18). $ <forward>

*Backward system B*, in $bb(F)_2[x]$:
$ (x+x^2)b_i=a_i+x^2a_(i-1)+x^2a_(i-2)+b_(i-2)
  quad (2<=i<=18). $ <backward>

Let $wt(p)$ count the nonzero coefficients of $p$, with $wt(0)=0$, and put
$ w_i=wt(a_i)+wt(b_i), quad W=sum_(i=0)^18 w_i. $
Assume adjacent nonemptiness:
$ w_i+w_(i+1)>=1 quad (0<=i<=17). $ <adjacent>
Let $z$ count indices with $w_i=0$, and set $E=W-(19-z)$.
For F define $epsilon=1$ exactly when $w_16=w_18=0$; for B define
$epsilon=1$ exactly when $w_0=w_2=0$. Otherwise set $epsilon=0$.
Then
$ E>=z-1-epsilon, quad W>=18-epsilon>=17. $ <main-bound>

*Grade: THEOREM. Independently refereed and formalized in Lean.*

All polynomial equalities are exact, with no quotient reduction or truncation.
The degree cap is unnecessary for the local implication.

*Proof organization.* Lemmas 1–4 establish directional branching and local
gap costs. Lemmas 5–7 establish short-run propagation and the run-exit
alternative. Section 5 partitions the excess without double counting and
proves the main theorem. Every needed local lemma is proved here.

= Polynomial facts and a branch between zeros

For the local calculations only, rename the indeterminate in either
system as $T$, and put $t=T+T^2$. This renames a variable, not a recurrence.
A slice is empty if $w_i=0$, a singleton if $w_i=1$, and heavy if $w_i>=2$.
A gap between consecutive zero indices $p<q$ has length $q-p$ and contains
$q-p-1$ interior slices.
A singleton pair has exactly one nonzero block, which is a monomial.
In particular $u+T^2v$ and $T^2u+v$ each have weight one whenever
$(u,v)$ is a singleton.

If $rho(p)$ counts maximal consecutive runs of exponents in the support of
$p$, with $rho(0)=0$, then
$ wt(t p)=wt((1+T)p)=2rho(p). $ <runs>
Indeed a run from exponent $c$ to $d$ contributes exactly $T^c+T^(d+1)$
to $(1+T)p$. Endpoints from distinct runs are distinct. A monomial shift
does not change weight. Thus $wt(t p)>=2$ for $p!=0$.
We also use $wt(u+v)<=wt(u)+wt(v)$ and the fact that $p(1)$ is the parity
of $wt(p)$. Both follow coefficient by coefficient over $bb(F)_2$.
For two nonzero polynomials with largest exponents $r,s$, only the pair
$(r,s)$ contributes to the coefficient at $r+s$ in their product, and that
coefficient is 1. Thus the product is nonzero: the polynomial ring is a domain,
and nonzero factors can be cancelled. If a polynomial vanishes at zero, its
constant coefficient is zero; shifting every remaining exponent down by one
expresses it as $T$ times another polynomial.

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
= Short runs and exit classification

Orient the list of zero slices in the forcing direction: increasing index
for F and decreasing index for B. A _short gap_ is a gap of length two
between successive zero slices. A _short run_ is a maximal sequence of
$m>=1$ consecutive short gaps. Its $m$ middle slices are nonempty by
@adjacent. The _exit target_ is the next slice after its last zero in the
forcing direction. It either lies inside the following longer gap, lies
in the tail after the last zero, or falls outside the index range.

*Lemma 5 (exact propagation and exceptional exits).* Write the active
polynomials in the $m$ middle slices of a short run as $P_1,dots,P_m$ in
forcing order. In F these are A-only slices and in B they are B-only slices.
Renaming the indeterminate as $T$ and writing $t=T+T^2$, one has
$ P_j=t^(j-1)P_1 quad (1<=j<=m), quad P_1!=0. $ <run-powers>
At an on-board exit $e$, respectively,
$ a_e+T^2b_e=t P_m quad "(F)", quad
  T^2a_e+b_e=t P_m quad "(B)". $ <exit-feed>
Thus every middle after the first, and every on-board exit, has weight at
least two. There is at most one missing exit: the final middle 17 in F or
the final middle 1 in B. Its occurrence is exactly $epsilon=1$ in the main
statement.

*Proof.* Lemma 1 gives the active block of every middle. In F, at the next
middle $r+2$, the B terms at $r,r+1,r+2$ vanish; hence its A polynomial
is $t$ times that at $r$. At an exit the same equation gives the F identity
in @exit-feed. In B, the equation at a middle $r$ is
$t b_r=T^2a_(r-2)+b_(r-2)$ because $a_r=a_(r-1)=0$. If $r-2$ is the next
middle, its A polynomial also vanishes, proving the B propagation step;
otherwise it gives the B exit identity. Induction proves @run-powers.
The domain property and @runs show weight at least two at every positive
power and every on-board exit.

A run ending at zero 18 in F has last middle 17 and would exit at 19.
Every other F run has an on-board exit: in particular zero 17 has target
18. In B a run ending at zero 0 has last middle 1 and would exit at $-1$;
zero 1 still has target 0. Only the final run can lack an exit. Such a run
exists precisely when the final zero gap is $(16,18)$ in F or $(2,0)$ in B,
as specified by $epsilon$. $square$

*Lemma 6 (cheap exit forces a feed of weight three or four).* Suppose three
successive exit slices in forcing order have weights $2,1,1$. If their
feeding middle polynomial is $P$, then $wt(P)$ is three or four. More
precisely $P$ is a monomial shift of $1+T+T^2$ or $1+T+T^2+T^3$.
The following statements specify the exact index ranges and equations.

*Forward proof.* Let the feeding middle be at $r$, with $1<=r<=14$, and
zeros at $r-1,r+1$. It is $(P,0)$. Write $(A_i,B_i)$ for the slices at
$r+2+i$, for $i=0,1,2$. The equations at $r+2,r+3,r+4$ are
$ A_0+T^2B_0=t P, quad A_1+T^2B_1=B_0, \
  A_2+T^2B_2=t A_0+B_0+B_1. $ <cheap-forward>
The second equation makes $B_0$ a monomial; the first slice's weight two
then makes $A_0$ a monomial. If the second slice is B-only, the last right
side has even coefficient parity: $t A_0$ has even weight and $B_0,B_1$
are monomials. It cannot be the monomial on the left.
Thus the second slice is A-only, with $A_1=B_0,B_1=0$. For $t A_0+B_0$
to be a monomial, $B_0$ must cancel exactly one term of $t A_0$. Hence
$B_0=T A_0$ or $B_0=T^2A_0$. Write $A_0=T^a$. The feed equation gives
$ P=T^(a-1)(1+T+T^2) quad "or" quad
  P=T^(a-1)(1+T+T^2+T^3), quad a>=1. $
To justify the division, $a=0$ would give a nonzero constant on the left
of the feed, while $T$ divides its right side. For $a>=1$, cancel
$T(1+T)$ using $1+T^3=(1+T)(1+T+T^2)$ and
$1+T^4=(1+T)(1+T+T^2+T^3)$. Both displayed feed forms have the asserted
weight.

*Backward proof.* Let the feeding middle be at $r$, with $4<=r<=17$ and
zeros at $r-1,r+1$. It is $(0,P)$. Write $(A_i,B_i)$ for the slices at
$r-2-i$. The equations at $r,r-1,r-2$ give
$ T^2A_0+B_0=t P, quad T^2A_1+B_1=T^2A_0, \
  T^2A_2+B_2=t B_0+A_0+T^2A_1. $ <cheap-backward>
Now the second equation makes $A_0$ a monomial and weight two of the first
slice makes $B_0$ a monomial. If the second slice is A-only, then $A_1=A_0$
and the last right side is $t B_0+(1+T^2)A_0$, of even coefficient parity.
It cannot be a monomial. Thus the second slice is B-only, and $t B_0+A_0$
must be a monomial. Necessarily $A_0=T B_0$ or $A_0=T^2B_0$.
Writing $B_0=T^b$, the feed yields
$ P=T^(b-1)(1+T+T^2) quad "or" quad
  P=T^(b-1)(1+T+T^2+T^3), quad b>=1. $
As above $b=0$ is excluded by the constant coefficient, and cancellation
of $T(1+T)$ proves the formulas for $b>=1$. This proves the lemma from the
separate backward equations. $square$

*Lemma 7 (exit alternative).* Suppose a short run feeds a longer zero gap
$D$ of length $d>=4$. Let $P$ be its final middle polynomial and let
$E_D$ be the excess inside $D$, namely the sum of $w_i-1$ over its interior.
Then
$ E_D>=2 quad "or" quad wt(P)>=3. $ <exit-alternative>
For length three, $E_D>=2$ unconditionally.

*Proof.* The exit target is the first interior slice and has weight at
least two by Lemma 5. If $E_D<=1$, that slice has weight exactly two and
every other interior slice is a singleton. There are at least three
interior slices, so Lemma 6 applies. Its equations are tested: a gap of
length at least four requires $r+5<=18$ in F or $r-5>=0$ in B, stronger
than the respective index ranges in Lemma 6. Thus $wt(P)>=3$.
For length three use Lemma 2. $square$

#pagebreak()
= Disjoint excess accounting and the main proof

If $z=0$, all nineteen slices are occupied, giving $W>=19$ and
$E>=0>=z-1-epsilon$. Hence assume $z>=1$. There are $z-1$ successive-zero
gaps. All have length at least two by @adjacent. Let $G$ count short gaps,
$M=z-1-G$ count longer gaps, and $R_2$ count maximal short runs. Every
interior slice of a successive-zero gap is occupied, so its contribution
to $E$ is exactly its weight minus one.

*Baseline inside runs.* In a short run of $m$ gaps, reserve one excess
unit at every middle after the first, totalling $m-1$. These units exist by
Lemma 5. Across all short runs this reserves $G-R_2$ units.

*Baseline inside longer gaps.* Reserve one excess unit in every longer
gap, totalling $M$. Length three has at least two units by Lemma 2.
Length four has at least one by Lemma 3. Length at least five has at least
one in the first four interior slices in forcing order by Lemma 4.
These longer-gap interiors are disjoint from each other and from all
short-run middles. Thus the baseline reserves $G-R_2+M$ units.

*An additional unit for each run that has an exit.* If a run is followed
by a gap of length three, that gap has a second excess unit after its
reserved baseline. If its following gap has length at least four, Lemma 7
says either the same second gap unit exists, or the run's terminal middle
has weight at least three. In the latter case that middle has at least two
excess units. At most one was reserved there in the run baseline: one for
$m>=2$, zero for $m=1$. At least one further unit therefore remains.
Knowing only that the terminal middle was heavy would not suffice;
Lemma 6 supplies the needed weight at least three.

Distinct short runs have distinct terminal middles and distinct following
longer gaps. Run interiors are disjoint from longer-gap interiors.
Thus none of these selected additional units is a reserved baseline unit
or a unit already selected for another run.

If instead the final run exits into an on-board tail, Lemma 5 makes its
target heavy. Its excess unit lies outside all baseline regions and supplies
that run's additional unit. Only a run with a missing exit receives no
required additional unit. Lemma 5 identifies precisely $epsilon$ such runs.
Therefore the number of additional units is at least $R_2-epsilon$, and
$ E &>= (G-R_2+M)+(R_2-epsilon) \
    &= G+M-epsilon=z-1-epsilon. $
Finally,
$ W=19-z+E>=18-epsilon>=17. $
This includes $z=1$, where $G=M=R_2=epsilon=0$ and $W>=18$.
The main theorem is proved. $square$

*Endpoint distinction.* The only possible discount is the nonexistent
target at index 19 in F or $-1$ in B. An existing target at index 18 in F
or index 0 in B still costs an excess unit, even when no later zero exists.
The result gives eighteen whenever that missing-exit configuration is absent.

