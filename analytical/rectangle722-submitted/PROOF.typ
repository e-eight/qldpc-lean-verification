#set page(paper: "a4", margin: (x: 22mm, y: 17mm), numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.60em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)")
#let F = $bb(F)_2$
#let wt = math.op("wt")
#let runs = math.op("runs")

// Referenceable statement headings use native figure counters and labels.
// Appendix prefixes are captured at the statement, so forward references
// retain their target's numbering even when used in another appendix.
#let statement(target, kind: "Theorem", title: none, appendix: false) = context {
  let prefix = if appendix {
    numbering("A", counter(heading).get().first()) + "."
  } else { "" }
  let numbers = n => prefix + str(n)
  [#figure(
    kind: kind,
    supplement: kind,
    numbering: numbers,
    outlined: false,
    caption: none,
    block(width: 100%, align(left, context strong([
      #kind #counter(figure.where(kind: kind)).display(numbers)#if title != none [ (#title)].
    ]))),
  )#target]
}
#let theorem = statement.with(kind: "Theorem")
#let lemma = statement.with(kind: "Lemma")
#show figure.where(kind: "Theorem"): set block(above: 0.5em, below: 0.3em)
#show figure.where(kind: "Lemma"): set block(above: 0.5em, below: 0.3em)


#align(center)[
  #text(size: 17pt, weight: "bold")[Analytic bounds for the pinned 722-qubit code]
  #v(4pt)
  An elementary distance proof with explicit boundary accounting \
  Analytic proof · 11 November 2026
]

*Grade: THEOREM. Independently refereed and formalized in Lean.*

= Main theorem and explicit model <sec-model>

#theorem(<thm-main>, title: [main result])

For the two binary check matrices tabulated in @app-tables, proved in @app-input
to equal the formulas in this section,
$
H_X H_Z^T=0, quad
"rank"(H_X)="rank"(H_Z)=357, quad k=8,
$
and both sector distances and the CSS Pauli distance satisfy
$
d_X >= 17, quad 17 <= d_Z <= 20, quad 17 <= d_"Pauli" <= 20.
$
The support tables give the complete numerical definition of this instance.
They are the check arrays of `qldpc-challenge/codes/722-8-20.json` at revision
`8c87413d16b78cdd934b7b7a8592cddc81ae6eed`, with byte SHA-256
#text(size: 8pt)[`4ab209d0c450dc7a96e6054ed29322808be87ee52eb3002c51ab4531dcc91b15`].
The file identity is provenance: the mathematical proof uses the full support
tables printed here. The name's distance label is not a premise.
The main text proves the lower bound by exact polynomial cancellation and
disjoint weight accounting, then completes both bounds. @app-algebra and @app-boundary
supply full elementary proofs of the established algebraic prerequisites.
@app-input through @app-tables identify the fixed input and verify the upper witness.
All numerical inputs and manipulations are printed in this document.

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
dimensions are proved equal in @app-algebra. Define
$
d_X=min{ "wt"(w):w in K_X without S_X}, quad
d_Z=min{ "wt"(w):w in K_Z without S_Z}.
$
Both sets are nonempty by the dimension calculation in @app-algebra.
A CSS Pauli cycle is a pair $(w_X,w_Z)$ in $K_X times K_Z$.
It is trivial exactly when $(w_X,w_Z)$ belongs to $S_X times S_Z$.
Its weight is the cardinality of the union of the two physical supports;
$d_"Pauli"$ is the minimum weight of a nontrivial such pair. These are
the algebraic definitions used in @thm-main.


#pagebreak()
= Contribution and proof route <sec-contribution>

*Scope and attribution.* The polynomial description, the rectangular code
family and its dimension eight are established results of Liang, Eberhardt
and Chen @liang2025[Section II and Figure 1]. Polynomial stabilizer and
excitation maps belong to the module formalism of Haah
@haah2013[Sections 1–3]. The finite logical-space identification by one
boundary's syndrome is given explicitly by Breuckmann et al.
@tile2025[Section 4.3, Lemmas 4–5 and Theorem 3]. We do not claim these
structures as new. Their specialization is proved from elementary algebra
in @app-algebra and @app-boundary, without importing a topological-order assumption.

*Focus of this proof.* The main argument is @thm-run-exit. @lem-cheap-exit classifies
an exit with physical slice weights $2,1,1$: its feeding polynomial must
have three or four consecutive terms. @lem-exit-alternative turns that classification
into a choice of where an additional unit of weight must occur. The
allocation in @sec-accounting proves that these units
are disjoint, including at the two exceptional endpoints. This gives
$W>=18-epsilon>=17$. The final application derives both recurrences
directly from the physical checks and transfers coefficient weight to
sector and mixed-Pauli weight.

*Relation to earlier distance methods.* Polynomial cellular-automaton
propagation is established machinery @devakul2020[Section 2.1]. General
boundary-crossing bounds occur in Wang and Pryadko
@wang2026[Statement 7 and Appendix H]. Decomposing a word into initial,
terminal and intervening segments has precedents in active distances for
convolutional codes @host1999[Section III, Theorem 6]. Those encoder states
are not the physical slices used here; no reduction to that theorem is
assumed. The specific cheap-exit classification and allocation below are
the potential contribution. The literature search found no exact match,
but this document makes no claim of established priority. Its THEOREM
grade concerns mathematical correctness, not originality.

*Dependency guide.* The local proof in @sec-local through @sec-accounting needs only binary
polynomial arithmetic and adjacent nonemptiness. @app-boundary proves that
nontrivial physical logicals have that nonemptiness property. @sec-application
derives the physical recurrences and applies the local theorem. @app-algebra
supplies commutation, ranks and the elementary charge algebra; @app-input
identifies the submitted matrices; @app-witness proves the upper bound;
@app-tables prints the full numerical input. All referenced arguments are
contained here, and the references provide attribution rather than
unproved premises.

= Exact polynomial recurrences and local gap costs <sec-local>

#theorem(<thm-run-exit>, title: [local run-exit bound])
 Let $(a_i,b_i)_(i=0)^18$ be polynomial pairs over $bb(F)_2$, each
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

All polynomial identities below are exact, with no quotient reduction or
truncation. The degree cap is unnecessary for the local implication.

*Proof organization.* @lem-branch through @lem-four-slices establish directional branching and local
gap costs. @lem-run-propagation through @lem-exit-alternative establish short-run propagation and the run-exit
alternative. The run-counting section below partitions the excess without double counting and
proves the local strip theorem. Every needed local lemma is proved here.

== Elementary polynomial facts and a branch between zeros

For the local calculations only, rename the indeterminate in either
system as $T$, and put $t=T+T^2$. This renames a variable, not a recurrence.
A slice is empty if $w_i=0$, a singleton if $w_i=1$, and heavy if $w_i>=2$.
A zero-gap between consecutive zero indices $p<q$ has length $q-p$
and has $q-p-1$ interior slices, at indices $p+1,dots,q-1$.
A singleton pair has exactly one nonzero block, which is a monomial.
In particular $u+T^2v$ and $T^2u+v$ each have weight one whenever
$(u,v)$ is a singleton.

If $runs(p)$ counts maximal consecutive runs of exponents in the support of
$p$, with $runs(0)=0$, then
$ wt(t p)=wt((1+T)p)=2runs(p). $ <runs>
Indeed a run from exponent $c$ to $d$ contributes exactly $T^c+T^(d+1)$
to $(1+T)p$. Endpoints from distinct runs are distinct. A monomial shift
does not change weight. Thus $wt(t p)>=2$ for $p!=0$.
We also use $wt(u+v)<=wt(u)+wt(v)$ and the fact that $p(1)$ is the parity
of $wt(p)$. Both follow coefficient by coefficient over $bb(F)_2$.
The polynomial ring is a domain: the leading coefficient of a product
of two nonzero polynomials is the product of their leading coefficients,
hence is nonzero. Therefore nonzero factors can be cancelled.

#lemma(<lem-branch>, title: [directional branch])
 Suppose $1<=r<=17$ and slices $r-1,r+1$
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
$r=17$ in F would require the recurrence at index 19, and $r=1$ in B would require
the recurrence at index 1. Neither equation is among the hypotheses. No branch cost is
asserted at these exceptions.

== Local costs inside gaps

#lemma(<lem-gap-three>, title: [two occupied slices between zeros])
 If $0<=k<=15$, slices
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

#lemma(<lem-gap-four>, title: [three occupied slices between zeros])
 If $0<=k<=14$, slices
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

#lemma(<lem-four-slices>, title: [four occupied slices next to a zero])
 In system F, an empty
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
slices are occupied. @lem-four-slices applies from the left endpoint in F and from
the right endpoint in B. These endpoints satisfy $k<=13$ and $R>=5$,
respectively. Thus such a gap has interior weight at least five.
All monomials counted in the proofs have distinct exponents; none may be
discarded if an exponent exceeds 18. Such an identity would violate the
hypotheses rather than supply a further cancellation.


= Short runs and their exits <sec-runs>

Orient the list of zero slices in the forcing direction: increasing index
for F and decreasing index for B. A _short gap_ is a gap of length two
between successive zero slices. A _short run_ is a maximal sequence of
$m>=1$ consecutive short gaps. Its $m$ middle slices are nonempty by
@adjacent. The _exit target_ is the next slice after its last zero in the
forcing direction. It either lies inside the following longer gap, lies
in the tail after the last zero, or falls outside the index range.

#lemma(<lem-run-propagation>, title: [exact propagation and exceptional exits])
 Write the active
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

*Proof.* @lem-branch gives the active block of every middle. In F, at the next
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

= Cheap-exit classification <sec-cheap>

#lemma(<lem-cheap-exit>, title: [cheap exit forces a feed of weight three or four])
 Suppose three
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

#lemma(<lem-exit-alternative>, title: [exit alternative])
 Suppose a short run feeds a longer zero gap
$D$ of length $d>=4$. Let $P$ be its final middle polynomial and let
$E_D$ be the excess inside $D$, namely the sum of $w_i-1$ over its interior.
Then
$ E_D>=2 quad "or" quad wt(P)>=3. $ <exit-alternative>
For length three, $E_D>=2$ unconditionally.

*Proof.* The exit target is the first interior slice and has weight at
least two by @lem-run-propagation. If $E_D<=1$, that slice has weight exactly two and
every other interior slice is a singleton. There are at least three
interior slices, so @lem-cheap-exit applies. Its equations are tested: a gap of
length at least four requires $r+5<=18$ in F or $r-5>=0$ in B, stronger
than the respective index ranges in @lem-cheap-exit. Thus $wt(P)>=3$.
For length three use @lem-gap-three. $square$

= Disjoint excess-weight allocation <sec-accounting>

If $z=0$, all nineteen slices are occupied, giving $W>=19$ and
$E>=0>=z-1-epsilon$. Hence assume $z>=1$. There are $z-1$ successive-zero
gaps. All have length at least two by @adjacent. Let $G$ count short gaps,
$M=z-1-G$ count longer gaps, and $R_2$ count maximal short runs. Every
interior slice of a successive-zero gap is occupied, so its contribution
to $E$ is exactly its weight minus one.

*Baseline inside runs.* In a short run of $m$ gaps, reserve one excess
unit at every middle after the first, totalling $m-1$. These units exist by
@lem-run-propagation. Across all short runs this reserves $G-R_2$ units.

*Baseline inside longer gaps.* Reserve one excess unit in every longer
gap, totalling $M$. Length three has at least two units by @lem-gap-three.
Length four has at least one by @lem-gap-four. Length at least five has at least
one in the first four interior slices in forcing order by @lem-four-slices.
These longer-gap interiors are disjoint from each other and from all
short-run middles. Thus the baseline reserves $G-R_2+M$ units.

*An additional unit for each run that has an exit.* If a run is followed
by a gap of length three, that gap has a second excess unit after its
reserved baseline. If its following gap has length at least four, @lem-exit-alternative
says either the same second gap unit exists, or the run's terminal middle
has weight at least three. In the latter case that middle has at least two
excess units. At most one was reserved there in the run baseline: one for
$m>=2$, zero for $m=1$. At least one further unit therefore remains.
Knowing only that the terminal middle was heavy would not suffice;
@lem-cheap-exit supplies the needed weight at least three.

Distinct short runs have distinct terminal middles and distinct following
longer gaps. Run interiors are disjoint from longer-gap interiors.
Thus none of these selected additional units is a reserved baseline unit
or a unit already selected for another run.

If instead the final run exits into an on-board tail, @lem-run-propagation makes its
target heavy. Its excess unit lies outside all baseline regions and supplies
that run's additional unit. Only a run with a missing exit receives no
required additional unit. @lem-run-propagation identifies precisely $epsilon$ such runs.
Therefore the number of additional units is at least $R_2-epsilon$, and
$ E &>= (G-R_2+M)+(R_2-epsilon) \
    &= G+M-epsilon=z-1-epsilon. $
Finally,
$ W=19-z+E>=18-epsilon>=17. $
This includes $z=1$, where $G=M=R_2=epsilon=0$ and $W>=18$.
The local strip theorem is proved. $square$

*Endpoint distinction.* The only possible discount is the nonexistent
target at index 19 in F or $-1$ in B. An existing target at index 18 in F
or index 0 in B still costs an excess unit, even when no later zero exists.
The result gives eighteen whenever that missing-exit configuration is absent.

= Elementary derivation for the physical code <sec-application>

The inputs from the appendices are commutation and ranks (@thm-ranks),
complete boundary charges (@thm-x-charge and @thm-z-charge), and adjacent nonemptiness
(@thm-cuts). Each has a full elementary proof below. We now derive the
local equations, keeping the two orientations separate.


*X sector.* Let $w=(u,v)$ be any nontrivial X logical. Expand its two
physical blocks in rows as
$u=sum_(i=0)^18 x^i a_i (y)$ and $v=sum_(i=0)^18 x^i b_i (y)$.
Each slice has degree at most 18. Its full syndrome vanishes at every
row $2<=i<=18$ by @thm-x-charge. Extracting that row from
$g u+f v$, using $g=1+x^2(y+y^2)$ and $f=x+x^2+y^2$, gives
$
0=a_i+(y+y^2)a_(i-2)+b_(i-1)+b_(i-2)+y^2b_i.
$
In characteristic two, moving $a_i$ to the other side leaves the forward
system of @thm-run-exit. @thm-cuts gives adjacent-row nonemptiness. The sum of
the slice coefficient weights is exactly the physical weight of $w$:
each A or B coordinate lies in exactly one row. Thus @thm-run-exit proves
$"wt"(w)>=17$. The argument applies to every nontrivial representative,
without choosing a minimum or changing its weight by a stabilizer.

*Z sector.* Define $M$ by reflecting coordinates $(i,j)$ to
$(18-i,18-j)$ and exchanging blocks A and B. Let $w$ be any nontrivial
Z logical and write $M(w)=(u',v')$ in columns:
$u'=sum_(j=0)^18 y^j a_j (x)$ and $v'=sum_(j=0)^18 y^j b_j (x)$.
Reflection and block exchange preserve the square and physical weight,
so every slice has degree at most 18. @thm-z-charge identifies the tested
columns of $g u'+f v'$ as $2<=j<=18$. The coefficient in one such column is
$
0=a_j+x^2a_(j-1)+x^2a_(j-2)+(x+x^2)b_j+b_(j-2).
$
Rearranging in characteristic two gives precisely the backward system of
@thm-run-exit. The Z-cut argument of @thm-cuts gives adjacent nonemptiness for
these reflected columns. Their total coefficient weight equals the weight
of $M(w)$, hence equals the original physical weight of $w$. @thm-run-exit
therefore proves $"wt"(w)>=17$ for every nontrivial Z representative.

*Mixed Pauli sector.* A nontrivial pair $(w_X,w_Z)$ has a nontrivial X or
Z component, since otherwise it belongs to $S_X times S_Z$. That component
has weight at least seventeen by the preceding two paragraphs. Its support
is contained in the union defining the Pauli support, so the Pauli weight
is at least seventeen. The minima exist by the dimension argument in @app-algebra.

@thm-ranks supplies commutation and both ranks 357. The dimension
calculation immediately after @thm-ranks supplies $k=8$. The sector and Pauli arguments
above prove the lower-bound assertions for the polynomial formulas.
The fixed-input identity and upper witness complete the argument as follows.

== Input identification and the upper bound

@thm-input proves that the fixed support tables in @app-tables are exactly
these polynomial-defined matrices in the stated order. Thus the preceding
lower bound applies to the submitted input, not only to an abstract model.

@thm-witness supplies an X cycle of weight 23 and a Z cycle of weight 20.
Their complete supports and all multiplication terms are printed in
@app-witness. Their supports intersect in exactly $\{65\}$, so their pairing
is one. A Z stabilizer pairs to zero with every X cycle; hence the Z cycle
is nontrivial. Its pure-Z Pauli operator is nontrivial with the same weight.
Consequently $d_Z<=20$ and $d_"Pauli"<=20$.

Combining these witnesses with the lower bound, commutation and ranks gives
$ "rank"(H_X)="rank"(H_Z)=357, quad k=8, $
$ d_X>=17, quad 17<=d_Z<=20, quad 17<=d_"Pauli"<=20. $
This proves @thm-main. The witness supplies no lower bound of twenty. $square$

#block[
  #set par(justify: false)
  *Formal counterpart.* The Lean capstones are:

  #text(size: 8.5pt)[`QldpcVerification.Rectangle722Submitted.parameters_and_bounds`] \
  #text(size: 8.5pt)[`QldpcVerification.Rectangle722Submitted.pauli_bounds`]

  The local proof is formalized in the `Planar/StripRunLocal`,
  `StripRunCounting`, `StripRunRecurrence` and `StripRunClassification`
  modules. Lean verification checks these arguments; it is not a premise
  of the hand proof.
]

#pagebreak()
#counter(heading).update(0)
#set heading(numbering: "A.1", supplement: [Appendix])
#let theorem = statement.with(kind: "Theorem", appendix: true)
= Established algebra: elementary proofs <app-algebra>
#counter(figure.where(kind: "Theorem")).update(0)

This appendix supplies the standard prerequisites used in the main text.
The polynomial formalism follows Haah @haah2013 and the planar construction
of Liang, Eberhardt and Chen @liang2025[Appendix A and Section II]. The
bulk kernel statement is a two-generator Koszul exactness statement
@tile2025[Sections 4.1–4.2]. Here monic division and a two-by-two determinant
verify it directly, avoiding any appeal to unique factorization. The
rank and dimension claims specialize the known rectangular family; they
are reproved for the exact anchor ranges of @sec-model.

== Elementary algebra and dimension facts

#theorem(<thm-elementary>, title: [tools used below])

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

== Commutation and the two check ranks

#theorem(<thm-ranks>)

The matrices in @sec-model commute and both have rank 357.

=== Commutation for every pair of anchors

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

=== X independence

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

=== Z independence

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
a symmetry of the code. This completes @thm-ranks. $square$

By @thm-elementary and commutation,
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

== Elementary bulk exactness without unique factorization

#theorem(<thm-bulk>)

For polynomials $u,v$ in $F[x,y]$,
$
g u+f v=0 quad <==> quad
(u,v)=(f h,g h) \
"for a unique " h in F[x,y].
$
Among pairs supported in $Q$, this kernel has dimension $17^2=289$.

*Proof.* Regard the ring as $F[y][x]$. The polynomial
$f=x^2+x+y^2$ is monic in $x$. @thm-elementary gives a unique division
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

== The degree-eight charge algebra and its two bases

#theorem(<thm-charge-algebra>)

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


= Established boundary charges and cut transport <app-boundary>
#counter(figure.where(kind: "Theorem")).update(0)

The construction in this appendix specializes the known boundary-syndrome
map. Breuckmann et al. prove that the bottom-boundary syndrome modulo the
stabilizer ideal identifies the finite logical space
@tile2025[Section 4.3, Theorem 3]; Liang, Eberhardt and Chen state the
corresponding planar dimension formula @liang2025[Section III.2, equation (6)].
We establish the required finite statements directly by coefficient
spaces, explicit residue maps and dimension counts. No bulk-to-boundary
completeness assertion is left as an assumption. The final cut formulas
are elementary specializations of the boundary-crossing principle
@wang2026[Statement 7 and Appendix H].

== X boundary image and complete X charge

#theorem(<thm-x-charge>)

The low-boundary residue defined below induces an isomorphism
$K_X/S_X arrow cal(A)$.

=== Full-syndrome image and its ambient coefficient space

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
@thm-bulk. It lies in $K_X$, since zero full syndrome implies
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

=== Stabilizers have zero low charge

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

=== Surjectivity and injectivity on the quotient

Given $a in cal(A)$, choose $ell in E_l$ and $h in E_h$ with
$rho(ell)=rho(h)=a$, using the two surjective restrictions.
Then $phi(ell+h)=a+a=0$. Since $D=ker phi$, there exists a physical
cycle $w$ with $sigma(w)=ell+h$. It has $c_X (w)=a$.
Thus $c_X:K_X arrow cal(A)$ is onto.
Its kernel has dimension $365-8=357$ and contains $S_X$, whose
dimension is 357. Hence $ker c_X=S_X$.
The induced quotient map is well-defined because it kills $S_X$;
it is onto by surjectivity of $c_X$ and injective by the kernel equality.
This proves @thm-x-charge. $square$

== Z boundary image and complete Z charge

#theorem(<thm-z-charge>)

The reflected low-column charge defined here induces an isomorphism
$K_Z/S_Z arrow cal(A)$.

=== Reflection and all tested coefficients

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
Put $D'=sigma(K'_Z)$. @thm-bulk applies to these polynomial pairs:
the full-syndrome kernel in the square has dimension 289, and lies in
$K'_Z$ because its tested coefficients are zero. Hence $dim D'=76$.

=== Total residue and the dual image

Define $phi':E' arrow cal(A)$ by $phi'(ell+h)=rho(ell)+rho(h)$.
The vectors $1,x,dots,x^7$ in $E'_l$ map to the second basis of
@thm-charge-algebra. The vectors $y^19,y^19 x,dots,y^19 x^7$ in $E'_h$
map to that basis multiplied by the unit $y^19$.
Thus both restrictions of $phi'$ are onto. It has rank eight and
kernel dimension 76.
Every syndrome is killed by $rho$, so $D' subset.eq ker phi'$.
These are subspaces of $E'$ of the same dimension, proving
$D'=ker phi'$.

=== All reflected stabilizers have zero low-column residue

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

=== Surjectivity and the original Z quotient

For any $a in cal(A)$, choose $ell in E'_l$ and $h in E'_h$
both of residue $a$. Their sum has total residue zero, so belongs to
$ker phi'=D'$. There is $w' in K'_Z$ with this full syndrome and
$c'_Z (w')=a$. Thus $c'_Z$ is onto.
Its kernel has dimension $365-8=357$ and contains the
357-dimensional $S'_Z$, so these spaces are equal.
Define on original Z cycles $c_Z (w)=c'_Z (M(w))$.
The invertible permutation $M$ gives surjectivity of $c_Z$ and
$ker c_Z=S_Z$. Hence it induces the claimed isomorphism.
This proves @thm-z-charge without assuming an X/Z symmetry of the code.
$square$

== Row and column transport inequalities

#theorem(<thm-cuts>)

For every nontrivial X logical, if $w_i$ is its weight in physical row
$i$ and $W=sum_(i=0)^18 w_i$, then
$
w_i+w_(i+1)>=1 " for " 0<=i<=17,
quad W>=9+ceil((w_0+w_18)/2).
$
For every nontrivial Z logical, the corresponding assertions hold with
physical column weights.

=== X cuts: exact flux and weight count

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
For a nontrivial logical this value is nonzero by @thm-x-charge.
If physical rows $k-2$ and $k-1$ were both empty, every coefficient in
$F_k$ would be zero, a contradiction. Hence
$w_i+w_(i+1)>=1$ for every $0<=i<=17$.
Summing all eighteen inequalities counts the outer rows once and all
other rows twice:
$
18<=sum_(i=0)^17(w_i+w_(i+1))=2W-w_0-w_18.
$
Since $W$ is an integer, the claimed X weight inequality follows.

=== Z cuts: explicit flux after reflection

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
If $w$ is a nontrivial Z logical, @thm-z-charge makes this value nonzero.
Two consecutive empty columns of $M(w)$ would make $G_k=0$.
Thus its column weights $w'_j$ satisfy
$w'_j+w'_(j+1)>=1$ for $0<=j<=17$. Summing gives
$2W-w'_0-w'_18>=18$, because $M$ preserves total weight.
If $w_j$ are the original column weights, the reflection and block
exchange give $w'_j=w_(18-j)$. Every adjacent original column pair
therefore also has total weight at least one, and
$w'_0+w'_18=w_18+w_0$. This proves the claimed Z inequality. $square$



= Fixed-input identification <app-input>
#counter(figure.where(kind: "Theorem")).update(0)

#theorem(<thm-input>, title: [equality with the numerical tables])
 Each row in @app-tables
is exactly the support of the corresponding polynomial-defined check above,
in the stated order and physical coordinates. Thus all model results apply
to the matrices defined by these complete numerical tables.

*Proof and complete integer manipulation.* Every X row number has the unique
form $r=17a+b$ with $0<=a<=20$, $0<=b<=16$. Every Z row number has the unique
form $r=21c+d$ with $0<=c<=16$, $0<=d<=20$. Division by 17 or 21 gives these
quotients and remainders for every index 0 through 356. Uniqueness follows because
two remainders differ in absolute value by less than the divisor. Thus these
ranges exhaust the 357 rows in each table.

For X put $u=a-2$. The six terms before clipping are
$A(u+1,b), A(u+2,b), A(u,b+2), B(u,b), B(u+2,b+1), B(u+2,b+2)$.
All columns are allowed. The first A term is retained for $1<=a<=19$;
the second for $0<=a<=18$; the third for $2<=a<=20$. The first B term
is retained for $2<=a<=20$ and the last two for $0<=a<=18$.
Substituting physical labels and sorting gives these five exhaustive cases:

#table(columns: (1fr, 4fr), inset: 4pt,
  table.header([X condition], [Sorted support]),
  [$a=0$], [$b,b+362,b+363$],
  [$a=1$], [$b,b+19,b+381,b+382$],
  [$2<=a<=18$], [For $U=19a+b$: $U-36,U-19,U,U+323,U+362,U+363$],
  [$a=19$], [$b+325,b+342,b+684$],
  [$a=20$], [$b+344,b+703$],
)

For Z put $v=c+2$. The six terms before clipping are
$A(v,d), A(v-2,d-1), A(v-2,d-2), B(v-1,d), B(v-2,d), B(v,d-2)$.
All rows are allowed. The first A term and first two B terms are retained
for $0<=d<=18$; the second A term for $1<=d<=19$; the third A and last B
terms for $2<=d<=20$. Substitution and sorting give:

#table(columns: (1fr, 4fr), inset: 4pt,
  table.header([Z condition], [Sorted support]),
  [$d=0$], [$19c+38,19c+361,19c+380$],
  [$d=1$], [$19c,19c+39,19c+362,19c+381$],
  [$2<=d<=18$], [For $U=19c+d$: $U-2,U-1,U+38,U+361,U+380,U+397$],
  [$d=19$], [$19c+17,19c+18,19c+416$],
  [$d=20$], [$19c+18,19c+417$],
)

The five X conditions partition the integers 0 through 20, as do the five Z
conditions. Each displayed list is strictly increasing, so its terms do not
coincide or cancel. The two five-case expressions evaluated at the row and
anchor indices printed in @app-tables give exactly its complete tables.
This is a fixed integer identity: its inputs are all 714 printed rows; its
manipulation is the displayed coordinate substitution, clipping and sorting;
its result is the two five-case tables. For example X row 0 gives
$(0,362,363)$, and Z row 356, with $(c,d)=(16,20)$, gives $(322,721)$.
All remaining rows include their anchors and entries, so the entire identity
is reproducible by the stated integer additions. No unspecified data is used.
This proves equality of the numerical and polynomial-defined matrices. $square$

#pagebreak()
= Explicit upper witnesses and their verification <app-witness>
#counter(figure.where(kind: "Theorem")).update(0)

#theorem(<thm-witness>, title: [upper bound])
 The two explicitly listed vectors below are
opposite-check cycles with pairing one. The Z vector is a nontrivial logical
of weight 20; therefore $d_Z<=20$ and $d_"Pauli"<=20$. The X partner is
also nontrivial and has weight 23.

== Model and check rows

All qubit labels start at zero. $A(i,j)=19i+j$ and $B(i,j)=361+19i+j$,
where $0<=i,j<=18$. The vector of a support has coefficient one at each
listed qubit and zero elsewhere. Work over the two-element field, so two
copies of any monomial cancel. Exponents in this appendix are ordinary
integers; there is no periodic wrap.

Let $Q$ be the square of integer exponent pairs with $0<=i,j<=18$. A physical
vector is a pair $(u,v)$ of polynomials supported in $Q$, for species A and B.
Let $P$ delete all terms outside $Q$ in each component of a Laurent-polynomial
pair. Put $f=x+x^2+y^2$ and $g=1+x^2y+x^2y^2$. The bar operation
replaces $x$ and $y$ by their inverses, so
$ overline(f)=x^(-1)+x^(-2)+y^(-2), quad
  overline(g)=1+x^(-2)y^(-1)+x^(-2)y^(-2). $
Define the binary check rows by

$ H_X [(a,b),:] = P(x^a y^b (f,g)), quad -2 <= a <= 18, quad 0 <= b <= 16; $
$ H_Z [(c,d),:] = P(x^c y^d (overline(g),overline(f))),
  quad 2 <= c <= 18, quad 0 <= d <= 20. $

These are actual integer anchor coordinates. They correspond to the input
indices $(a+2,b)$ and $(c-2,d)$, respectively. Both matrices have 357 rows and
722 columns. The dot product sums the products of corresponding A and B
coefficients over $Q$. No rank assertion is needed for this witness argument.

== Coefficients are check dot products

Write $[i,j]h$ for the coefficient of $x^i y^j$ in a Laurent polynomial $h$,
with coefficient zero at absent exponents. Multiplication is the finite
convolution
$ [r,s](h u)=sum_((i,j) in bb(Z)^2) ([r-i,s-j]h)([i,j]u). $
The sum has finitely many nonzero terms because the supports are finite.
Because $u$ and $v$ vanish outside $Q$, projecting a check row with $P$ does not
change its dot product with $(u,v)$. The Z row at $(c,d)$ has A coefficient
$[i-c,j-d]overline(g)=[c-i,d-j]g$, and the analogous B coefficient uses $f$.
Consequently convolution gives

$ H_Z [(c,d),:] dot (u,v) = [c,d](g u + f v). $

For the X row at $(a,b)$, the A coefficient is
$[i-a,j-b]f=[a-i,b-j]overline(f)$, and the B coefficient similarly uses
$overline(g)$. Hence

$ H_X [(a,b),:] dot (u,v) = [a,b](overline(f) u + overline(g) v). $

These identities derive the full X syndrome $g u+f v$ and full Z syndrome
$overline(f)u+overline(g)v$ directly from the defined rows. Only coefficients at
retained check anchors are tested; the full polynomials may be nonzero outside
those anchors. No matrix computation or Lean result is a premise of this derivation.

== Commutation and retention of every overlap

Before projection, the X row at $(a,b)$ has every $y$ exponent in $[b,b+2]$,
which lies in $[0,18]$. Thus all its columns lie on the physical board even
when some $x$ exponents do not. Before projection, the Z row at $(c,d)$ has
every $x$ exponent in $[c-2,c]$, which lies in $[0,18]$. Thus all its rows lie
on the physical board even when some $y$ exponents do not. Any common
monomial of these two rows, in either species, therefore has both coordinates
in $[0,18]$. Projection discards no term that contributes to their dot product.

For finite Laurent polynomials $h$ and $k$, their full-plane coefficient dot
product is the constant coefficient of $h overline(k)$: each constant term pairs
equal exponent coordinates. Apply this componentwise to the two unprojected
check rows. The result is the constant coefficient of

$ x^(a-c) y^(b-d) (f g + g f). $

Polynomial multiplication commutes, and the field has characteristic two,
so $f g+g f=0$. The full-plane row dot product is zero; retention of every
overlap proves the same for the projected physical rows. Hence
$H_X H_Z^T = 0$, so the rows define a commuting CSS stabilizer model.

== The two supplied supports

X support (23 distinct qubits):

65, 103, 104, 105, 142, 162, 199, 219, 220, 332, 390, 407, 426, 504, 541, 560, 561, 579, 598, 617, 619, 636, 655.

Z support (20 distinct qubits):

46, 47, 61, 63, 65, 66, 80, 97, 131, 150, 167, 409, 424, 425, 446, 448, 456, 486, 487, 526.

== Complete multiplication and cancellation

Each pair $(i,j)$ below denotes $x^i y^j$. Each input row contributes exactly
the three exponent pairs in its product column. Nothing is truncated before
multiplication. The cancellation tables list a multiset $C$: every listed
entry is removed twice. Consequently the full product multiset is exactly
$R+C+C$, where $R$ is the stated residual multiset. These are fixed integer
identities that can be checked by sorting the product columns and tallying.

=== X multiplication

#table(columns: (40pt, 90pt, 1fr), inset: 3pt,
  table.header([Qubit], [Input monomial], [Three product exponents]),
  [65], [$A(3, 8)$], [$(3, 8), (5, 9), (5, 10)$],
  [103], [$A(5, 8)$], [$(5, 8), (7, 9), (7, 10)$],
  [104], [$A(5, 9)$], [$(5, 9), (7, 10), (7, 11)$],
  [105], [$A(5, 10)$], [$(5, 10), (7, 11), (7, 12)$],
  [142], [$A(7, 9)$], [$(7, 9), (9, 10), (9, 11)$],
  [162], [$A(8, 10)$], [$(8, 10), (10, 11), (10, 12)$],
  [199], [$A(10, 9)$], [$(10, 9), (12, 10), (12, 11)$],
  [219], [$A(11, 10)$], [$(11, 10), (13, 11), (13, 12)$],
  [220], [$A(11, 11)$], [$(11, 11), (13, 12), (13, 13)$],
  [332], [$A(17, 9)$], [$(17, 9), (19, 10), (19, 11)$],
  [390], [$B(1, 10)$], [$(2, 10), (3, 10), (1, 12)$],
  [407], [$B(2, 8)$], [$(3, 8), (4, 8), (2, 10)$],
  [426], [$B(3, 8)$], [$(4, 8), (5, 8), (3, 10)$],
  [504], [$B(7, 10)$], [$(8, 10), (9, 10), (7, 12)$],
  [541], [$B(9, 9)$], [$(10, 9), (11, 9), (9, 11)$],
  [560], [$B(10, 9)$], [$(11, 9), (12, 9), (10, 11)$],
  [561], [$B(10, 10)$], [$(11, 10), (12, 10), (10, 12)$],
  [579], [$B(11, 9)$], [$(12, 9), (13, 9), (11, 11)$],
  [598], [$B(12, 9)$], [$(13, 9), (14, 9), (12, 11)$],
  [617], [$B(13, 9)$], [$(14, 9), (15, 9), (13, 11)$],
  [619], [$B(13, 11)$], [$(14, 11), (15, 11), (13, 13)$],
  [636], [$B(14, 9)$], [$(15, 9), (16, 9), (14, 11)$],
  [655], [$B(15, 9)$], [$(16, 9), (17, 9), (15, 11)$],
)

Cancellation multiset $C$ (each entry cancels twice):

$(2, 10)$, $(3, 8)$, $(3, 10)$, $(4, 8)$, $(5, 8)$, $(5, 9)$, $(5, 10)$, $(7, 9)$, $(7, 10)$, $(7, 11)$, $(7, 12)$, $(8, 10)$, $(9, 10)$, $(9, 11)$, $(10, 9)$, $(10, 11)$, $(10, 12)$, $(11, 9)$, $(11, 10)$, $(11, 11)$, $(12, 9)$, $(12, 10)$, $(12, 11)$, $(13, 9)$, $(13, 11)$, $(13, 12)$, $(13, 13)$, $(14, 9)$, $(14, 11)$, $(15, 9)$, $(15, 11)$, $(16, 9)$, $(17, 9)$.

Residual multiset $R$: $(1, 12)$, $(19, 10)$, $(19, 11)$.

#pagebreak()
=== Z multiplication

#table(columns: (40pt, 90pt, 1fr), inset: 3pt,
  table.header([Qubit], [Input monomial], [Three product exponents]),
  [46], [$A(2, 8)$], [$(1, 8), (0, 8), (2, 6)$],
  [47], [$A(2, 9)$], [$(1, 9), (0, 9), (2, 7)$],
  [61], [$A(3, 4)$], [$(2, 4), (1, 4), (3, 2)$],
  [63], [$A(3, 6)$], [$(2, 6), (1, 6), (3, 4)$],
  [65], [$A(3, 8)$], [$(2, 8), (1, 8), (3, 6)$],
  [66], [$A(3, 9)$], [$(2, 9), (1, 9), (3, 7)$],
  [80], [$A(4, 4)$], [$(3, 4), (2, 4), (4, 2)$],
  [97], [$A(5, 2)$], [$(4, 2), (3, 2), (5, 0)$],
  [131], [$A(6, 17)$], [$(5, 17), (4, 17), (6, 15)$],
  [150], [$A(7, 17)$], [$(6, 17), (5, 17), (7, 15)$],
  [167], [$A(8, 15)$], [$(7, 15), (6, 15), (8, 13)$],
  [409], [$B(2, 10)$], [$(2, 10), (0, 9), (0, 8)$],
  [424], [$B(3, 6)$], [$(3, 6), (1, 5), (1, 4)$],
  [425], [$B(3, 7)$], [$(3, 7), (1, 6), (1, 5)$],
  [446], [$B(4, 9)$], [$(4, 9), (2, 8), (2, 7)$],
  [448], [$B(4, 11)$], [$(4, 11), (2, 10), (2, 9)$],
  [456], [$B(5, 0)$], [$(5, 0), (3, -1), (3, -2)$],
  [486], [$B(6, 11)$], [$(6, 11), (4, 10), (4, 9)$],
  [487], [$B(6, 12)$], [$(6, 12), (4, 11), (4, 10)$],
  [526], [$B(8, 13)$], [$(8, 13), (6, 12), (6, 11)$],
)

Cancellation multiset $C$ (each entry cancels twice):

$(0, 8)$, $(0, 9)$, $(1, 4)$, $(1, 5)$, $(1, 6)$, $(1, 8)$, $(1, 9)$, $(2, 4)$, $(2, 6)$, $(2, 7)$, $(2, 8)$, $(2, 9)$, $(2, 10)$, $(3, 2)$, $(3, 4)$, $(3, 6)$, $(3, 7)$, $(4, 2)$, $(4, 9)$, $(4, 10)$, $(4, 11)$, $(5, 0)$, $(5, 17)$, $(6, 11)$, $(6, 12)$, $(6, 15)$, $(7, 15)$, $(8, 13)$.

Residual multiset $R$: $(3, -2)$, $(3, -1)$, $(4, 17)$, $(6, 17)$.

== Cycle, nontriviality, and upper bound

The X residual is $x y^12+x^19 y^10+x^19 y^11$. Its first coordinates,
1 and 19, are outside the retained Z-check range 2 through 18.
The Z residual is $x^3 y^(-2)+x^3 y^(-1)+x^4 y^17+x^6 y^17$.
Its second coordinates, $-2$, $-1$, and $17$, are outside the retained X-check
range 0 through 16. Both actual opposite-check syndromes therefore vanish.

The displayed supports intersect in exactly $\{65\}$, so their binary dot
product is one. Every Z stabilizer is a sum of Z-check rows and pairs to
zero with the X cycle. Thus the displayed Z vector cannot be a Z stabilizer.
The same argument with X and Z interchanged makes the X vector nontrivial.
Counting the distinct Z labels gives weight 20; the X partner has weight 23.

The pure-Z Pauli operator placing Z on the 20 listed qubits and identity
elsewhere commutes with every stabilizer and is nontrivial modulo stabilizers.
Its Pauli weight is exactly 20. Hence the Z-sector minimum and the minimum
nontrivial Pauli weight are at most 20. The X partner only supplies an
X-sector upper bound of 23. No lower bound of 20 follows from these witnesses.


#pagebreak()
= Complete numerical support matrices <app-tables>
#counter(figure.where(kind: "Theorem")).update(0)
#set par(justify: false)

Rows and qubits are numbered from zero. Each row is the binary vector with
ones precisely at its displayed support. The X and Z tables retain input order.
Their anchors specify the unique row formula in @thm-input. This appendix is
the complete numerical input to the theorem.

== X supports

#table(columns: (40pt, 80pt, 1fr), inset: 3pt,
  table.header([Row], [Anchor], [Physical support]),
  [0], [(-2, 0)], [0, 362, 363],
  [1], [(-2, 1)], [1, 363, 364],
  [2], [(-2, 2)], [2, 364, 365],
  [3], [(-2, 3)], [3, 365, 366],
  [4], [(-2, 4)], [4, 366, 367],
  [5], [(-2, 5)], [5, 367, 368],
  [6], [(-2, 6)], [6, 368, 369],
  [7], [(-2, 7)], [7, 369, 370],
  [8], [(-2, 8)], [8, 370, 371],
  [9], [(-2, 9)], [9, 371, 372],
  [10], [(-2, 10)], [10, 372, 373],
  [11], [(-2, 11)], [11, 373, 374],
  [12], [(-2, 12)], [12, 374, 375],
  [13], [(-2, 13)], [13, 375, 376],
  [14], [(-2, 14)], [14, 376, 377],
  [15], [(-2, 15)], [15, 377, 378],
  [16], [(-2, 16)], [16, 378, 379],
  [17], [(-1, 0)], [0, 19, 381, 382],
  [18], [(-1, 1)], [1, 20, 382, 383],
  [19], [(-1, 2)], [2, 21, 383, 384],
  [20], [(-1, 3)], [3, 22, 384, 385],
  [21], [(-1, 4)], [4, 23, 385, 386],
  [22], [(-1, 5)], [5, 24, 386, 387],
  [23], [(-1, 6)], [6, 25, 387, 388],
  [24], [(-1, 7)], [7, 26, 388, 389],
  [25], [(-1, 8)], [8, 27, 389, 390],
  [26], [(-1, 9)], [9, 28, 390, 391],
  [27], [(-1, 10)], [10, 29, 391, 392],
  [28], [(-1, 11)], [11, 30, 392, 393],
  [29], [(-1, 12)], [12, 31, 393, 394],
  [30], [(-1, 13)], [13, 32, 394, 395],
  [31], [(-1, 14)], [14, 33, 395, 396],
  [32], [(-1, 15)], [15, 34, 396, 397],
  [33], [(-1, 16)], [16, 35, 397, 398],
  [34], [(0, 0)], [2, 19, 38, 361, 400, 401],
  [35], [(0, 1)], [3, 20, 39, 362, 401, 402],
  [36], [(0, 2)], [4, 21, 40, 363, 402, 403],
  [37], [(0, 3)], [5, 22, 41, 364, 403, 404],
  [38], [(0, 4)], [6, 23, 42, 365, 404, 405],
  [39], [(0, 5)], [7, 24, 43, 366, 405, 406],
  [40], [(0, 6)], [8, 25, 44, 367, 406, 407],
  [41], [(0, 7)], [9, 26, 45, 368, 407, 408],
  [42], [(0, 8)], [10, 27, 46, 369, 408, 409],
  [43], [(0, 9)], [11, 28, 47, 370, 409, 410],
  [44], [(0, 10)], [12, 29, 48, 371, 410, 411],
  [45], [(0, 11)], [13, 30, 49, 372, 411, 412],
  [46], [(0, 12)], [14, 31, 50, 373, 412, 413],
  [47], [(0, 13)], [15, 32, 51, 374, 413, 414],
  [48], [(0, 14)], [16, 33, 52, 375, 414, 415],
  [49], [(0, 15)], [17, 34, 53, 376, 415, 416],
  [50], [(0, 16)], [18, 35, 54, 377, 416, 417],
  [51], [(1, 0)], [21, 38, 57, 380, 419, 420],
  [52], [(1, 1)], [22, 39, 58, 381, 420, 421],
  [53], [(1, 2)], [23, 40, 59, 382, 421, 422],
  [54], [(1, 3)], [24, 41, 60, 383, 422, 423],
  [55], [(1, 4)], [25, 42, 61, 384, 423, 424],
  [56], [(1, 5)], [26, 43, 62, 385, 424, 425],
  [57], [(1, 6)], [27, 44, 63, 386, 425, 426],
  [58], [(1, 7)], [28, 45, 64, 387, 426, 427],
  [59], [(1, 8)], [29, 46, 65, 388, 427, 428],
  [60], [(1, 9)], [30, 47, 66, 389, 428, 429],
  [61], [(1, 10)], [31, 48, 67, 390, 429, 430],
  [62], [(1, 11)], [32, 49, 68, 391, 430, 431],
  [63], [(1, 12)], [33, 50, 69, 392, 431, 432],
  [64], [(1, 13)], [34, 51, 70, 393, 432, 433],
  [65], [(1, 14)], [35, 52, 71, 394, 433, 434],
  [66], [(1, 15)], [36, 53, 72, 395, 434, 435],
  [67], [(1, 16)], [37, 54, 73, 396, 435, 436],
  [68], [(2, 0)], [40, 57, 76, 399, 438, 439],
  [69], [(2, 1)], [41, 58, 77, 400, 439, 440],
  [70], [(2, 2)], [42, 59, 78, 401, 440, 441],
  [71], [(2, 3)], [43, 60, 79, 402, 441, 442],
  [72], [(2, 4)], [44, 61, 80, 403, 442, 443],
  [73], [(2, 5)], [45, 62, 81, 404, 443, 444],
  [74], [(2, 6)], [46, 63, 82, 405, 444, 445],
  [75], [(2, 7)], [47, 64, 83, 406, 445, 446],
  [76], [(2, 8)], [48, 65, 84, 407, 446, 447],
  [77], [(2, 9)], [49, 66, 85, 408, 447, 448],
  [78], [(2, 10)], [50, 67, 86, 409, 448, 449],
  [79], [(2, 11)], [51, 68, 87, 410, 449, 450],
  [80], [(2, 12)], [52, 69, 88, 411, 450, 451],
  [81], [(2, 13)], [53, 70, 89, 412, 451, 452],
  [82], [(2, 14)], [54, 71, 90, 413, 452, 453],
  [83], [(2, 15)], [55, 72, 91, 414, 453, 454],
  [84], [(2, 16)], [56, 73, 92, 415, 454, 455],
  [85], [(3, 0)], [59, 76, 95, 418, 457, 458],
  [86], [(3, 1)], [60, 77, 96, 419, 458, 459],
  [87], [(3, 2)], [61, 78, 97, 420, 459, 460],
  [88], [(3, 3)], [62, 79, 98, 421, 460, 461],
  [89], [(3, 4)], [63, 80, 99, 422, 461, 462],
  [90], [(3, 5)], [64, 81, 100, 423, 462, 463],
  [91], [(3, 6)], [65, 82, 101, 424, 463, 464],
  [92], [(3, 7)], [66, 83, 102, 425, 464, 465],
  [93], [(3, 8)], [67, 84, 103, 426, 465, 466],
  [94], [(3, 9)], [68, 85, 104, 427, 466, 467],
  [95], [(3, 10)], [69, 86, 105, 428, 467, 468],
  [96], [(3, 11)], [70, 87, 106, 429, 468, 469],
  [97], [(3, 12)], [71, 88, 107, 430, 469, 470],
  [98], [(3, 13)], [72, 89, 108, 431, 470, 471],
  [99], [(3, 14)], [73, 90, 109, 432, 471, 472],
  [100], [(3, 15)], [74, 91, 110, 433, 472, 473],
  [101], [(3, 16)], [75, 92, 111, 434, 473, 474],
  [102], [(4, 0)], [78, 95, 114, 437, 476, 477],
  [103], [(4, 1)], [79, 96, 115, 438, 477, 478],
  [104], [(4, 2)], [80, 97, 116, 439, 478, 479],
  [105], [(4, 3)], [81, 98, 117, 440, 479, 480],
  [106], [(4, 4)], [82, 99, 118, 441, 480, 481],
  [107], [(4, 5)], [83, 100, 119, 442, 481, 482],
  [108], [(4, 6)], [84, 101, 120, 443, 482, 483],
  [109], [(4, 7)], [85, 102, 121, 444, 483, 484],
  [110], [(4, 8)], [86, 103, 122, 445, 484, 485],
  [111], [(4, 9)], [87, 104, 123, 446, 485, 486],
  [112], [(4, 10)], [88, 105, 124, 447, 486, 487],
  [113], [(4, 11)], [89, 106, 125, 448, 487, 488],
  [114], [(4, 12)], [90, 107, 126, 449, 488, 489],
  [115], [(4, 13)], [91, 108, 127, 450, 489, 490],
  [116], [(4, 14)], [92, 109, 128, 451, 490, 491],
  [117], [(4, 15)], [93, 110, 129, 452, 491, 492],
  [118], [(4, 16)], [94, 111, 130, 453, 492, 493],
  [119], [(5, 0)], [97, 114, 133, 456, 495, 496],
  [120], [(5, 1)], [98, 115, 134, 457, 496, 497],
  [121], [(5, 2)], [99, 116, 135, 458, 497, 498],
  [122], [(5, 3)], [100, 117, 136, 459, 498, 499],
  [123], [(5, 4)], [101, 118, 137, 460, 499, 500],
  [124], [(5, 5)], [102, 119, 138, 461, 500, 501],
  [125], [(5, 6)], [103, 120, 139, 462, 501, 502],
  [126], [(5, 7)], [104, 121, 140, 463, 502, 503],
  [127], [(5, 8)], [105, 122, 141, 464, 503, 504],
  [128], [(5, 9)], [106, 123, 142, 465, 504, 505],
  [129], [(5, 10)], [107, 124, 143, 466, 505, 506],
  [130], [(5, 11)], [108, 125, 144, 467, 506, 507],
  [131], [(5, 12)], [109, 126, 145, 468, 507, 508],
  [132], [(5, 13)], [110, 127, 146, 469, 508, 509],
  [133], [(5, 14)], [111, 128, 147, 470, 509, 510],
  [134], [(5, 15)], [112, 129, 148, 471, 510, 511],
  [135], [(5, 16)], [113, 130, 149, 472, 511, 512],
  [136], [(6, 0)], [116, 133, 152, 475, 514, 515],
  [137], [(6, 1)], [117, 134, 153, 476, 515, 516],
  [138], [(6, 2)], [118, 135, 154, 477, 516, 517],
  [139], [(6, 3)], [119, 136, 155, 478, 517, 518],
  [140], [(6, 4)], [120, 137, 156, 479, 518, 519],
  [141], [(6, 5)], [121, 138, 157, 480, 519, 520],
  [142], [(6, 6)], [122, 139, 158, 481, 520, 521],
  [143], [(6, 7)], [123, 140, 159, 482, 521, 522],
  [144], [(6, 8)], [124, 141, 160, 483, 522, 523],
  [145], [(6, 9)], [125, 142, 161, 484, 523, 524],
  [146], [(6, 10)], [126, 143, 162, 485, 524, 525],
  [147], [(6, 11)], [127, 144, 163, 486, 525, 526],
  [148], [(6, 12)], [128, 145, 164, 487, 526, 527],
  [149], [(6, 13)], [129, 146, 165, 488, 527, 528],
  [150], [(6, 14)], [130, 147, 166, 489, 528, 529],
  [151], [(6, 15)], [131, 148, 167, 490, 529, 530],
  [152], [(6, 16)], [132, 149, 168, 491, 530, 531],
  [153], [(7, 0)], [135, 152, 171, 494, 533, 534],
  [154], [(7, 1)], [136, 153, 172, 495, 534, 535],
  [155], [(7, 2)], [137, 154, 173, 496, 535, 536],
  [156], [(7, 3)], [138, 155, 174, 497, 536, 537],
  [157], [(7, 4)], [139, 156, 175, 498, 537, 538],
  [158], [(7, 5)], [140, 157, 176, 499, 538, 539],
  [159], [(7, 6)], [141, 158, 177, 500, 539, 540],
  [160], [(7, 7)], [142, 159, 178, 501, 540, 541],
  [161], [(7, 8)], [143, 160, 179, 502, 541, 542],
  [162], [(7, 9)], [144, 161, 180, 503, 542, 543],
  [163], [(7, 10)], [145, 162, 181, 504, 543, 544],
  [164], [(7, 11)], [146, 163, 182, 505, 544, 545],
  [165], [(7, 12)], [147, 164, 183, 506, 545, 546],
  [166], [(7, 13)], [148, 165, 184, 507, 546, 547],
  [167], [(7, 14)], [149, 166, 185, 508, 547, 548],
  [168], [(7, 15)], [150, 167, 186, 509, 548, 549],
  [169], [(7, 16)], [151, 168, 187, 510, 549, 550],
  [170], [(8, 0)], [154, 171, 190, 513, 552, 553],
  [171], [(8, 1)], [155, 172, 191, 514, 553, 554],
  [172], [(8, 2)], [156, 173, 192, 515, 554, 555],
  [173], [(8, 3)], [157, 174, 193, 516, 555, 556],
  [174], [(8, 4)], [158, 175, 194, 517, 556, 557],
  [175], [(8, 5)], [159, 176, 195, 518, 557, 558],
  [176], [(8, 6)], [160, 177, 196, 519, 558, 559],
  [177], [(8, 7)], [161, 178, 197, 520, 559, 560],
  [178], [(8, 8)], [162, 179, 198, 521, 560, 561],
  [179], [(8, 9)], [163, 180, 199, 522, 561, 562],
  [180], [(8, 10)], [164, 181, 200, 523, 562, 563],
  [181], [(8, 11)], [165, 182, 201, 524, 563, 564],
  [182], [(8, 12)], [166, 183, 202, 525, 564, 565],
  [183], [(8, 13)], [167, 184, 203, 526, 565, 566],
  [184], [(8, 14)], [168, 185, 204, 527, 566, 567],
  [185], [(8, 15)], [169, 186, 205, 528, 567, 568],
  [186], [(8, 16)], [170, 187, 206, 529, 568, 569],
  [187], [(9, 0)], [173, 190, 209, 532, 571, 572],
  [188], [(9, 1)], [174, 191, 210, 533, 572, 573],
  [189], [(9, 2)], [175, 192, 211, 534, 573, 574],
  [190], [(9, 3)], [176, 193, 212, 535, 574, 575],
  [191], [(9, 4)], [177, 194, 213, 536, 575, 576],
  [192], [(9, 5)], [178, 195, 214, 537, 576, 577],
  [193], [(9, 6)], [179, 196, 215, 538, 577, 578],
  [194], [(9, 7)], [180, 197, 216, 539, 578, 579],
  [195], [(9, 8)], [181, 198, 217, 540, 579, 580],
  [196], [(9, 9)], [182, 199, 218, 541, 580, 581],
  [197], [(9, 10)], [183, 200, 219, 542, 581, 582],
  [198], [(9, 11)], [184, 201, 220, 543, 582, 583],
  [199], [(9, 12)], [185, 202, 221, 544, 583, 584],
  [200], [(9, 13)], [186, 203, 222, 545, 584, 585],
  [201], [(9, 14)], [187, 204, 223, 546, 585, 586],
  [202], [(9, 15)], [188, 205, 224, 547, 586, 587],
  [203], [(9, 16)], [189, 206, 225, 548, 587, 588],
  [204], [(10, 0)], [192, 209, 228, 551, 590, 591],
  [205], [(10, 1)], [193, 210, 229, 552, 591, 592],
  [206], [(10, 2)], [194, 211, 230, 553, 592, 593],
  [207], [(10, 3)], [195, 212, 231, 554, 593, 594],
  [208], [(10, 4)], [196, 213, 232, 555, 594, 595],
  [209], [(10, 5)], [197, 214, 233, 556, 595, 596],
  [210], [(10, 6)], [198, 215, 234, 557, 596, 597],
  [211], [(10, 7)], [199, 216, 235, 558, 597, 598],
  [212], [(10, 8)], [200, 217, 236, 559, 598, 599],
  [213], [(10, 9)], [201, 218, 237, 560, 599, 600],
  [214], [(10, 10)], [202, 219, 238, 561, 600, 601],
  [215], [(10, 11)], [203, 220, 239, 562, 601, 602],
  [216], [(10, 12)], [204, 221, 240, 563, 602, 603],
  [217], [(10, 13)], [205, 222, 241, 564, 603, 604],
  [218], [(10, 14)], [206, 223, 242, 565, 604, 605],
  [219], [(10, 15)], [207, 224, 243, 566, 605, 606],
  [220], [(10, 16)], [208, 225, 244, 567, 606, 607],
  [221], [(11, 0)], [211, 228, 247, 570, 609, 610],
  [222], [(11, 1)], [212, 229, 248, 571, 610, 611],
  [223], [(11, 2)], [213, 230, 249, 572, 611, 612],
  [224], [(11, 3)], [214, 231, 250, 573, 612, 613],
  [225], [(11, 4)], [215, 232, 251, 574, 613, 614],
  [226], [(11, 5)], [216, 233, 252, 575, 614, 615],
  [227], [(11, 6)], [217, 234, 253, 576, 615, 616],
  [228], [(11, 7)], [218, 235, 254, 577, 616, 617],
  [229], [(11, 8)], [219, 236, 255, 578, 617, 618],
  [230], [(11, 9)], [220, 237, 256, 579, 618, 619],
  [231], [(11, 10)], [221, 238, 257, 580, 619, 620],
  [232], [(11, 11)], [222, 239, 258, 581, 620, 621],
  [233], [(11, 12)], [223, 240, 259, 582, 621, 622],
  [234], [(11, 13)], [224, 241, 260, 583, 622, 623],
  [235], [(11, 14)], [225, 242, 261, 584, 623, 624],
  [236], [(11, 15)], [226, 243, 262, 585, 624, 625],
  [237], [(11, 16)], [227, 244, 263, 586, 625, 626],
  [238], [(12, 0)], [230, 247, 266, 589, 628, 629],
  [239], [(12, 1)], [231, 248, 267, 590, 629, 630],
  [240], [(12, 2)], [232, 249, 268, 591, 630, 631],
  [241], [(12, 3)], [233, 250, 269, 592, 631, 632],
  [242], [(12, 4)], [234, 251, 270, 593, 632, 633],
  [243], [(12, 5)], [235, 252, 271, 594, 633, 634],
  [244], [(12, 6)], [236, 253, 272, 595, 634, 635],
  [245], [(12, 7)], [237, 254, 273, 596, 635, 636],
  [246], [(12, 8)], [238, 255, 274, 597, 636, 637],
  [247], [(12, 9)], [239, 256, 275, 598, 637, 638],
  [248], [(12, 10)], [240, 257, 276, 599, 638, 639],
  [249], [(12, 11)], [241, 258, 277, 600, 639, 640],
  [250], [(12, 12)], [242, 259, 278, 601, 640, 641],
  [251], [(12, 13)], [243, 260, 279, 602, 641, 642],
  [252], [(12, 14)], [244, 261, 280, 603, 642, 643],
  [253], [(12, 15)], [245, 262, 281, 604, 643, 644],
  [254], [(12, 16)], [246, 263, 282, 605, 644, 645],
  [255], [(13, 0)], [249, 266, 285, 608, 647, 648],
  [256], [(13, 1)], [250, 267, 286, 609, 648, 649],
  [257], [(13, 2)], [251, 268, 287, 610, 649, 650],
  [258], [(13, 3)], [252, 269, 288, 611, 650, 651],
  [259], [(13, 4)], [253, 270, 289, 612, 651, 652],
  [260], [(13, 5)], [254, 271, 290, 613, 652, 653],
  [261], [(13, 6)], [255, 272, 291, 614, 653, 654],
  [262], [(13, 7)], [256, 273, 292, 615, 654, 655],
  [263], [(13, 8)], [257, 274, 293, 616, 655, 656],
  [264], [(13, 9)], [258, 275, 294, 617, 656, 657],
  [265], [(13, 10)], [259, 276, 295, 618, 657, 658],
  [266], [(13, 11)], [260, 277, 296, 619, 658, 659],
  [267], [(13, 12)], [261, 278, 297, 620, 659, 660],
  [268], [(13, 13)], [262, 279, 298, 621, 660, 661],
  [269], [(13, 14)], [263, 280, 299, 622, 661, 662],
  [270], [(13, 15)], [264, 281, 300, 623, 662, 663],
  [271], [(13, 16)], [265, 282, 301, 624, 663, 664],
  [272], [(14, 0)], [268, 285, 304, 627, 666, 667],
  [273], [(14, 1)], [269, 286, 305, 628, 667, 668],
  [274], [(14, 2)], [270, 287, 306, 629, 668, 669],
  [275], [(14, 3)], [271, 288, 307, 630, 669, 670],
  [276], [(14, 4)], [272, 289, 308, 631, 670, 671],
  [277], [(14, 5)], [273, 290, 309, 632, 671, 672],
  [278], [(14, 6)], [274, 291, 310, 633, 672, 673],
  [279], [(14, 7)], [275, 292, 311, 634, 673, 674],
  [280], [(14, 8)], [276, 293, 312, 635, 674, 675],
  [281], [(14, 9)], [277, 294, 313, 636, 675, 676],
  [282], [(14, 10)], [278, 295, 314, 637, 676, 677],
  [283], [(14, 11)], [279, 296, 315, 638, 677, 678],
  [284], [(14, 12)], [280, 297, 316, 639, 678, 679],
  [285], [(14, 13)], [281, 298, 317, 640, 679, 680],
  [286], [(14, 14)], [282, 299, 318, 641, 680, 681],
  [287], [(14, 15)], [283, 300, 319, 642, 681, 682],
  [288], [(14, 16)], [284, 301, 320, 643, 682, 683],
  [289], [(15, 0)], [287, 304, 323, 646, 685, 686],
  [290], [(15, 1)], [288, 305, 324, 647, 686, 687],
  [291], [(15, 2)], [289, 306, 325, 648, 687, 688],
  [292], [(15, 3)], [290, 307, 326, 649, 688, 689],
  [293], [(15, 4)], [291, 308, 327, 650, 689, 690],
  [294], [(15, 5)], [292, 309, 328, 651, 690, 691],
  [295], [(15, 6)], [293, 310, 329, 652, 691, 692],
  [296], [(15, 7)], [294, 311, 330, 653, 692, 693],
  [297], [(15, 8)], [295, 312, 331, 654, 693, 694],
  [298], [(15, 9)], [296, 313, 332, 655, 694, 695],
  [299], [(15, 10)], [297, 314, 333, 656, 695, 696],
  [300], [(15, 11)], [298, 315, 334, 657, 696, 697],
  [301], [(15, 12)], [299, 316, 335, 658, 697, 698],
  [302], [(15, 13)], [300, 317, 336, 659, 698, 699],
  [303], [(15, 14)], [301, 318, 337, 660, 699, 700],
  [304], [(15, 15)], [302, 319, 338, 661, 700, 701],
  [305], [(15, 16)], [303, 320, 339, 662, 701, 702],
  [306], [(16, 0)], [306, 323, 342, 665, 704, 705],
  [307], [(16, 1)], [307, 324, 343, 666, 705, 706],
  [308], [(16, 2)], [308, 325, 344, 667, 706, 707],
  [309], [(16, 3)], [309, 326, 345, 668, 707, 708],
  [310], [(16, 4)], [310, 327, 346, 669, 708, 709],
  [311], [(16, 5)], [311, 328, 347, 670, 709, 710],
  [312], [(16, 6)], [312, 329, 348, 671, 710, 711],
  [313], [(16, 7)], [313, 330, 349, 672, 711, 712],
  [314], [(16, 8)], [314, 331, 350, 673, 712, 713],
  [315], [(16, 9)], [315, 332, 351, 674, 713, 714],
  [316], [(16, 10)], [316, 333, 352, 675, 714, 715],
  [317], [(16, 11)], [317, 334, 353, 676, 715, 716],
  [318], [(16, 12)], [318, 335, 354, 677, 716, 717],
  [319], [(16, 13)], [319, 336, 355, 678, 717, 718],
  [320], [(16, 14)], [320, 337, 356, 679, 718, 719],
  [321], [(16, 15)], [321, 338, 357, 680, 719, 720],
  [322], [(16, 16)], [322, 339, 358, 681, 720, 721],
  [323], [(17, 0)], [325, 342, 684],
  [324], [(17, 1)], [326, 343, 685],
  [325], [(17, 2)], [327, 344, 686],
  [326], [(17, 3)], [328, 345, 687],
  [327], [(17, 4)], [329, 346, 688],
  [328], [(17, 5)], [330, 347, 689],
  [329], [(17, 6)], [331, 348, 690],
  [330], [(17, 7)], [332, 349, 691],
  [331], [(17, 8)], [333, 350, 692],
  [332], [(17, 9)], [334, 351, 693],
  [333], [(17, 10)], [335, 352, 694],
  [334], [(17, 11)], [336, 353, 695],
  [335], [(17, 12)], [337, 354, 696],
  [336], [(17, 13)], [338, 355, 697],
  [337], [(17, 14)], [339, 356, 698],
  [338], [(17, 15)], [340, 357, 699],
  [339], [(17, 16)], [341, 358, 700],
  [340], [(18, 0)], [344, 703],
  [341], [(18, 1)], [345, 704],
  [342], [(18, 2)], [346, 705],
  [343], [(18, 3)], [347, 706],
  [344], [(18, 4)], [348, 707],
  [345], [(18, 5)], [349, 708],
  [346], [(18, 6)], [350, 709],
  [347], [(18, 7)], [351, 710],
  [348], [(18, 8)], [352, 711],
  [349], [(18, 9)], [353, 712],
  [350], [(18, 10)], [354, 713],
  [351], [(18, 11)], [355, 714],
  [352], [(18, 12)], [356, 715],
  [353], [(18, 13)], [357, 716],
  [354], [(18, 14)], [358, 717],
  [355], [(18, 15)], [359, 718],
  [356], [(18, 16)], [360, 719],
)

#pagebreak()
== Z supports

#table(columns: (40pt, 80pt, 1fr), inset: 3pt,
  table.header([Row], [Anchor], [Physical support]),
  [0], [(2, 0)], [38, 361, 380],
  [1], [(2, 1)], [0, 39, 362, 381],
  [2], [(2, 2)], [0, 1, 40, 363, 382, 399],
  [3], [(2, 3)], [1, 2, 41, 364, 383, 400],
  [4], [(2, 4)], [2, 3, 42, 365, 384, 401],
  [5], [(2, 5)], [3, 4, 43, 366, 385, 402],
  [6], [(2, 6)], [4, 5, 44, 367, 386, 403],
  [7], [(2, 7)], [5, 6, 45, 368, 387, 404],
  [8], [(2, 8)], [6, 7, 46, 369, 388, 405],
  [9], [(2, 9)], [7, 8, 47, 370, 389, 406],
  [10], [(2, 10)], [8, 9, 48, 371, 390, 407],
  [11], [(2, 11)], [9, 10, 49, 372, 391, 408],
  [12], [(2, 12)], [10, 11, 50, 373, 392, 409],
  [13], [(2, 13)], [11, 12, 51, 374, 393, 410],
  [14], [(2, 14)], [12, 13, 52, 375, 394, 411],
  [15], [(2, 15)], [13, 14, 53, 376, 395, 412],
  [16], [(2, 16)], [14, 15, 54, 377, 396, 413],
  [17], [(2, 17)], [15, 16, 55, 378, 397, 414],
  [18], [(2, 18)], [16, 17, 56, 379, 398, 415],
  [19], [(2, 19)], [17, 18, 416],
  [20], [(2, 20)], [18, 417],
  [21], [(3, 0)], [57, 380, 399],
  [22], [(3, 1)], [19, 58, 381, 400],
  [23], [(3, 2)], [19, 20, 59, 382, 401, 418],
  [24], [(3, 3)], [20, 21, 60, 383, 402, 419],
  [25], [(3, 4)], [21, 22, 61, 384, 403, 420],
  [26], [(3, 5)], [22, 23, 62, 385, 404, 421],
  [27], [(3, 6)], [23, 24, 63, 386, 405, 422],
  [28], [(3, 7)], [24, 25, 64, 387, 406, 423],
  [29], [(3, 8)], [25, 26, 65, 388, 407, 424],
  [30], [(3, 9)], [26, 27, 66, 389, 408, 425],
  [31], [(3, 10)], [27, 28, 67, 390, 409, 426],
  [32], [(3, 11)], [28, 29, 68, 391, 410, 427],
  [33], [(3, 12)], [29, 30, 69, 392, 411, 428],
  [34], [(3, 13)], [30, 31, 70, 393, 412, 429],
  [35], [(3, 14)], [31, 32, 71, 394, 413, 430],
  [36], [(3, 15)], [32, 33, 72, 395, 414, 431],
  [37], [(3, 16)], [33, 34, 73, 396, 415, 432],
  [38], [(3, 17)], [34, 35, 74, 397, 416, 433],
  [39], [(3, 18)], [35, 36, 75, 398, 417, 434],
  [40], [(3, 19)], [36, 37, 435],
  [41], [(3, 20)], [37, 436],
  [42], [(4, 0)], [76, 399, 418],
  [43], [(4, 1)], [38, 77, 400, 419],
  [44], [(4, 2)], [38, 39, 78, 401, 420, 437],
  [45], [(4, 3)], [39, 40, 79, 402, 421, 438],
  [46], [(4, 4)], [40, 41, 80, 403, 422, 439],
  [47], [(4, 5)], [41, 42, 81, 404, 423, 440],
  [48], [(4, 6)], [42, 43, 82, 405, 424, 441],
  [49], [(4, 7)], [43, 44, 83, 406, 425, 442],
  [50], [(4, 8)], [44, 45, 84, 407, 426, 443],
  [51], [(4, 9)], [45, 46, 85, 408, 427, 444],
  [52], [(4, 10)], [46, 47, 86, 409, 428, 445],
  [53], [(4, 11)], [47, 48, 87, 410, 429, 446],
  [54], [(4, 12)], [48, 49, 88, 411, 430, 447],
  [55], [(4, 13)], [49, 50, 89, 412, 431, 448],
  [56], [(4, 14)], [50, 51, 90, 413, 432, 449],
  [57], [(4, 15)], [51, 52, 91, 414, 433, 450],
  [58], [(4, 16)], [52, 53, 92, 415, 434, 451],
  [59], [(4, 17)], [53, 54, 93, 416, 435, 452],
  [60], [(4, 18)], [54, 55, 94, 417, 436, 453],
  [61], [(4, 19)], [55, 56, 454],
  [62], [(4, 20)], [56, 455],
  [63], [(5, 0)], [95, 418, 437],
  [64], [(5, 1)], [57, 96, 419, 438],
  [65], [(5, 2)], [57, 58, 97, 420, 439, 456],
  [66], [(5, 3)], [58, 59, 98, 421, 440, 457],
  [67], [(5, 4)], [59, 60, 99, 422, 441, 458],
  [68], [(5, 5)], [60, 61, 100, 423, 442, 459],
  [69], [(5, 6)], [61, 62, 101, 424, 443, 460],
  [70], [(5, 7)], [62, 63, 102, 425, 444, 461],
  [71], [(5, 8)], [63, 64, 103, 426, 445, 462],
  [72], [(5, 9)], [64, 65, 104, 427, 446, 463],
  [73], [(5, 10)], [65, 66, 105, 428, 447, 464],
  [74], [(5, 11)], [66, 67, 106, 429, 448, 465],
  [75], [(5, 12)], [67, 68, 107, 430, 449, 466],
  [76], [(5, 13)], [68, 69, 108, 431, 450, 467],
  [77], [(5, 14)], [69, 70, 109, 432, 451, 468],
  [78], [(5, 15)], [70, 71, 110, 433, 452, 469],
  [79], [(5, 16)], [71, 72, 111, 434, 453, 470],
  [80], [(5, 17)], [72, 73, 112, 435, 454, 471],
  [81], [(5, 18)], [73, 74, 113, 436, 455, 472],
  [82], [(5, 19)], [74, 75, 473],
  [83], [(5, 20)], [75, 474],
  [84], [(6, 0)], [114, 437, 456],
  [85], [(6, 1)], [76, 115, 438, 457],
  [86], [(6, 2)], [76, 77, 116, 439, 458, 475],
  [87], [(6, 3)], [77, 78, 117, 440, 459, 476],
  [88], [(6, 4)], [78, 79, 118, 441, 460, 477],
  [89], [(6, 5)], [79, 80, 119, 442, 461, 478],
  [90], [(6, 6)], [80, 81, 120, 443, 462, 479],
  [91], [(6, 7)], [81, 82, 121, 444, 463, 480],
  [92], [(6, 8)], [82, 83, 122, 445, 464, 481],
  [93], [(6, 9)], [83, 84, 123, 446, 465, 482],
  [94], [(6, 10)], [84, 85, 124, 447, 466, 483],
  [95], [(6, 11)], [85, 86, 125, 448, 467, 484],
  [96], [(6, 12)], [86, 87, 126, 449, 468, 485],
  [97], [(6, 13)], [87, 88, 127, 450, 469, 486],
  [98], [(6, 14)], [88, 89, 128, 451, 470, 487],
  [99], [(6, 15)], [89, 90, 129, 452, 471, 488],
  [100], [(6, 16)], [90, 91, 130, 453, 472, 489],
  [101], [(6, 17)], [91, 92, 131, 454, 473, 490],
  [102], [(6, 18)], [92, 93, 132, 455, 474, 491],
  [103], [(6, 19)], [93, 94, 492],
  [104], [(6, 20)], [94, 493],
  [105], [(7, 0)], [133, 456, 475],
  [106], [(7, 1)], [95, 134, 457, 476],
  [107], [(7, 2)], [95, 96, 135, 458, 477, 494],
  [108], [(7, 3)], [96, 97, 136, 459, 478, 495],
  [109], [(7, 4)], [97, 98, 137, 460, 479, 496],
  [110], [(7, 5)], [98, 99, 138, 461, 480, 497],
  [111], [(7, 6)], [99, 100, 139, 462, 481, 498],
  [112], [(7, 7)], [100, 101, 140, 463, 482, 499],
  [113], [(7, 8)], [101, 102, 141, 464, 483, 500],
  [114], [(7, 9)], [102, 103, 142, 465, 484, 501],
  [115], [(7, 10)], [103, 104, 143, 466, 485, 502],
  [116], [(7, 11)], [104, 105, 144, 467, 486, 503],
  [117], [(7, 12)], [105, 106, 145, 468, 487, 504],
  [118], [(7, 13)], [106, 107, 146, 469, 488, 505],
  [119], [(7, 14)], [107, 108, 147, 470, 489, 506],
  [120], [(7, 15)], [108, 109, 148, 471, 490, 507],
  [121], [(7, 16)], [109, 110, 149, 472, 491, 508],
  [122], [(7, 17)], [110, 111, 150, 473, 492, 509],
  [123], [(7, 18)], [111, 112, 151, 474, 493, 510],
  [124], [(7, 19)], [112, 113, 511],
  [125], [(7, 20)], [113, 512],
  [126], [(8, 0)], [152, 475, 494],
  [127], [(8, 1)], [114, 153, 476, 495],
  [128], [(8, 2)], [114, 115, 154, 477, 496, 513],
  [129], [(8, 3)], [115, 116, 155, 478, 497, 514],
  [130], [(8, 4)], [116, 117, 156, 479, 498, 515],
  [131], [(8, 5)], [117, 118, 157, 480, 499, 516],
  [132], [(8, 6)], [118, 119, 158, 481, 500, 517],
  [133], [(8, 7)], [119, 120, 159, 482, 501, 518],
  [134], [(8, 8)], [120, 121, 160, 483, 502, 519],
  [135], [(8, 9)], [121, 122, 161, 484, 503, 520],
  [136], [(8, 10)], [122, 123, 162, 485, 504, 521],
  [137], [(8, 11)], [123, 124, 163, 486, 505, 522],
  [138], [(8, 12)], [124, 125, 164, 487, 506, 523],
  [139], [(8, 13)], [125, 126, 165, 488, 507, 524],
  [140], [(8, 14)], [126, 127, 166, 489, 508, 525],
  [141], [(8, 15)], [127, 128, 167, 490, 509, 526],
  [142], [(8, 16)], [128, 129, 168, 491, 510, 527],
  [143], [(8, 17)], [129, 130, 169, 492, 511, 528],
  [144], [(8, 18)], [130, 131, 170, 493, 512, 529],
  [145], [(8, 19)], [131, 132, 530],
  [146], [(8, 20)], [132, 531],
  [147], [(9, 0)], [171, 494, 513],
  [148], [(9, 1)], [133, 172, 495, 514],
  [149], [(9, 2)], [133, 134, 173, 496, 515, 532],
  [150], [(9, 3)], [134, 135, 174, 497, 516, 533],
  [151], [(9, 4)], [135, 136, 175, 498, 517, 534],
  [152], [(9, 5)], [136, 137, 176, 499, 518, 535],
  [153], [(9, 6)], [137, 138, 177, 500, 519, 536],
  [154], [(9, 7)], [138, 139, 178, 501, 520, 537],
  [155], [(9, 8)], [139, 140, 179, 502, 521, 538],
  [156], [(9, 9)], [140, 141, 180, 503, 522, 539],
  [157], [(9, 10)], [141, 142, 181, 504, 523, 540],
  [158], [(9, 11)], [142, 143, 182, 505, 524, 541],
  [159], [(9, 12)], [143, 144, 183, 506, 525, 542],
  [160], [(9, 13)], [144, 145, 184, 507, 526, 543],
  [161], [(9, 14)], [145, 146, 185, 508, 527, 544],
  [162], [(9, 15)], [146, 147, 186, 509, 528, 545],
  [163], [(9, 16)], [147, 148, 187, 510, 529, 546],
  [164], [(9, 17)], [148, 149, 188, 511, 530, 547],
  [165], [(9, 18)], [149, 150, 189, 512, 531, 548],
  [166], [(9, 19)], [150, 151, 549],
  [167], [(9, 20)], [151, 550],
  [168], [(10, 0)], [190, 513, 532],
  [169], [(10, 1)], [152, 191, 514, 533],
  [170], [(10, 2)], [152, 153, 192, 515, 534, 551],
  [171], [(10, 3)], [153, 154, 193, 516, 535, 552],
  [172], [(10, 4)], [154, 155, 194, 517, 536, 553],
  [173], [(10, 5)], [155, 156, 195, 518, 537, 554],
  [174], [(10, 6)], [156, 157, 196, 519, 538, 555],
  [175], [(10, 7)], [157, 158, 197, 520, 539, 556],
  [176], [(10, 8)], [158, 159, 198, 521, 540, 557],
  [177], [(10, 9)], [159, 160, 199, 522, 541, 558],
  [178], [(10, 10)], [160, 161, 200, 523, 542, 559],
  [179], [(10, 11)], [161, 162, 201, 524, 543, 560],
  [180], [(10, 12)], [162, 163, 202, 525, 544, 561],
  [181], [(10, 13)], [163, 164, 203, 526, 545, 562],
  [182], [(10, 14)], [164, 165, 204, 527, 546, 563],
  [183], [(10, 15)], [165, 166, 205, 528, 547, 564],
  [184], [(10, 16)], [166, 167, 206, 529, 548, 565],
  [185], [(10, 17)], [167, 168, 207, 530, 549, 566],
  [186], [(10, 18)], [168, 169, 208, 531, 550, 567],
  [187], [(10, 19)], [169, 170, 568],
  [188], [(10, 20)], [170, 569],
  [189], [(11, 0)], [209, 532, 551],
  [190], [(11, 1)], [171, 210, 533, 552],
  [191], [(11, 2)], [171, 172, 211, 534, 553, 570],
  [192], [(11, 3)], [172, 173, 212, 535, 554, 571],
  [193], [(11, 4)], [173, 174, 213, 536, 555, 572],
  [194], [(11, 5)], [174, 175, 214, 537, 556, 573],
  [195], [(11, 6)], [175, 176, 215, 538, 557, 574],
  [196], [(11, 7)], [176, 177, 216, 539, 558, 575],
  [197], [(11, 8)], [177, 178, 217, 540, 559, 576],
  [198], [(11, 9)], [178, 179, 218, 541, 560, 577],
  [199], [(11, 10)], [179, 180, 219, 542, 561, 578],
  [200], [(11, 11)], [180, 181, 220, 543, 562, 579],
  [201], [(11, 12)], [181, 182, 221, 544, 563, 580],
  [202], [(11, 13)], [182, 183, 222, 545, 564, 581],
  [203], [(11, 14)], [183, 184, 223, 546, 565, 582],
  [204], [(11, 15)], [184, 185, 224, 547, 566, 583],
  [205], [(11, 16)], [185, 186, 225, 548, 567, 584],
  [206], [(11, 17)], [186, 187, 226, 549, 568, 585],
  [207], [(11, 18)], [187, 188, 227, 550, 569, 586],
  [208], [(11, 19)], [188, 189, 587],
  [209], [(11, 20)], [189, 588],
  [210], [(12, 0)], [228, 551, 570],
  [211], [(12, 1)], [190, 229, 552, 571],
  [212], [(12, 2)], [190, 191, 230, 553, 572, 589],
  [213], [(12, 3)], [191, 192, 231, 554, 573, 590],
  [214], [(12, 4)], [192, 193, 232, 555, 574, 591],
  [215], [(12, 5)], [193, 194, 233, 556, 575, 592],
  [216], [(12, 6)], [194, 195, 234, 557, 576, 593],
  [217], [(12, 7)], [195, 196, 235, 558, 577, 594],
  [218], [(12, 8)], [196, 197, 236, 559, 578, 595],
  [219], [(12, 9)], [197, 198, 237, 560, 579, 596],
  [220], [(12, 10)], [198, 199, 238, 561, 580, 597],
  [221], [(12, 11)], [199, 200, 239, 562, 581, 598],
  [222], [(12, 12)], [200, 201, 240, 563, 582, 599],
  [223], [(12, 13)], [201, 202, 241, 564, 583, 600],
  [224], [(12, 14)], [202, 203, 242, 565, 584, 601],
  [225], [(12, 15)], [203, 204, 243, 566, 585, 602],
  [226], [(12, 16)], [204, 205, 244, 567, 586, 603],
  [227], [(12, 17)], [205, 206, 245, 568, 587, 604],
  [228], [(12, 18)], [206, 207, 246, 569, 588, 605],
  [229], [(12, 19)], [207, 208, 606],
  [230], [(12, 20)], [208, 607],
  [231], [(13, 0)], [247, 570, 589],
  [232], [(13, 1)], [209, 248, 571, 590],
  [233], [(13, 2)], [209, 210, 249, 572, 591, 608],
  [234], [(13, 3)], [210, 211, 250, 573, 592, 609],
  [235], [(13, 4)], [211, 212, 251, 574, 593, 610],
  [236], [(13, 5)], [212, 213, 252, 575, 594, 611],
  [237], [(13, 6)], [213, 214, 253, 576, 595, 612],
  [238], [(13, 7)], [214, 215, 254, 577, 596, 613],
  [239], [(13, 8)], [215, 216, 255, 578, 597, 614],
  [240], [(13, 9)], [216, 217, 256, 579, 598, 615],
  [241], [(13, 10)], [217, 218, 257, 580, 599, 616],
  [242], [(13, 11)], [218, 219, 258, 581, 600, 617],
  [243], [(13, 12)], [219, 220, 259, 582, 601, 618],
  [244], [(13, 13)], [220, 221, 260, 583, 602, 619],
  [245], [(13, 14)], [221, 222, 261, 584, 603, 620],
  [246], [(13, 15)], [222, 223, 262, 585, 604, 621],
  [247], [(13, 16)], [223, 224, 263, 586, 605, 622],
  [248], [(13, 17)], [224, 225, 264, 587, 606, 623],
  [249], [(13, 18)], [225, 226, 265, 588, 607, 624],
  [250], [(13, 19)], [226, 227, 625],
  [251], [(13, 20)], [227, 626],
  [252], [(14, 0)], [266, 589, 608],
  [253], [(14, 1)], [228, 267, 590, 609],
  [254], [(14, 2)], [228, 229, 268, 591, 610, 627],
  [255], [(14, 3)], [229, 230, 269, 592, 611, 628],
  [256], [(14, 4)], [230, 231, 270, 593, 612, 629],
  [257], [(14, 5)], [231, 232, 271, 594, 613, 630],
  [258], [(14, 6)], [232, 233, 272, 595, 614, 631],
  [259], [(14, 7)], [233, 234, 273, 596, 615, 632],
  [260], [(14, 8)], [234, 235, 274, 597, 616, 633],
  [261], [(14, 9)], [235, 236, 275, 598, 617, 634],
  [262], [(14, 10)], [236, 237, 276, 599, 618, 635],
  [263], [(14, 11)], [237, 238, 277, 600, 619, 636],
  [264], [(14, 12)], [238, 239, 278, 601, 620, 637],
  [265], [(14, 13)], [239, 240, 279, 602, 621, 638],
  [266], [(14, 14)], [240, 241, 280, 603, 622, 639],
  [267], [(14, 15)], [241, 242, 281, 604, 623, 640],
  [268], [(14, 16)], [242, 243, 282, 605, 624, 641],
  [269], [(14, 17)], [243, 244, 283, 606, 625, 642],
  [270], [(14, 18)], [244, 245, 284, 607, 626, 643],
  [271], [(14, 19)], [245, 246, 644],
  [272], [(14, 20)], [246, 645],
  [273], [(15, 0)], [285, 608, 627],
  [274], [(15, 1)], [247, 286, 609, 628],
  [275], [(15, 2)], [247, 248, 287, 610, 629, 646],
  [276], [(15, 3)], [248, 249, 288, 611, 630, 647],
  [277], [(15, 4)], [249, 250, 289, 612, 631, 648],
  [278], [(15, 5)], [250, 251, 290, 613, 632, 649],
  [279], [(15, 6)], [251, 252, 291, 614, 633, 650],
  [280], [(15, 7)], [252, 253, 292, 615, 634, 651],
  [281], [(15, 8)], [253, 254, 293, 616, 635, 652],
  [282], [(15, 9)], [254, 255, 294, 617, 636, 653],
  [283], [(15, 10)], [255, 256, 295, 618, 637, 654],
  [284], [(15, 11)], [256, 257, 296, 619, 638, 655],
  [285], [(15, 12)], [257, 258, 297, 620, 639, 656],
  [286], [(15, 13)], [258, 259, 298, 621, 640, 657],
  [287], [(15, 14)], [259, 260, 299, 622, 641, 658],
  [288], [(15, 15)], [260, 261, 300, 623, 642, 659],
  [289], [(15, 16)], [261, 262, 301, 624, 643, 660],
  [290], [(15, 17)], [262, 263, 302, 625, 644, 661],
  [291], [(15, 18)], [263, 264, 303, 626, 645, 662],
  [292], [(15, 19)], [264, 265, 663],
  [293], [(15, 20)], [265, 664],
  [294], [(16, 0)], [304, 627, 646],
  [295], [(16, 1)], [266, 305, 628, 647],
  [296], [(16, 2)], [266, 267, 306, 629, 648, 665],
  [297], [(16, 3)], [267, 268, 307, 630, 649, 666],
  [298], [(16, 4)], [268, 269, 308, 631, 650, 667],
  [299], [(16, 5)], [269, 270, 309, 632, 651, 668],
  [300], [(16, 6)], [270, 271, 310, 633, 652, 669],
  [301], [(16, 7)], [271, 272, 311, 634, 653, 670],
  [302], [(16, 8)], [272, 273, 312, 635, 654, 671],
  [303], [(16, 9)], [273, 274, 313, 636, 655, 672],
  [304], [(16, 10)], [274, 275, 314, 637, 656, 673],
  [305], [(16, 11)], [275, 276, 315, 638, 657, 674],
  [306], [(16, 12)], [276, 277, 316, 639, 658, 675],
  [307], [(16, 13)], [277, 278, 317, 640, 659, 676],
  [308], [(16, 14)], [278, 279, 318, 641, 660, 677],
  [309], [(16, 15)], [279, 280, 319, 642, 661, 678],
  [310], [(16, 16)], [280, 281, 320, 643, 662, 679],
  [311], [(16, 17)], [281, 282, 321, 644, 663, 680],
  [312], [(16, 18)], [282, 283, 322, 645, 664, 681],
  [313], [(16, 19)], [283, 284, 682],
  [314], [(16, 20)], [284, 683],
  [315], [(17, 0)], [323, 646, 665],
  [316], [(17, 1)], [285, 324, 647, 666],
  [317], [(17, 2)], [285, 286, 325, 648, 667, 684],
  [318], [(17, 3)], [286, 287, 326, 649, 668, 685],
  [319], [(17, 4)], [287, 288, 327, 650, 669, 686],
  [320], [(17, 5)], [288, 289, 328, 651, 670, 687],
  [321], [(17, 6)], [289, 290, 329, 652, 671, 688],
  [322], [(17, 7)], [290, 291, 330, 653, 672, 689],
  [323], [(17, 8)], [291, 292, 331, 654, 673, 690],
  [324], [(17, 9)], [292, 293, 332, 655, 674, 691],
  [325], [(17, 10)], [293, 294, 333, 656, 675, 692],
  [326], [(17, 11)], [294, 295, 334, 657, 676, 693],
  [327], [(17, 12)], [295, 296, 335, 658, 677, 694],
  [328], [(17, 13)], [296, 297, 336, 659, 678, 695],
  [329], [(17, 14)], [297, 298, 337, 660, 679, 696],
  [330], [(17, 15)], [298, 299, 338, 661, 680, 697],
  [331], [(17, 16)], [299, 300, 339, 662, 681, 698],
  [332], [(17, 17)], [300, 301, 340, 663, 682, 699],
  [333], [(17, 18)], [301, 302, 341, 664, 683, 700],
  [334], [(17, 19)], [302, 303, 701],
  [335], [(17, 20)], [303, 702],
  [336], [(18, 0)], [342, 665, 684],
  [337], [(18, 1)], [304, 343, 666, 685],
  [338], [(18, 2)], [304, 305, 344, 667, 686, 703],
  [339], [(18, 3)], [305, 306, 345, 668, 687, 704],
  [340], [(18, 4)], [306, 307, 346, 669, 688, 705],
  [341], [(18, 5)], [307, 308, 347, 670, 689, 706],
  [342], [(18, 6)], [308, 309, 348, 671, 690, 707],
  [343], [(18, 7)], [309, 310, 349, 672, 691, 708],
  [344], [(18, 8)], [310, 311, 350, 673, 692, 709],
  [345], [(18, 9)], [311, 312, 351, 674, 693, 710],
  [346], [(18, 10)], [312, 313, 352, 675, 694, 711],
  [347], [(18, 11)], [313, 314, 353, 676, 695, 712],
  [348], [(18, 12)], [314, 315, 354, 677, 696, 713],
  [349], [(18, 13)], [315, 316, 355, 678, 697, 714],
  [350], [(18, 14)], [316, 317, 356, 679, 698, 715],
  [351], [(18, 15)], [317, 318, 357, 680, 699, 716],
  [352], [(18, 16)], [318, 319, 358, 681, 700, 717],
  [353], [(18, 17)], [319, 320, 359, 682, 701, 718],
  [354], [(18, 18)], [320, 321, 360, 683, 702, 719],
  [355], [(18, 19)], [321, 322, 720],
  [356], [(18, 20)], [322, 721],
)

#pagebreak()
#bibliography("references.bib", style: "ieee", title: [References])
