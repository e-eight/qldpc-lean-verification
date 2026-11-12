# Exact cyclic binomial distances and a coprime rotated-square family

**Working grade: PROPOSITION.** The analytic argument below is complete. The named
outstanding obligations are the final Lean replay and three independent hostile
referee passes. This draft must not be promoted to `PROOF.md` before they pass.

## Main statement

Let $m$ be a positive integer and let $s,t$ be nonnegative integers with
$\gcd(\gcd(s,t),m)=1$. The cyclic binomial CSS code defined below has $2m$
physical qubits, both check ranks $m-1$, and two encoded qubits. Its two CSS
distances are equal, and their common value is

\[
\lambda(m;s,t)=\min\{\lvert u\rvert+\lvert v\rvert:
 (u,v)\in\mathbb Z^2\setminus\{(0,0)\},\quad m\mid su+tv\}.
\]

In particular, an analytic proof of this integer minimum supplies the exact code
distance without a separate search for logical operators or a separate support
certificate. The statement includes $m=1$, zero steps, loops, parallel edges,
and even values of $m$.

A concrete infinite subfamily has the following exact parameters. Let $a,h$
be positive integers, let $b$ be a nonnegative integer, and suppose
$\gcd(a,b)=1$. Put $m=h(a^2+b^2)$ and take steps $s=a,t=b$. Then

\[
[[n,k,d_X,d_Z]]=[[2h(a^2+b^2),\,2,\,a+b,\,a+b]].
\]

Both check ranks are $h(a^2+b^2)-1$. In both the general construction and this
subfamily, each check has weight at most four and each physical qubit belongs
to at most two checks of each type. These bounds are independent of the
parameters; this is the low-density property. In particular, for $r\ge1$,
the choice $a=r,b=r+1,h=1$ gives
$[[(2r+1)^2+1,2,2r+1]]$.

## 1. Definitions

Write $\mathbb F_2=\{0,1\}$ for the field in which $1+1=0$, and write
$V=\mathbb Z/m\mathbb Z$. There are two separately labelled edges for each
$z\in V$:

\[
h_z:z\longrightarrow z+s,\qquad v_z:z\longrightarrow z+t.
\]

Let $E=\{h_z:z\in V\}\sqcup\{v_z:z\in V\}$. The symbol $\sqcup$ means
disjoint union: even if endpoints coincide, edge labels remain distinct. An edge
whose two endpoints coincide is a loop. A binary chain is a function
$x:E\to\mathbb F_2$. Its weight $\operatorname{wt}(x)$ is the number of edges
where its value is one. Write $e_e$ for the chain that is one at $e$ and zero
elsewhere. The pairing of two chains is
$\langle x,y\rangle=\sum_{e\in E}x(e)y(e)$, evaluated in $\mathbb F_2$.

For each $z\in V$, define the vertex check

\[
H_z=e_{h_z}+e_{h_{z-s}}+e_{v_z}+e_{v_{z-t}}
\]

and the square check

\[
F_z=e_{h_z}+e_{v_{z+s}}+e_{h_{z+t}}+e_{v_z}.
\]

Repeated terms in these formulas cancel in $\mathbb F_2$. Regard $H$ and
$F$ as matrices with rows $H_z$ and $F_z$, respectively. The code has X
checks $H$ and Z checks $F$. Its Z cycles and Z boundaries are

\[
C=\ker H=\{x:\langle H_z,x\rangle=0\text{ for every }z\},\qquad
B=\operatorname{span}_{\mathbb F_2}\{F_z:z\in V\}.
\]

A nontrivial Z logical is a member of $C\setminus B$. Its least weight is
$d_Z$. A nontrivial X logical is a member of
$\ker F\setminus\operatorname{span}\{H_z\}$, and its least weight is $d_X$.
Once $HF^{\mathsf T}=0$, these are CSS logical spaces and the encoded
dimension is $2m-\operatorname{rank}H-\operatorname{rank}F$. This is also
$\dim C-\dim B$, by the linear algebra proved in Section 3.

A walk is a finite sequence of incident labelled edges, each traversed either
in its displayed direction or in the reverse direction. A forward horizontal
step contributes $(1,0)$, a reverse horizontal step contributes $(-1,0)$, a
forward vertical step contributes $(0,1)$, and a reverse vertical step
contributes $(0,-1)$. These are all possibilities because each edge belongs to
exactly one of the two disjoint edge sets and has exactly two traversal
directions. The sum of these integer contributions is the displacement
$(u(w),v(w))$. The length $L(w)$ is the number of traversals, with
repetitions. The binary chain $x(w)$ of a walk records each edge's number of
traversals modulo two, without its direction.

## 2. Elementary arithmetic and connectivity

For integers $a,b$, the set of integer combinations $aA+bB$ is a subgroup
of $\mathbb Z$. If it contains a positive integer, let $g$ be its smallest
positive integer. Division with remainder shows every combination is divisible
by $g$: a nonzero remainder would be a smaller positive combination. Thus
$g$ divides $a$ and $b$. Every common divisor divides every combination,
and therefore divides $g$. This proves both the gcd characterization and
the existence of integers $A,B$ with $aA+bB=\gcd(a,b)$. When $a=b=0$,
the subgroup is $\{0\}$ and the gcd is zero. These cases exhaust the
possibilities because a nonzero subgroup contains a positive integer by
negating a negative member if necessary.

Put $g=\gcd(s,t)$. The hypothesis gives $\gcd(g,m)=1$. Combining the two
gcd identities yields integers $A,B,K$ with $As+Bt+Km=1$. From a vertex
$z$, a positive coefficient of $s$ or $t$ is realized by that many forward
steps; a negative coefficient is realized by the corresponding number of
reverse steps; and coefficient zero requires no step. Applying this to $A,B$
gives a walk from $z$ to $z+1$. Repeating it reaches every residue, so the
graph is connected. This argument permits loops and repeated endpoints.

We will also need integers $a,b,p,q$ and a unit $c$ modulo $m$ such that

\[
s=ca\pmod m,\qquad t=cb\pmod m,\qquad ap+bq=1. \tag{1}
\]

If $g>0$, take $a=s/g$, $b=t/g$, and $c=g\pmod m$. A common divisor
of $a,b$ larger than one would make a common divisor of $s,t$ larger than
$g$, so $\gcd(a,b)=1$. The gcd identity supplies $p,q$, and
$\gcd(g,m)=1$ supplies a multiplicative inverse for $c$ modulo $m$.
If $g=0$, then $s=t=0$, and the hypothesis forces $m=1$; take
$a=p=c=1$, $b=q=0$. Equations (1) hold also in this case. These two cases
exhaust the nonnegative integer $g$.

## 3. Commutation and exact ranks

An edge contributes one at each of its two endpoints to its vertex boundary.
For a loop the two contributions occur at the same vertex and cancel. A walk
has vertex boundary equal to the sum of its initial and final vertices:
every intermediate vertex occurs twice in the concatenation. A closed walk
therefore has zero vertex boundary.

The four traversals

\[
h_z,\quad v_{z+s},\quad h_{z+t}\text{ reversed},\quad v_z\text{ reversed}
\]

form a closed walk, including when vertices or edge labels coincide. Its
binary chain is $F_z$, so $HF_z^{\mathsf T}=0$. Consequently
$HF^{\mathsf T}=0$, and $B\subseteq C$.

We record the finite-dimensional linear algebra used for the ranks. If a
linear map $T:U\to W$ acts on finite-dimensional vector spaces, choose a
basis of $\ker T$ and extend it to a basis of $U$. The images of the added
basis vectors are a basis of $\operatorname{im}T$: they span by expansion in
the domain basis, and a dependence would put a combination of the added
vectors in the kernel, contradicting independence of the full basis. Thus
$\dim U=\dim\ker T+\dim\operatorname{im}T$.

A subspace of dimension $r$ in an $N$-dimensional space has an
annihilator of dimension $N-r$: extend its basis to a full basis; a linear
functional vanishing on the subspace is determined freely and uniquely by its
values on the $N-r$ added basis vectors. Coordinate pairing identifies the
space with its dual, because a functional is uniquely determined by its
values on the coordinate basis. It follows that, for any matrix, its kernel
has codimension equal to the dimension of its row span. Applied also to the
transpose and to the map taking coefficient vectors to linear combinations
of rows, these facts prove equality of row rank and column rank. They also
justify the rank-nullity calculations that follow.

For a function $f:V\to\mathbb F_2$, the coordinates of $H^{\mathsf T}f$
are

\[
(H^{\mathsf T}f)(h_z)=f(z)+f(z+s),\qquad
(H^{\mathsf T}f)(v_z)=f(z)+f(z+t).
\]

Therefore $H^{\mathsf T}f=0$ precisely when $f$ has equal values at the
ends of every edge. Connectivity then makes $f$ constant; every constant
function does satisfy the equations. Because $V$ is nonempty, constant
functions form a one-dimensional space. Hence
$\operatorname{rank}H=m-1$.

Define an edge permutation $J$ by

\[
J(h_z)=v_{-z},\qquad J(v_z)=h_{-z}.
\]

It is an involution. The pulled-back chain $J^*x$ is defined by
$(J^*x)(e)=x(J(e))$. Substitution in the four-term formulas of Section 1
gives

\[
J^*H_z=F_{-z},\qquad J^*F_z=H_{-z}. \tag{2}
\]

For completeness, the horizontal coordinates of the first identity have
possible nonzero terms at $h_{-z}$ and $h_{-z+t}$; its vertical coordinates
have possible nonzero terms at $v_{-z}$ and $v_{-z+s}$. These are exactly
the terms of $F_{-z}$. If any listed labels coincide, both sides contain
both terms and cancel them. Applying the involution to the first identity,
and replacing $z$ by $-z$, proves the second identity.

Permuting coordinates and permuting rows preserve their span dimension.
Thus $\operatorname{rank}F=m-1$,
$\dim C=2m-(m-1)=m+1$, and $\dim B=m-1$. The quotient $C/B$ has
dimension two: extend a basis of $B$ to a basis of $C$; the added two
vectors give a basis of the quotient. This also proves the claimed encoded
dimension.

## 4. Integer winding coordinates and complete logical detection

Choose the data in (1). For $z\in V$, let $\phi(z)$ be the unique integer
in $\{0,\ldots,m-1\}$ representing $c^{-1}z$. A forward horizontal edge
has $\phi(z+s)-\phi(z)\equiv a\pmod m$, and a forward vertical edge has
$\phi(z+t)-\phi(z)\equiv b\pmod m$. Define integer edge carries

\[
\kappa(h_z)=\frac{a-\phi(z+s)+\phi(z)}m,\qquad
\kappa(v_z)=\frac{b-\phi(z+t)+\phi(z)}m.
\]

The congruences prove both quotients are integers. Attach to each edge a
two-coordinate binary label

\[
\ell(h_z)=(\kappa(h_z)\bmod2,q\bmod2),\qquad
\ell(v_z)=(\kappa(v_z)\bmod2,-p\bmod2).
\]

For a binary chain define its label sum
$L(x)=\sum_e x(e)\ell(e)\in\mathbb F_2^2$. This is a linear map.

For a walk $w$, add the carries with the traversal signs: forward edges
contribute $\kappa(e)$, reverse edges contribute $-\kappa(e)$. Let this
integer sum be $k(w)$. The definitions, summed along the walk, give

\[
a u(w)+b v(w)=\phi(\mathrm{end}(w))-\phi(\mathrm{start}(w))+m k(w). \tag{3}
\]

The potential terms cancel between successive traversals. A reverse edge
satisfies the same identity because all its forward terms are negated.
Moreover, reduction modulo two erases the distinction between a positive
and a negative traversal, since $1=-1$ in $\mathbb F_2$. Thus

\[
L(x(w))=(k(w)\bmod2,\ (q u(w)-p v(w))\bmod2). \tag{4}
\]

Repeated traversals cause no discrepancy in (4): two occurrences contribute
zero both to the binary chain and to the reduced label sum.

For a closed walk, (3) becomes $au+bv=mk$. If its displacement is zero,
then $mk=0$; because $m>0$, this forces $k=0$. Both coordinates in (4)
then vanish. In particular, the square walks have zero displacement, so
$L(F_z)=0$ for every $z$. Linearity gives $B\subseteq\ker L$.

Every integer pair $(u,v)$ with $su+tv\equiv0\pmod m$ is the
displacement of a closed walk based at zero. First take $\lvert u\rvert$
horizontal steps, forward if $u\ge0$ and reverse if $u<0$; then take
$\lvert v\rvert$ vertical steps, forward if $v\ge0$ and reverse if
$v<0$. For each coordinate these two inequalities exhaust the integers,
and a zero coordinate gives zero steps. The endpoint is $su+tv=0$ in $V$,
and the length is $\lvert u\rvert+\lvert v\rvert$.

Apply this construction to the two displacements

\[
P=(mp,mq),\qquad Q=(b,-a).
\]

They satisfy the period relation by (1). For $P$, equations (1) and (3)
give $mk=m(ap+bq)=m$, so $k=1$, and
$q(mp)-p(mq)=0$. Its binary cycle therefore has label $(1,0)$.
For $Q$, equation (3) gives $mk=ab-ba=0$, so $k=0$, and
$qb-p(-a)=bq+ap=1$. Its binary cycle has label $(0,1)$.

These cycles show that $L|_C:C\to\mathbb F_2^2$ is onto. Its kernel has
dimension $\dim C-2=m-1$. This kernel contains $B$, also of dimension
$m-1$, so they are equal: extend any basis of $B$ within the kernel;
equal dimensions permit no additional vector. We have proved the complete
logical-detection criterion

\[
x\in C\quad\Longrightarrow\quad
\bigl(x\in B\ \Longleftrightarrow\ L(x)=0\bigr). \tag{5}
\]

## 5. Every nontrivial cycle contains a short nonzero period relation

For a binary cycle $x$, let $S$ be its edge support. At each vertex, the
number of incident edge ends of $S$ is even: this is exactly the equation
$Hx=0$. A loop contributes two ends and hence zero modulo two.

We prove that $S$ decomposes into edge-disjoint closed trails, where a trail
does not repeat an edge. If $S$ is empty, the empty decomposition suffices.
Otherwise begin at an endpoint of an edge in $S$, traverse it, and extend
the resulting trail by an unused incident edge whenever such an edge exists.
This process terminates because $S$ is finite and every extension uses a
new edge. The terminal vertex must be the initial vertex: if they differed,
the used edge ends at the terminal vertex would be odd. Indeed, every visit
before the last uses an arrival and a departure, while the last visit has
an arrival only; loops use two ends in a single visit. Since the total number
of incident ends of $S$ is even, an odd number of used ends leaves an odd,
and therefore positive, number of unused ends there. An unused incident edge
would extend the trail, contrary to termination. The trail is therefore
closed. Its used edges have even incidence at every vertex, so removing
them leaves an even-incidence edge set of smaller cardinality. Induction on
$\lvert S\rvert$ finishes the decomposition. The induction has just two
cases, empty and nonempty; these exhaust finite edge sets.

Suppose $x\in C\setminus B$. Criterion (5) gives $L(x)\ne0$. In the
edge-disjoint decomposition, the binary chains of the trails sum to $x$.
Therefore at least one trail $w$ has nonzero label: if each label were zero,
linearity would make their sum zero. Its displacement $(u,v)$ is nonzero,
because (3)–(4) show that a closed walk of zero displacement has zero label.
Summing its vertex increments gives $su+tv\equiv0\pmod m$.

Let $N_h^+,N_h^-,N_v^+,N_v^-$ be the numbers of its four traversal types.
Then

\[
u=N_h^+-N_h^-,\quad v=N_v^+-N_v^-,\quad
L(w)=N_h^++N_h^-+N_v^++N_v^-.
\]

For nonnegative integers $A,B$, $\lvert A-B\rvert\le A+B$: if
$A\ge B$ the left side is $A-B$, and if $A<B$ it is $B-A$; both
are at most $A+B$. These cases exhaust the ordered pair $A,B$. Applying
this inequality twice yields

\[
\lvert u\rvert+\lvert v\rvert\le L(w)\le\lvert S\rvert
=\operatorname{wt}(x). \tag{6}
\]

The second inequality holds because the trail uses no edge twice and all its
edges belong to $S$. By the definition of $\lambda$, (6) implies
$\operatorname{wt}(x)\ge\lambda$. Thus $d_Z\ge\lambda$.

The minimum in the definition of $\lambda$ exists. The pair $(m,0)$
is a nonzero period relation, so the set of possible lengths is a nonempty
set of positive integers, which has a least member. Positivity follows
because a sum of two nonnegative absolute values is zero only when both
integers are zero.

## 6. A shortest relation gives a logical of exactly that weight

Choose a relation $(u,v)\ne(0,0)$ of length $\lambda$, and take the
closed signed walk constructed in Section 4. Denote its carry by $k$ and
put $l=qu-pv$. The closed-walk identity is $au+bv=mk$. Expanding with
$ap+bq=1$ gives the two reconstruction formulas

\[
\begin{aligned}
pmk+bl&=p(au+bv)+b(qu-pv)=(ap+bq)u=u,\\
qmk-al&=q(au+bv)-a(qu-pv)=(bq+ap)v=v.
\end{aligned} \tag{7}
\]

If the walk's binary label were zero, (4) would make $k$ and $l$ even.
Write $k=2k'$, $l=2l'$, and define

\[
u'=pmk'+bl',\qquad v'=qmk'-al'.
\]

Formula (7) gives $u=2u'$, $v=2v'$. This pair is nonzero, since a zero
pair would make $u=v=0$. Direct expansion gives

\[
au'+bv'=m(ap+bq)k'+(ab-ba)l'=mk'.
\]

Multiplying this equation modulo $m$ by $c$, and using (1), gives
$su'+tv'\equiv0\pmod m$. The new nonzero period relation has length
$(\lvert u\rvert+\lvert v\rvert)/2=\lambda/2<\lambda$, where the strict
inequality uses $\lambda>0$. This contradicts minimality. Therefore the
walk has nonzero binary label, and its chain is in $C\setminus B$ by (5).

Every nonzero coordinate of its binary chain belongs to an edge traversed
at least once. The number of such distinct edges is at most the number of
traversals. Hence its weight is at most its length, which is $\lambda$.
Section 5 proves the reverse inequality for this nontrivial cycle. Its
weight is exactly $\lambda$, proving $d_Z=\lambda$.

## 7. The dual distance and all degenerate cases

The permutation $J$ in (2) preserves pairing and weight: it merely
reorders the summands or the support elements. Equations (2) give

\[
J^*(\ker H)=\ker F,\qquad
J^*\operatorname{span}\{F_z\}=\operatorname{span}\{H_z\}.
\]

For the first equality, $z\in\ker H$ means
$\langle H_r,z\rangle=0$ for every $r$; preservation of pairing and
(2) turn these equations into
$\langle F_{-r},J^*z\rangle=0$ for every $r$. Every row index occurs
because negation is a bijection. Applying the involution proves the reverse
inclusion. For the second equality, linearity sends every generator $F_z$
to $H_{-z}$, and every target generator occurs; linearity and the
involution prove equality. Thus $J^*$ is a weight-preserving bijection
between nontrivial Z and X logicals. Their least weights are equal, so
$d_X=d_Z=\lambda$.

No step required distinct endpoints or distinct edges in a square. Vertex
incidence counted loop ends twice, binary chains canceled repeated edges,
and the trail decomposition retained edge labels. For $m=1$, there is
one vertex and two labelled loops. All four-term rows cancel, so both check
ranks are zero and both one-edge chains are logicals. Every integer pair
satisfies the period relation, whose minimum nonzero length is one. Thus
the formulas give $[[2,2,1]]$, in agreement with the direct definition.
For $m>1$, the gcd assumption excludes $s=t=0$, and the $g>0$ case of
Section 2 applies. These two cases exhaust all positive $m$. The main
statement follows.

## 8. The analytic rotated-square family

This section proves the arithmetic required for the second main statement.

### 8.1 Integral coordinates

Let $a,b$ be coprime nonnegative integers with $a>0$, put $M=a^2+b^2$,
and suppose $au+bv=Mk$. The gcd argument in Section 2 gives integers $p,q$
with $ap+bq=1$. Set $R=bu-av$. Direct multiplication gives

\[
\begin{aligned}
aR&=ab u-a^2v=b(au+bv)-(a^2+b^2)v=M(bk-v),\\
bR&=b^2u-abv=(a^2+b^2)u-a(au+bv)=M(u-ak).
\end{aligned}
\]

Multiply these identities by $p,q$, respectively, and add. Since $ap+bq=1$,

\[
R=M\bigl[p(bk-v)+q(u-ak)\bigr].
\]

Define integers $i=p(bk-v)+q(u-ak)$ and $j=k$. Then
$Mi=bu-av$ and $Mj=au+bv$. Consequently

\[
\begin{aligned}
M(bi+aj)&=b(bu-av)+a(au+bv)=(a^2+b^2)u=Mu,\\
M(-ai+bj)&=-a(bu-av)+b(au+bv)=(a^2+b^2)v=Mv.
\end{aligned}
\]

The assumption $a>0$ implies $M>0$, so cancellation yields

\[
u=bi+aj,\qquad v=-ai+bj. \tag{8}
\]

Conversely, any integers $i,j$ in (8) satisfy
$au+bv=(a^2+b^2)j=Mj$. Thus these are exactly the integer period
relations modulo $M$, with an explicit integral coordinate formula.

### 8.2 A uniform norm inequality

For nonnegative integers $a,b$ and integers $i,j$ not both zero, we claim

\[
|bi+aj|+|-ai+bj|\ge a+b. \tag{9}
\]

The following three cases are pairwise disjoint and exhaustive: $i=0$;
$i\ne0$ and $j=0$; $i\ne0$ and $j\ne0$. If $i=0$, then $j\ne0$, so
$|j|\ge1$, and the left side of (9) is $(a+b)|j|\ge a+b$. If $i\ne0$
and $j=0$, it is $(a+b)|i|\ge a+b$ because $|i|\ge1$. In the remaining
case put $U=bi+aj$, $V=-ai+bj$, and $W=|U|+|V|$. Both nonzero integers
$i,j$ have squared value at least one, so $i^2+j^2\ge2$. Expansion gives

\[
\begin{aligned}
U^2+V^2
 &=b^2i^2+2abij+a^2j^2+a^2i^2-2abij+b^2j^2\\
 &=(a^2+b^2)(i^2+j^2)\ge2(a^2+b^2).
\end{aligned}
\]

Also $W^2=U^2+V^2+2|U||V|\ge U^2+V^2$, and
$2(a^2+b^2)-(a+b)^2=(a-b)^2\ge0$. Hence $W^2\ge(a+b)^2$.
Both $W$ and $a+b$ are nonnegative. If $W<a+b$, then $a+b-W>0$ and
$a+b+W>0$, so
$(a+b)^2-W^2=(a+b-W)(a+b+W)>0$, a contradiction. This proves (9).

### 8.3 The lattice minimum and the code parameters

Now assume $a,h>0$, $b\ge0$, $\gcd(a,b)=1$, and $m=hM$. If a nonzero
integer pair satisfies $m\mid au+bv$, write $au+bv=hMk$ with integer
$k$ and apply Section 8.1 with $hk$ in place of $k$. The pair of
coordinates $(i,j)$ in (8) is nonzero because zero coordinates would
give $u=v=0$. Inequality (9) proves $|u|+|v|\ge a+b$.

The pair $(b,-a)$ is nonzero because $a>0$, satisfies
$ab+b(-a)=0$, and has length $a+b$. Thus the exact shortest period
length is $a+b$. Coprimality of $a,b$ gives
$\gcd(\gcd(a,b),m)=\gcd(1,m)=1$. Sections 2–7 therefore supply the
ranks, encoded dimension, and both exact CSS distances in the second
main statement.

For $a=r,b=r+1,h=1$ with $r\ge1$, any common divisor of $r,r+1$
divides their difference one. Thus the coprimality assumption holds.
Expansion gives

\[
2(r^2+(r+1)^2)=4r^2+4r+2=(2r+1)^2+1,\qquad
r+(r+1)=2r+1,
\]

which proves the stated one-parameter specialization.

## 9. Uniform check weights and qubit degrees

Each row displayed in Section 1 is a sum of four coordinate vectors.
A nonzero entry of the sum must occur among those four coordinates,
so its support has size at most four. Coincident appearances cancel
modulo two and cannot increase that size.

A horizontal edge $h_z$ occurs in vertex rows only at indices $z$
and $z+s$: these are its source and target. A vertical edge $v_z$
occurs in vertex rows only at $z$ and $z+t$. These are the two
exhaustive edge types. Thus each vertex-check column has at most two
nonzero entries.

In a square row $F_w$, a horizontal edge $h_z$ occurs only if
$w=z$ or $w+t=z$, that is, only at row indices $z,z-t$. A vertical
edge $v_z$ occurs only if $w+s=z$ or $w=z$, that is, only at
$z-s,z$. Again these two edge types exhaust all qubits. Each
square-check column therefore has at most two nonzero entries.
Coincident row indices cancel the two appearances; the upper bound
remains valid for zero steps and for $m=1$.

## 10. Lean correspondence

The family matrices, cycle and boundary spaces, commutation, ranks, winding
coverage, and lower bound already have generic formalizations under
`QldpcVerification.Bicycle.Connected`. The new module
`lean/QldpcVerification/Bicycle/ShortestVector.lean` proves:

- `Lattice.Walk.binaryChain_weight_le_length`: the support bound used in
  Section 6, including repeated edges;
- `Connected.closedPath_length`: the signed path realizes exactly the
  integer absolute-value length;
- `Connected.PeriodBasis.half_relation`: zero binary winding coordinates
  permit halving a period relation, as in (7);
- `Connected.shortest_relation_cycle`: a minimizing nonzero integer pair
  yields a nontrivial cycle of precisely that weight;
- `Connected.Match.parameters_of_shortest`: any recognized family matrices
  have two encoded qubits and both exact CSS distances, given an analytic
  lattice lower bound and a matching integer pair.

The noncomputable definition `minimumNorm` selects the least attained integer
length using the well-ordering of the natural numbers. The theorems
`minimumNorm_attained` and `minimumNorm_lower` prove attainment and
minimality. The unconditional capstone `Connected.Match.parameters_minimum`
therefore identifies both CSS distances with this minimum for every jointly
generating step pair, without a supplied lower bound or a supplied minimizing
pair. Its existence argument is the relation $(m,0)$ in Section 5.

The last theorem replaces two physical support-certificate hypotheses in
the older parameter interface by a single integer shortest-vector witness.
It accepts arbitrary jointly generating steps and arbitrary positive cyclic
length. No exhaustive search or finite grid is an input to this argument.


The generic row and column bounds are formalized as
`Connected.face_weight_le_four`, `Connected.vertex_weight_le_four`,
`Connected.vertex_column_weight_le_two`, and
`Connected.face_column_weight_le_two`.
The integer arithmetic is formalized in
`lean/QldpcVerification/Lattice/Gaussian.lean`, and the family capstones
`GaussianFamily.parameters` and `GaussianFamily.ranks` are in
`lean/QldpcVerification/Bicycle/GaussianFamily.lean`.

## 11. Attribution and scope

The geometric interpretation and the odd-distance rotated-square family
are established mathematics, not claimed inventions. Arnault, Gaborit,
and Saussay, “(2,2)-GB Codes: Classification and Comparison with weight-4
Surface Codes,” arXiv:2507.21237v1, Section II-E2, Theorem II.7,
Corollary II.8, and Lemma IV.4, discuss the period-lattice description,
distance correspondence, and the odd-distance parameters:
[primary paper](https://arxiv.org/html/2507.21237v1).

This document proves the needed facts independently. Its contribution to
this repository is a uniform analytic interface, a symbolic upper-witness
construction that joins the existing lower bound, and Lean formalization
of the coprime two-parameter family and all positive cover factors $h$.
No claim of mathematical priority is made.
