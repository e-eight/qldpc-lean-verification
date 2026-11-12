# All cyclic binomial codes: removal of the connectivity hypothesis

**Working grade: PROPOSITION.** The argument below is complete, but this
supplement requires a fresh hostile referee pass and replay of its final Lean
capstones. It is intended to be incorporated into the connected-family proof
document before promotion to a final theorem.

## Main statement

Let $m>0$ and $s,t\ge0$ be integers, and put
$c=\gcd(\gcd(s,t),m)$. For the cyclic binomial CSS code defined in Section 1
of the connected-family document, there are $2m$ physical qubits, both check
ranks are $m-c$, the number of encoded qubits is $2c$, and both CSS distances
are

\[
d_X=d_Z=\lambda(m;s,t)
=\min\{|u|+|v|:(u,v)\in\mathbb Z^2\setminus\{(0,0)\},
\quad m\mid su+tv\}.
\]

There is no connectivity hypothesis. The code is a direct sum of $c$
identical connected components, and each component has this same distance.
The row-weight bound four and the column-weight bound two for each check
type hold without alteration.

## 1. Arithmetic of the component parameters

The gcd characterization and integer-combination proof in Section 2 of the
connected-family document apply here. In particular, $c$ is a nonnegative
integer that divides $m,s,t$, and every integer dividing all three divides
$c$. Since $m>0$ and $c\mid m$, one cannot have $c=0$: zero divides only
zero. Thus $c>0$.

Define the nonnegative integers

\[
\ell=m/c,\qquad a=s/c,\qquad b=t/c.
\]

Divisibility gives the exact identities

\[
m=c\ell,\qquad s=ca,\qquad t=cb.
\tag{C1}
\]

Because $m,c>0$, the identity $m=c\ell$ implies $\ell>0$.

We claim $\gcd(\gcd(a,b),\ell)=1$. Let this last gcd be $q$.
It divides the positive integer $\ell$, so $q>0$. Since $q$ divides
$a,b,\ell$, the integer $cq$ divides $s,t,m$ by (C1), and therefore
divides $c$. Write $c=cqk$ with an integer $k$. Cancellation of
$c\ne0$ gives $1=qk$. Since $q$ is positive, this forces $q=1$:
$k$ must be positive, and positive integers with product one are both one.
This proves the claim, including $a=0$ or $b=0$.

## 2. Explicit vertex and edge decomposition

Use the vertex and edge definitions of Section 1 of the connected-family
document. Let

\[
R=\{0,1,\ldots,c-1\},\qquad V'=\mathbb Z/\ell\mathbb Z.
\]

The set $R$ is nonempty because $c>0$. Define a map

\[
\Phi:R\times V'\longrightarrow\mathbb Z/m\mathbb Z,\qquad
\Phi(r,j)=r+cj\pmod m.
\tag{C2}
\]

It is well-defined: changing an integer representative of $j$ by $\ell k$
changes $r+cj$ by $c\ell k=mk$, which is zero modulo $m$.

Here is an explicit inverse. Given a residue modulo $m$, choose its unique
representative $N$ with $0\le N<m$. Divide $N$ by the positive integer $c$:

\[
N=cJ+r,\qquad 0\le r<c,\qquad J\ge0.
\tag{C3}
\]

The quotient satisfies $J<\ell$. Otherwise $J\ge\ell$ would imply
$N=cJ+r\ge c\ell=m$, contradicting the choice of $N$. Send the residue
to $(r,J\bmod\ell)$.

These constructions are mutually inverse. Starting with $N$, equation
(C3) gives $\Phi(r,J)=N\bmod m$. Starting with $(r,j)$, choose the
representative $J$ of $j$ in $\{0,\ldots,\ell-1\}$. Then
$0\le r+cJ\le(c-1)+c(\ell-1)=m-1$. Thus the least nonnegative
representative of $\Phi(r,j)$ is exactly $r+cJ$, whose division by $c$
returns remainder $r$ and quotient $J$. The uniqueness of quotient and
remainder follows directly: if $cJ+r=cJ'+r'$ with both remainders in
$[0,c-1]$, then $c(J-J')=r'-r$; a multiple of $c$ strictly between
$-c$ and $c$ must be zero, so $r=r'$ and $J=J'$.

Let $h'_j,v'_j$ be the two labelled edge types on $V'$, with respective
steps $a,b$. Extend (C2) to a bijection of edge sets by

\[
(r,h'_j)\longmapsto h_{\Phi(r,j)},\qquad
(r,v'_j)\longmapsto v_{\Phi(r,j)}.
\tag{C4}
\]

Each is a bijection on its labelled type because $\Phi$ is a bijection
on vertices; the two types are disjoint in both source and target.
The map respects endpoints. Equations (C1)–(C2) give

\[
\begin{aligned}
\Phi(r,j)+s&=r+cj+ca=\Phi(r,j+a)\pmod m,\\
\Phi(r,j)+t&=r+cj+cb=\Phi(r,j+b)\pmod m.
\end{aligned}
\tag{C5}
\]

These identities do not change $r$. Thus edges never join different
values of $r$, and within each fixed $r$ they are exactly the cyclic
graph with period $\ell$ and steps $a,b$. The coprimality established
in Section 1 and the connectivity proof in Section 2 of the connected
document show that each such graph is connected. Hence there are
exactly $c$ connected components, labelled by $R$.

This argument also handles zero steps: an edge with a zero step remains
a separately labelled loop under (C4). When $a$ or $b$ is a multiple
of $\ell$, (C5) again identifies its two endpoints while retaining its
edge label.

## 3. The check matrices split into identical blocks

Let $H',F'$ be the vertex and square checks for the period $\ell$ and
steps $a,b$. Pull a physical chain back along (C4). The chain space is
then identified with a tuple $(x_r)_{r\in R}$ of component chains.

Under this identification, the vertex row indexed by $\Phi(r,j)$
has its four appearances at

\[
(r,h'_j),\quad(r,h'_{j-a}),\quad
(r,v'_j),\quad(r,v'_{j-b}).
\]

It is therefore $H'_j$ in component $r$ and zero in every other
component. The square row at $\Phi(r,j)$ has its four appearances at

\[
(r,h'_j),\quad(r,v'_{j+a}),\quad
(r,h'_{j+b}),\quad(r,v'_j).
\]

It is $F'_j$ in component $r$ and zero elsewhere. These equalities
are identities of sums over $\mathbb F_2$. If two appearances denote
the same physical edge, both sides cancel those appearances. Thus the
identities require no distinctness of vertices or edges.

Consequently the reordered matrices are block diagonal with $c$
copies of $H'$ and $c$ copies of $F'$. Their row spaces are the direct
sums of the component row spaces. To verify the latter assertion in
both directions, each original row belongs to its one component
row space, so every row combination lies in the product of those
spaces. Conversely, a tuple whose $r$th coordinate lies in the
component row space has a row-combination expression in each
component; summing those expressions over the finite set $R$
produces the tuple as an original row combination.

The dimension of this direct sum is the sum of the component
dimensions. Indeed, embed a basis of each component space by filling
all other components with zero. The union spans by componentwise
expansion. If a linear combination of this union vanishes, projection
to any component makes the coefficients of its basis vanish. Since
this holds for every component, the union is independent.

The connected theorem gives both component check ranks $\ell-1$.
Therefore the full ranks are

\[
c(\ell-1)=c\ell-c=m-c.
\]

There are $2m$ physical qubits, so the encoded dimension is
$2m-(m-c)-(m-c)=2c$.

## 4. Logical spaces and exact distance of the direct sum

Write $C'=\ker H'$ and $B'=\operatorname{rowspan}F'$, and let
$C=\ker H$, $B=\operatorname{rowspan}F$. The preceding block identities
give

\[
x\in C\ \Longleftrightarrow\ x_r\in C'\text{ for every }r,\qquad
x\in B\ \Longleftrightarrow\ x_r\in B'\text{ for every }r.
\tag{C6}
\]

The first equivalence holds because the matrix equations in component
$r$ are precisely $H'x_r=0$. The second is the row-space statement
proved in Section 3. Thus $x$ is a nontrivial Z logical exactly when
every $x_r$ is a component cycle and at least one $x_r$ is not a
component boundary. For the last assertion, if every component were
a boundary, (C6) would make $x$ a boundary; if one component is not
a boundary, the same equivalence excludes $x$ from $B$.

Because the physical edge set is partitioned by its component label,
counting the support gives

\[
\operatorname{wt}(x)=\sum_{r\in R}\operatorname{wt}(x_r).
\tag{C7}
\]

Let $d'$ be the exact Z distance of the component code. It exists and
is positive by the connected theorem. A nontrivial full Z logical
has at least one nontrivial component, say $x_{r_0}$. Its component
weight is at least $d'$, and every summand in (C7) is nonnegative,
so the full weight is at least $d'$.

For the matching upper bound, take a component logical of weight
$d'$, whose existence is part of the connected theorem. Place it
in component $0\in R$, and place zero in every other component.
Zero is a cycle and a boundary in every component. Equations
(C6) show that the resulting tuple is a nontrivial full logical;
(C7) shows that its weight is $d'$. Therefore $d_Z=d'$.

The X argument uses $C'_X=\ker F'$ and
$B'_X=\operatorname{rowspan}H'$. The block equations prove
$x\in\ker F$ exactly when all $x_r\in C'_X$, and the row-space
calculation proves $x\in\operatorname{rowspan}H$ exactly when all
$x_r\in B'_X$. Thus a nontrivial X logical contains a nontrivial
X component. Formula (C7) bounds its weight below by the exact
component X distance. A minimum-weight component X logical,
inserted in component zero with zeros elsewhere, gives equality.
The connected theorem equates the component X and Z distances,
so both full distances equal $d'$.

## 5. The integer relation lattice is unchanged by factoring

For every integer pair $(u,v)$, equations (C1) imply

\[
\begin{aligned}
m\mid su+tv
&\ \Longleftrightarrow\
 c\ell\mid c(au+bv)\\
&\ \Longleftrightarrow\
 \ell\mid au+bv.
\end{aligned}
\tag{C8}
\]

For the final equivalence, if $c(au+bv)=c\ell k$ for an integer
$k$, cancel $c\ne0$ to obtain $au+bv=\ell k$. Conversely,
multiplying this last equation by $c$ gives the first divisibility.
The set of admissible nonzero integer pairs is therefore exactly
the same for the full and component codes. Its length function
$|u|+|v|$ has not been changed. In particular,

\[
\lambda(m;s,t)=\lambda(\ell;a,b).
\tag{C9}
\]

The connected theorem identifies $d'$ with the right side of (C9).
Combining Sections 3–5 proves every parameter in the main statement.
The row and column bounds were proved directly for arbitrary
positive period and arbitrary steps in Section 9 of the connected
document, so their hypotheses already cover this setting.

The case $s=t=0$ is included explicitly: then $c=m$, $\ell=1$,
and $a=b=0$. The decomposition consists of $m$ one-vertex components,
each with two labelled loops and no nonzero check. Both ranks
are zero, the encoded dimension is $2m$, and both distances are
one. Every integer pair satisfies the period relation, whose least
nonzero length is one. When at least one of $s,t$ is nonzero, the
same proof applies with $c>0$ and $\ell>0$ established in Section 1.
These two cases exhaust the nonnegative step pairs.

## 6. Formal correspondence

The existing component formalizations provide the explicit vertex
and edge decomposition, block identities, ranks, and exact-distance
transfer:

- Bicycle/CyclicComponents.lean;
- Bicycle/ComponentParameters.lean;
- Bicycle/GcdComponents.lean.

The new Bicycle/CyclicDistance.lean supplies the remaining exact
minimum interface. Its relation_scaled_iff proves (C8), and
minimumNorm_scaled proves (C9). Match.parameters_factored combines
the connected minimum theorem with the block distance equivalences.
Match.parameters_all applies the gcd factorization to every
positive cyclic period and arbitrary nonnegative steps. The
pre-existing gcd rank theorems supply both ranks $m-c$.

No shortest-vector search, generated finite case list, numerical
certificate, or computational experiment is an input to this
argument.
