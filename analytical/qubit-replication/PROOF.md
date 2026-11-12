# Exact CSS parameters under uniform qubit replication

**Grade: THEOREM.** Complete hand proof, three independent hostile reviews,
adversarial author rereading, and guarded Lean replay.

## Main theorem

Let a binary CSS code have a finite physical set $Q$, X-check matrix $A$,
and Z-check matrix $B$, with $AB^{\mathsf T}=0$. Let $n=|Q|$, and let

\[
r_X=\dim\operatorname{row}(A),\qquad
r_Z=\dim\operatorname{row}(B),\qquad k=n-r_X-r_Z.
\]

Fix a nonempty finite set $I$, choose $i_0\in I$, and write $r=|I|$.
Replace each physical coordinate $q$ by the $r$ coordinates $(i,q)$.
The following displayed rows define the replicated code:

* For every old X row $a$, put its entries on the anchor coordinates
  $(i_0,q)$, with zero entries on every other replica.
* For every $q\in Q$ and $i\in I\setminus\{i_0\}$, add the X row
  $e_{(i,q)}+e_{(i_0,q)}$.
* For every old Z row $b$, put the entry $b(q)$ at every $(i,q)$.

Then these rows commute. Their ranks and encoded dimension are

\[
r'_X=r_X+n(r-1),\qquad r'_Z=r_Z,\qquad k'=k.
\]

If both original sector distances exist, then both replicated sector
distances exist and satisfy

\[
\boxed{d'_X=d_X,\qquad d'_Z=r d_Z.}
\]

If the old X/Z check weights are bounded by $w_X,w_Z$, respectively, the
new bounds are $\max(w_X,2)$ and $r w_Z$. If an old qubit belongs to at
most $\delta_X$ X checks and $\delta_Z$ Z checks, every new qubit belongs
to at most $\delta_X+r$ X checks and $\delta_Z$ Z checks. Thus for each
fixed positive $r$, this operation takes a qLDPC family to a qLDPC family,
preserves its encoded dimension, and gives its exact asymmetric distances.
The theorem does not claim uniform sparsity if $r$ itself grows.

The statements allow dependent original rows. Neither the rank result nor
the sparsity result assumes the existence of any nontrivial logical.

## 1. Binary vector spaces and distance

Write $F=\{0,1\}$ for the field with addition and multiplication modulo
two. In particular $1+1=0$. A vector on a finite set $Q$ is a function

\[
x:Q\longrightarrow F.
\]

Its support is $\{q:x(q)\ne0\}$, and its Hamming weight $\operatorname{wt}(x)$
is the number of elements in this support. The vector $e_q$ has value one
at $q$ and zero at every other coordinate. The dot product is

\[
x\cdot z=\sum_{q\in Q}x(q)z(q).
\]

The row space of a matrix is the space of binary linear combinations of
its rows. Write

\[
U=\operatorname{row}(A),\quad V=\operatorname{row}(B),\quad
S_X=\ker B,\quad S_Z=\ker A.
\]

The equation $AB^{\mathsf T}=0$ says that every row of $A$ has dot
product zero with every row of $B$. Expanding linear combinations of
rows therefore gives $U\subseteq S_X$ and $V\subseteq S_Z$.

A nontrivial X logical is a vector in $S_X\setminus U$, and a nontrivial
Z logical is a vector in $S_Z\setminus V$. If the relevant set is
nonempty, its distance is the smallest Hamming weight in that set.
These sets are finite, so a smallest weight is attained. We assign no
distance to an empty set. A distance assertion in this document includes
both a vector attaining the stated value and a proof that no nontrivial
logical has smaller weight.

## 2. Three maps and their identities

For $y\in F^{I\times Q}$ and $x,z\in F^Q$, define

\[
(Py)(q)=\sum_{i\in I}y(i,q),\qquad
(Rx)(i,q)=x(q),\qquad
(Ex)(i,q)=
\begin{cases}
x(q),&i=i_0,\\
0,&i\ne i_0.
\end{cases}
\]

Each is a linear map because each output coordinate is a fixed sum of
input coordinates. For every $x$, the sum defining $PEx$ has one
possibly nonzero term, at $i_0$, and equals $x$. Thus $PE$ is the
identity and $P$ is surjective. If $Rx=Rz$, evaluating at $(i_0,q)$
for every $q$ gives $x=z$; hence $R$ is injective.

Expansion of the two finite sums gives the dot-product identity

\[
y\cdot Rz
=\sum_{q\in Q}\sum_{i\in I}y(i,q)z(q)
=\sum_{q\in Q}(Py)(q)z(q)
=Py\cdot z. \tag{1}
\]

The three weight relations are

\[
\operatorname{wt}(Ex)=\operatorname{wt}(x),\qquad
\operatorname{wt}(Rx)=r\operatorname{wt}(x),\qquad
\operatorname{wt}(Py)\le\operatorname{wt}(y). \tag{2}
\]

For the first equality, $q\mapsto(i_0,q)$ bijects the two supports.
For the second equality, the support of $Rx$ is exactly

\[
I\times\operatorname{supp}(x).
\]

For the inequality, if $(Py)(q)\ne0$, at least one term $y(i,q)$ is
nonzero; a sum all of whose terms are zero is zero. Consequently

\[
\operatorname{supp}(Py)
\subseteq\{q:\text{there exists }i\text{ with }y(i,q)\ne0\}.
\]

The set on the right is the image of $\operatorname{supp}(y)$ under
projection to $Q$. An image of a finite set has no more elements than
that set, proving the inequality. This argument holds for even and odd

$r$; it does not use $PR$ being the identity.

## 3. Exact stabilizer spaces

Let $p_{i,q}=e_{(i,q)}+e_{(i_0,q)}$. For $i=i_0$, this is zero. We may
include these zero rows in a matrix without changing its row space,
commutation, or nonzero row incidences. This is the convention used in
the Lean matrix definition.

The parity of every $p_{i,q}$ is zero. At base coordinate $q$, its two
contributions add to zero; at each other base coordinate both are zero.
For any $y\in F^{I\times Q}$, the following is an exact vector identity:

\[
\sum_{i\in I}\sum_{q\in Q}y(i,q)p_{i,q}=y+EPy. \tag{3}
\]

To check (3), expand its left side using the definition of $p_{i,q}$.
The terms $y(i,q)e_{(i,q)}$ sum to $y$, since exactly the term indexed
by a coordinate contributes at that coordinate. The remaining terms
are all on the anchor. Their coefficient at $(i_0,q)$ is

\[
\sum_i y(i,q)=(Py)(q),
\]

so they sum to $EPy$. This proves (3) at every coordinate. In particular,
when $Py=0$, the star rows span $y$. Thus they span exactly $\ker P$.

Write $U',V'$ for the two replicated stabilizer spaces. We claim

\[
U'=P^{-1}(U),\qquad V'=R(V). \tag{4}
\]

Each anchor X row has parity equal to its old row in $U$; every star
row has parity zero in $U$. Linearity proves $U'\subseteq P^{-1}(U)$.
For the reverse inclusion, if $Py\in U$, express $Py$ as a sum of old
X rows. Applying $E$ shows $EPy\in U'$. Identity (3) shows

\[
y+EPy\in U'.
\]

Adding these two vectors gives $y\in U'$, because $EPy+EPy=0$.
For the Z equality, each new Z row is the repeat of an old Z row.
Linearity of $R$ implies that all their linear combinations are exactly
the repeats of the old linear combinations, which is $R(V)$.

For $u'\in U'$ and $v'\in V'$, choose $v\in V$ with $v'=Rv$.
Then $Pu'\in U$ by (4), and (1) gives

\[
u'\cdot v'=Pu'\cdot v=0.
\]

Thus the displayed checks commute and define a CSS code.

## 4. Exact cycle spaces

An X vector $y$ has zero dot product with every replicated Z row
precisely when $Py$ has zero dot product with every old Z row, by (1).
Therefore its cycle space is

\[
S'_X=P^{-1}(S_X). \tag{5}
\]

A Z vector $z'$ has zero dot product with the star row $p_{i,q}$
precisely when

\[
z'(i,q)+z'(i_0,q)=0,
\]

equivalently $z'(i,q)=z'(i_0,q)$. These equations for every $i,q$
force $z'=Rz$, where $z(q)=z'(i_0,q)$. Conversely every $Rz$
satisfies all of them. Its dot product with an anchored old row $Ea$
is $a\cdot z$, by (1) and $PEa=a$. Thus all anchored X syndromes
vanish precisely when $z\in S_Z$. We have proved

\[
S'_Z=R(S_Z). \tag{6}
\]

Equations (4)--(6) yield the following complete logical description:

\[
y\in S'_X\setminus U'
\quad\Longleftrightarrow\quad Py\in S_X\setminus U, \tag{7}
\]

\[
z'\in S'_Z\setminus V'
\quad\Longleftrightarrow\quad
z'=Rz\text{ for a unique }z\in S_Z\setminus V. \tag{8}
\]

For (8), the uniqueness and preservation of nonmembership follow from
injectivity of $R$: if $Rz=Rv$ with $v\in V$, then $z=v\in V$.
All directions of (7) follow directly from the two inverse images.

## 5. Exact distances

Suppose $d_X$ exists. For every replicated nontrivial X logical $y$,
equations (7) and (2) give

\[
d_X\le\operatorname{wt}(Py)\le\operatorname{wt}(y).
\]

Choose an original X logical $x$ of weight $d_X$. The vector $Ex$
is a replicated nontrivial X logical because $PEx=x$, and it has weight

$d_X$ by (2). Both inequalities necessary for $d'_X=d_X$ are proved.

Suppose $d_Z$ exists. By (8) every replicated nontrivial Z logical has
the unique form $Rz$ for an old nontrivial Z logical $z$. Equation (2)
then gives

\[
\operatorname{wt}(Rz)=r\operatorname{wt}(z)\ge r d_Z.
\]

Repeating an old Z logical of weight $d_Z$ attains $r d_Z$. Thus

$d'_Z=r d_Z$. These arguments also show that the relevant logical set
is empty in the new code exactly when it was empty in the old code.

## 6. Ranks and encoded dimension

Because $PE$ is the identity, $F^{I\times Q}$ decomposes as

\[
F^{I\times Q}=E(F^Q)\mathbin{\oplus}\ker P. \tag{9}
\]

Indeed $y=EPy+(y+EPy)$, and applying $P$ to the second summand gives
zero. If $Ex\in\ker P$, then $x=PEx=0$, proving that the intersection
is zero. A basis of $F^Q$ consists of its $n$ unit vectors, and a
basis of $F^{I\times Q}$ consists of its $rn$ unit vectors. An
injective linear map takes a basis to a basis of its image, and bases
of two subspaces with zero intersection concatenate to a basis of
their sum: spanning and linear independence follow by projecting a
linear relation to each direct summand. Consequently (9) implies

\[
\dim\ker P=rn-n=n(r-1).
\]

The same decomposition restricted to $P^{-1}(U)$ gives

\[
P^{-1}(U)=E(U)\mathbin{\oplus}\ker P.
\]

The proof is the decomposition above with $Py\in U$; intersection
zero was already proved. Since $E$ is injective, (4) implies

\[
\dim U'=\dim U+\dim\ker P=r_X+n(r-1).
\]

Injectivity of $R$ and $V'=R(V)$ give $\dim V'=\dim V=r_Z$.
Subtracting the two ranks from $rn$ gives

\[
k'=rn-\bigl(r_X+rn-n\bigr)-r_Z=n-r_X-r_Z=k.
\]

## 7. Sparsity and families

An anchored old X row has its original weight by (2). A star row has
weight two when $i\ne i_0$: its two indicated coordinates are
different, so both entries are one, and all other entries are zero.
When $i=i_0$, its weight is zero. These two cases are exhaustive.
Hence every X row has weight at most $\max(w_X,2)$. A repeated Z row
has weight $r$ times its old weight, so every Z row has weight at most

$r w_Z$.

For a fixed new physical coordinate $(j,q)$, the old anchored X rows
contribute at most $\delta_X$ incidences: only when $j=i_0$ can any
contribute. Among star rows, a row $p_{i,e}$ can contribute only when

$e=q$, because both of its coordinates have base coordinate $e$.
There are at most $r$ choices of $i$, so these rows contribute at
most $r$ incidences. This proves the bound $\delta_X+r$. A Z row is
nonzero at $(j,q)$ exactly when its original row is nonzero at $q$,
giving exactly the original Z incidence count and the bound

$\delta_Z$.

A qLDPC family here means a collection of CSS codes whose check row
weights and numbers of incident checks per qubit are bounded by
constants independent of the family index. For a fixed $r$, the four
bounds just proved are constants whenever the original four bounds
are constants. The resulting physical size is $rn$, encoded dimension
is $k$, and sector distances are $d_X,r d_Z$. This proves the stated
family conclusion without a numerical certificate or a search.

## Formal correspondence

`lean/QldpcVerification/QubitReplication.lean` defines the maps as
`parity`, `replicate`, and `embed`; the displayed matrices as `HX` and `HZ`;
and proves `rowspace_HX`, `rowspace_HZ`, `kernel_HX`, `kernel_HZ`,
`commutation`, `exact_distances`, `ranks`, `encoded_dimension`,
`row_weights`, `x_column_weight_le`, and `z_column_weight`.

The formal exact-distance predicate is `Components.Distance`: it contains
both attainment and a universal lower bound. No generated certificate
or concrete code instance enters this proof.

## Attribution

This is repetition-code concatenation, a known construction. Daniel Gottesman,
*Stabilizer Codes and Quantum Error Correction* (1997), Sections 3.5 and 6.1,
provides the general stabilizer-concatenation construction
([primary thesis](https://thesis.caltech.edu/2900/02/THESIS.pdf)).
The proof above derives all required facts independently; no priority claim is made.
