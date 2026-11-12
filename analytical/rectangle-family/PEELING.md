# Working proof: constructive one-sided exactness

**Grade: PROPOSITION.** The mathematics below is proved on paper; generic Lean
replay of the peeling argument and independent refereeing remain obligations.
This file is a working note, not a final theorem artifact.

## Precise claim

For the rectangular code of `DRAFT.md`, put $M=m+2$ and $N=n+2$.
Every $H_Z$-cycle whose two consecutive physical rows $k,k+1$ are empty is
an X stabilizer. Here $0\le k\le M-2$. Every $H_X$-cycle whose two consecutive
physical columns are empty is a Z stabilizer.

A stronger auxiliary statement holds: an $H_Z$-cycle supported in the first
$r\le M-2$ rows is an X stabilizer, as is one supported in the last
$r\le M-2$ rows. The analogous assertions hold for Z cycles and columns.

## X-sector prefix peeling

Write a physical vector as row polynomials $(A_i(T),B_i(T))$ for $0\le i<M$,
with coefficients in $\mathbb F_2$ and degrees at most $N-1$ whenever nonzero.
Put $s=T^2$ and $t=T+T^2$. The $H_Z$-cycle equations are precisely

\[
 tA_i+A_{i+2}+B_i+B_{i+1}+sB_{i+2}=0\qquad(0\le i\le M-3).
\]

These equations follow by reading the coefficient at first exponent $i+2$
of $gA+fB$: $g=1+x^2(T+T^2)$ and $f=x+x^2+T^2$. All transverse coefficients
of this syndrome are tested, since the Z-anchor second coordinates range
from $0$ to $N+1$.

Suppose the vector is supported in rows $0,\ldots,r-1$, where $1\le r\le M-2$.
The cycle equation at index $i=r-1$ is valid: $r-1\le M-3$. Rows $r$ and
$r+1$ vanish, so this equation says

\[
 B_{r-1}=tA_{r-1}.
\]

Set $h=A_{r-1}$. If $h\ne0$, the largest exponent in $th$ is $\deg h+2$,
by the nonzero leading coefficient of each factor. Because $B_{r-1}$ fits in
$N$ coefficients, $\deg h+2\le N-1$. Hence $\deg h\le N-3$, so $h$ is a
linear combination of the permitted transverse anchor monomials
$1,T,\ldots,T^{N-3}$. If $N=2$, a nonzero $h$ would give degree at least two
but $B_{r-1}$ has degree at most one, a contradiction; thus $h=0$. This
handles the empty transverse anchor set explicitly.

Consider the X stabilizer combination

\[
 p=P\bigl(x^{r-3}h(T)(f,g)\bigr).
\]

Its first anchor coordinate $r-3$ lies between $-2$ and $M-1$; its
transverse anchors are allowed by the previous support argument. Its
physical rows are supported among $r-3,r-2,r-1$; any negative row is removed
by $P$. At row $r-1$, its components are exactly $(h,th)$, because the
$x^2$ coefficients of $f,g$ are $1,t$. It has no physical rows greater than
$r-1$. Thus subtracting $p$ removes row $r-1$ and leaves support in the first
$r-1$ rows. It remains a cycle, since X stabilizers are $H_Z$ cycles by
commutation. Induction on $r$, with the zero vector at $r=0$ as base case,
expresses the original vector as a sum of X stabilizers.

## X-sector suffix peeling

Suppose a cycle is supported in rows $a,\ldots,M-1$, where $a\ge2$.
The cycle equation with index $a-2$ is valid and both preceding physical
rows vanish. It gives

\[
 A_a=sB_a.
\]

Set $h=B_a$. If $h\ne0$, the largest exponent of $sh$ is $\deg h+2$;
therefore $h$ fits in the permitted transverse anchor interval
$0,\ldots,N-3$. For $N=2$ it must be zero. The stabilizer combination
$P(x^ah(T)(f,g))$ has first row $a$ with pair $(sh,h)$, and it is supported
only in rows $a,a+1,a+2$. Its first anchor coordinate $a$ lies in the allowed
range. Subtracting it removes row $a$ and leaves a cycle supported in
$a+1,\ldots,M-1$. Induction on the number $M-a$ of remaining rows terminates
at the zero vector.

## Splitting at two empty rows

Let rows $k,k+1$ vanish. Split the vector as $w=w_L+w_R$, where $w_L$ retains
only rows below $k$ and $w_R$ only rows above $k+1$. These sets are disjoint
and exhaust the possibly nonzero rows, so the equality holds coordinatewise.

Each Z check has first-coordinate support contained in three consecutive
rows $c-2,c-1,c$. It cannot meet both retained parts: such an intersection
would require two rows differing by at least three, while any two rows in
that check differ by at most two. Hence each check pairs with at most one
part, and its zero pairing with $w$ implies its zero pairing with both parts.
Thus both parts are cycles. The prefix has at most $k\le M-2$ rows, and the
suffix at most $M-k-2\le M-2$ rows. The two peeling arguments put both parts
in the X row space, which is closed under addition.

## Z-sector orientation and peeling

Reflect the physical board and exchange the two species, then describe the
result by columns instead of rows. Let $(A_i(T),B_i(T))$ denote these column
polynomials, with $0\le i<N$ and transverse degree at most $M-1$. A reflected
Z stabilizer synthesis with anchor polynomial sequence $(h_i)$ has components

\[
 A_i=h_i+t h_{i+2},\qquad
 B_i=h_{i+2}+s h_{i+1}+s h_i,
 \qquad t=T+T^2,\ s=T^2.
\]

This is obtained directly by exchanging the variables in $f,g$ after the
reflection: in the column direction their coefficients are $(t,0,1)$ for
$f$ and $(1,s,s)$ for $g$. The anchor index is shifted by two, so $h_i$
denotes the anchor at directional coordinate $i-2$. Reflection and species
exchange are coordinate permutations, so vanishing and weight are preserved.
The actual $H_X$-cycle equations in these coordinates are

\[
 tB_{i+2}=A_{i+2}+sA_{i+1}+sA_i+B_i
 \qquad(0\le i\le N-3).
\]

For a cycle supported in the first $r\le N-2$ columns, use $i=r-1$.
The last two physical columns are zero, and the equation gives
$B_{r-1}=sA_{r-1}$. Therefore $h=A_{r-1}$ has transverse support in
$0,\ldots,M-3$ (or is zero when $M=2$). A Z synthesis packet with only
$h_{r-1}=h$ nonzero has last column $r-1$ equal to $(h,sh)$ and has no
columns beyond it. It removes that column and affects only the preceding
two. This proves prefix exactness by induction.

For a cycle whose first potentially nonzero column is $a\ge2$, use $i=a-2$.
The preceding two columns vanish and the equation gives $A_a=tB_a$.
Thus $h=B_a$ has allowed transverse support. The synthesis packet with only
$h_{a+2}=h$ nonzero has first physical column $a$ equal to $(th,h)$ and
no earlier columns. It removes that column and affects only the next two.
This proves suffix exactness. The same diameter-two check-support argument
splits a cycle across two empty columns into these two exact parts.

## Consequence and remaining formal tasks

PROPOSITION: A nonboundary X cycle occupies at least one row from every
adjacent row pair. A nonboundary Z cycle occupies at least one column from
every adjacent column pair. These are direct contrapositives of the proved
paper statements. In particular the two sector weights are at least
$\lfloor M/2\rfloor$ and $\lfloor N/2\rfloor$, by using disjoint adjacent
pairs. The generic run-cost theorem developed separately strengthens these
to $M-2$ and $N-2$ for dimensions at least three.

Implementation obligations: finish capped replay of prefix/suffix peeling,
formalize the gap split and its physical-cycle preservation, transport the
Z directional view and packets, then connect physical weights to the generic
strip theorem. These are not assumed by the completed rank theorem.
