#set page(paper: "a4", margin: 22mm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.6em)
#set heading(numbering: none)
#let wt = math.op("wt")
#let supp = math.op("supp")
#let row = math.op("row")

#align(center)[
  #text(17pt, weight: "bold")[A column criterion for CSS distance at least three]
  #v(5pt)
  Standalone analytical draft · 11 November 2026
]

*Status: PROPOSITION throughout; independent mathematical review pending.*
The Lean module and guarded axiom audit passed in the coordinating capped
detached run, as recorded at the end. The arguments below are complete
proposed proofs for hand checking, not final mathematically reviewed proofs.
No concrete 722-code distance is asserted.

= PROPOSITION 1 — Main column criterion

Let $F=bb(F)_2={0,1}$, with addition and multiplication modulo two. Let $Q$ be
a finite set of physical coordinates and $R$ any set of check indices. Let
$H: R times Q -> F$ be a matrix and $B$ a linear subspace of $F^Q$.
For $i in Q$, define the unit vector $e_i$ by $e_i (i)=1$ and $e_i (q)=0$ for
$q != i$. Define the column $c_i in F^R$ and the syndrome $H x$ by
$ c_i (r)=H(r,i), quad (H x)(r)=sum_(q in Q) H(r,q)x(q). $
For $x in F^Q$, its support and Hamming weight are
$ supp(x)={q in Q : x(q) != 0}, quad wt(x)=|supp(x)|. $
Assume the following two hypotheses:

+ *No zero columns:* $c_i != 0$ for every $i in Q$.
+ *Trivial column collisions:* for every distinct $i,j in Q$, if $c_i=c_j$,
  then $e_i+e_j in B$.

Then
$ H x=0 " and " wt(x)<=2 quad ==> quad x in B. $
Consequently every $x$ with $H x=0$ and $x ∉ B$ satisfies $wt(x)>=3$.
No inclusion $B subset.eq ker H$ is needed for this implication. Such an
inclusion will hold in the CSS applications below.

*Proposed proof (PROPOSITION; review pending).* A vector over $F$ is exactly
the indicator of its support: at a supported coordinate its nonzero value
must be 1, and at every other coordinate it is 0. A finite set of cardinality
at most two is empty, a singleton, or a pair of distinct elements. This gives
the following exhaustive classification, with no enumeration of $Q$:

- If $supp(x)$ is empty, every coordinate is zero, so $x=0$.
- If $supp(x)={i}$, the indicator description gives $x=e_i$.
- If $supp(x)={i,j}$ with $i != j$, the indicator description gives
  $x=e_i+e_j$. At $i$ and $j$ exactly one summand is 1; elsewhere both are 0.

In the first case $x in B$ because a linear subspace contains zero. In the
second case, the definition of matrix multiplication gives $H e_i=c_i$;
thus $H x=0$ contradicts the first hypothesis. In the third case, linearity
gives $0=H x=c_i+c_j$. Adding $c_j$ to both sides and using $c_j+c_j=0$
gives $c_i=c_j$. The second hypothesis now puts $x=e_i+e_j$ in $B$.
This proves the first conclusion. If $H x=0$ and $x ∉ B$, a weight at
most two would contradict that conclusion. Weight is a natural number, so
it is at least three. This completes the proposed argument.

The statement allows repeated columns and dependent check rows. It requires
neither a positive-dimensional logical space nor an existing nontrivial cycle.
If there are no such cycles, the universal lower bound is vacuous.

#pagebreak()
= Definitions for the CSS specialization

Take finite check sets $R_X,R_Z$ and binary matrices
$H_X: R_X times Q -> F$ and $H_Z: R_Z times Q -> F$ satisfying
$ H_X H_Z^T=0. $
Here transpose interchanges row and column indices. This equation says that
every X-check row has zero dot product with every Z-check row, where
$u dot v=sum_(q in Q) u(q)v(q)$ in $F$.
Define the stabilizer subspaces and cycle spaces by
$ U=row(H_X), quad V=row(H_Z), $
$ C_X=ker H_Z, quad C_Z=ker H_X. $
The row space is the set of all binary linear combinations of rows; no row
independence is assumed. An X-sector nontrivial logical is an $x in C_X$
with $x ∉ U$. A Z-sector nontrivial logical is a $z in C_Z$ with
$z ∉ V$. Thus the X sector uses the Z-check syndrome, and conversely.

= PROPOSITION 2 — CSS sector corollaries

For the X-sector bound, assume:

+ Every column of $H_Z$ is nonzero.
+ Whenever distinct columns $i,j$ of $H_Z$ are equal, $e_i+e_j in U$.

Then every nontrivial X-sector logical has Hamming weight at least three.
For the Z-sector bound, assume:

+ Every column of $H_X$ is nonzero.
+ Whenever distinct columns $i,j$ of $H_X$ are equal, $e_i+e_j in V$.

Then every nontrivial Z-sector logical has Hamming weight at least three.
Either conclusion requires only its own two column hypotheses. If both sets
of hypotheses hold, both conclusions hold simultaneously.

*Proposed proof (PROPOSITION; review pending).* First, commutation makes the
stabilizer spaces subspaces of the corresponding cycle spaces. Indeed,
if $u=sum_(r in R_X) a_r H_X (r, dot)$, then for every $s in R_Z$,
$ (H_Z u)(s)=sum_(r in R_X) a_r
    (sum_(q in Q) H_Z (s,q) H_X (r,q))=0. $
The inner sum is an entry of $H_X H_Z^T$, using commutativity of multiplication
in $F$. Hence $U subset.eq C_X$. Likewise, for
$v=sum_(s in R_Z) b_s H_Z (s,dot)$, each coordinate of $H_X v$ is a linear
combination of entries of $H_X H_Z^T$, so $V subset.eq C_Z$.

Now apply Proposition 1 with $(H,B)=(H_Z,U)$. Its hypotheses are precisely
the two X-sector hypotheses. For $x in C_X$ outside $U$ it gives
$wt(x)>=3$. Apply it with $(H,B)=(H_X,V)$ for the Z sector. This proves
both claimed bounds.

*Distance convention.* If the set $C_X without U$ is nonempty, define $d_X$ as
the minimum Hamming weight of its elements, and similarly define $d_Z$
when $C_Z without V$ is nonempty. The preceding universal statements then give
$d_X>=3$ and $d_Z>=3$ whenever the respective minimum exists. No numerical
value is assigned here to an empty minimum. In particular the corollary does
not assert that a code encodes a logical qubit or that its distance equals three.

#pagebreak()
= Definitions for mixed Pauli operators

On one qubit, use the matrices
$ I=mat(1,0;0,1), quad X=mat(0,1;1,0), quad Z=mat(1,0;0,-1). $
A Pauli operator on $Q$ is, up to a scalar phase in $\{1,-1,upright(i),-upright(i)\}$,
specified by a pair $(x,z) in F^Q times F^Q$: at coordinate $q$ its operator
is $X^(x(q)) Z^(z(q))$. Tensor products over all coordinates give the full
operator. The pair $(0,0)$ is identity at that coordinate; $(1,0)$, $(0,1)$,
and $(1,1)$ are its three nonidentity possibilities up to phase. Define
$ wt_P (x,z)=|supp(x) union supp(z)|. $
Global phase does not change the pair or this weight. In particular
$ wt_P (x,z)>=wt(x), quad wt_P (x,z)>=wt(z). $
These inequalities follow from the two inclusions into the union and
monotonicity of finite-set cardinality.

For the CSS matrices of Proposition 2, let $S$ be the group generated by
the pure-X check operators $(H_X (r,dot),0)$ and pure-Z check operators
$(0,H_Z (s,dot))$, with their standard phase-one representatives.
A nontrivial Pauli logical means an operator commuting with every element
of $S$ whose operator pair is not the pair of any element of $S$.
Thus a scalar multiple of a stabilizer is excluded, including a phase-only
operator. This is the convention needed for code distance.

= PROPOSITION 3 — Mixed-Pauli corollary

Under both sets of column hypotheses in Proposition 2, every nontrivial
Pauli logical for $S$ has Pauli weight at least three.

*Proposed proof (PROPOSITION; review pending).* Direct multiplication gives
$X^2=Z^2=I$ and $Z X=-X Z$. Operators on different coordinates commute.
Consequently the commutation sign between pairs $(x,z)$ and $(u,v)$ is
$ (-1)^(x dot v+z dot u). $
Indeed, moving every X factor through the other operator's Z factors
introduces exactly one minus sign for each common coordinate with both
bits 1; all exponents are summed modulo two. Products of Pauli pairs add
their two binary components, regardless of the resulting scalar phase.

The CSS equation therefore makes all the check generators commute. A pair
$(x,z)$ commutes with every X generator exactly when $H_X z=0$, and with
every Z generator exactly when $H_Z x=0$. Commuting with generators is
equivalent to commuting with the generated group: commutation is preserved
under products and inverses. Thus a Pauli logical has $x in C_X$, $z in C_Z$.

The set of operator pairs of $S$ is exactly $U times V$. One inclusion
follows by adding the pairs of the generators in a product. For the reverse
inclusion, express $u in U$ as a sum of X rows and $v in V$ as a sum of Z
rows, and multiply the selected generators; the resulting pair is $(u,v)$.
Global phases do not affect this statement. In fact these commuting
generators define a valid stabilizer group: reorder each product with all
X generators first, giving the phase-one representative $X^u Z^v$; if its
pair is zero, this representative is $I$, so $-I$ is not generated.

Nontriviality therefore means $x ∉ U$ or $z ∉ V$. In the first
case Proposition 2 gives $wt(x)>=3$, so $wt_P (x,z)>=3$. In the second
case it gives $wt(z)>=3$ and the same conclusion. This proves the corollary
without assuming that the logical is purely X or purely Z.

#pagebreak()
= Explicit hypotheses for a possible 722 adapter

This section specifies an application interface only. It does not establish
that any submitted or reconstructed 722-qubit matrices meet that interface.
In particular the symbolic column classification in another draft is not
silently taken as a proved premise here.

Take $Q=\{0,dots,721\}$ and name its qubits
$ A(i,j)=19i+j, quad B(i,j)=361+19i+j quad (0<=i,j<=18). $
Suppose a CSS code has matrices $H_X,H_Z$, each with 357 rows, and has
the following verified properties:

+ *Input identification and commutation.* The matrices are identified with
  the intended literal input on these physical coordinates, and
  $H_X H_Z^T=0$. X rows are labeled $X_(c,d)$ with
  $-2<=c<=18$, $0<=d<=16$; Z rows are labeled $Z_(c,d)$ with
  $2<=c<=18$, $0<=d<=20$. The labels must refer to actual rows of the
  recognized matrices, not to a different board or boundary convention.
+ *Nonzero Z-check columns.* Every column of $H_Z$ is nonzero.
+ *Complete Z-check collision classification.* If distinct columns of
  $H_Z$ are equal, their qubits, in either order, are
  $A(18,j),B(18,j-2)$ for some integer $2<=j<=18$.
+ *X stabilizer witnesses.* For every such $j$, the actual row
  $X_(18,j-2)$ is $e_(A(18,j))+e_(B(18,j-2))$.
+ *Nonzero X-check columns.* Every column of $H_X$ is nonzero.
+ *Complete X-check collision classification.* If distinct columns of
  $H_X$ are equal, their qubits, in either order, are
  $A(i,18),B(i+2,18)$ for some integer $0<=i<=16$.
+ *Z stabilizer witnesses.* For every such $i$, the actual row
  $Z_(i+2,20)$ is $e_(A(i,18))+e_(B(i+2,18))$.

*PROPOSITION 4 (conditional adapter; review pending).* If all these
hypotheses hold, the universal X-sector, Z-sector, and mixed-Pauli lower
bounds of three hold for that recognized code.

*Proposed proof (PROPOSITION; review pending).* For any Z-check column
collision, the classification and X witness put the two-site vector in
$row(H_X)$: an individual row is a linear combination of rows with its
own coefficient 1 and all others 0. Exchanging the two sites does not change
their sum. The same argument with the X-check classification and Z witness
puts each X-check collision in $row(H_Z)$. Together with the nonzero-column
hypotheses these are exactly both instances of Proposition 2. Apply
Propositions 2 and 3. This implication does not discharge any of its premises.

= Formalization correspondence and review boundary

The companion draft is `lean/QldpcVerification/Planar/SmallSupport.lean`.
Its `support` and `card_support` use physical support and Mathlib's
`hammingNorm`; `classify_weight_le_two` uses `Finset.card_eq_one` and
`Finset.card_eq_two`. The generic conclusions are `small_cycle_mem` and
`weight_ge_three`. The two hypotheses are packaged as `ColumnCriterion`.
The project CSS corollaries are `x_lower` and `z_lower`, using
`Input.CSSCode.IsXLogical`, `IsZLogical`, `xStab`, and `zStab`.
The theorem `pauli_lower` transfers through the project's homological
identification and QECLean's `chainWeight_lower_bound_transfers`.

The separate file `lean/QldpcVerification/PlanarSmallSupportAudit.lean`
contains guarded axiom checks. These filenames identify draft interfaces,
not substitutes for mathematical review. The coordinating run reported that
both the module and guarded audit passed in the capped detached allocation
`small-v2` (3.841 s and 2.807 s; reported process peak 3,774,580 KiB).
This is a reported formal check, not an independent mathematical review.
The actual 722 adapter remains separate and unproved in this document.
No support-search certificate, numerical distance estimate, rank computation,
or assertion of distance twenty is a premise of this note.
