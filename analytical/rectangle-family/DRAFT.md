# Eight logical qubits on every open rectangle

**Grade: PROPOSITION.** The proof below is complete on paper. The remaining acceptance
obligations are successful Lean replay, guarded axiom audit, three independent hostile
reviews, and the author's final adversarial rereading. No distance bound is asserted here.

## Main theorem

Let `m,n` be arbitrary nonnegative integers. The binary matrices defined below have
`2(m+2)(n+2)` columns and satisfy

\[
 H_XH_Z^{\mathsf T}=0,\qquad
 \operatorname{rank} H_X=(m+4)n,\qquad
 \operatorname{rank} H_Z=m(n+4).
\]

If `S_X` and `S_Z` are their row spaces, then

\[
 \dim_{\mathbb F_2}(S_Z^\perp/S_X)=8.
\]

Consequently the associated CSS code has eight encoded qubits for every pair of side
lengths `M=m+2≥2`, `N=n+2≥2`. Its separate ranks are `(M+2)(N−2)` and
`(M−2)(N+2)`. The statement includes rectangles with a side of length two and the
`2×2` rectangle, where both row sets are empty.

## Definitions

The field `F=𝔽₂` consists of `0,1`, with addition and multiplication modulo two.
In particular `a+a=0` for every `a∈F`. Every vector space in this document is over `F`.
A finite vector's coordinates form a finite index set; its dot product with another
vector is the sum of their coordinatewise products in `F`.

A finite Laurent polynomial in `x,y` is an expression
`p=∑ pᵢⱼxⁱyʲ` with integer exponents and only finitely many nonzero coefficients.
Equality and addition are coefficientwise. Multiplication is defined by convolution:
the coefficient at `(r,s)` of `pq` is
`∑_{i+k=r,j+l=s} pᵢⱼqₖₗ`. All these sums are finite. Ordinary polynomials have only
nonnegative exponents. A nonzero coefficient is one. The support is the set of its
nonzero coefficient indices. Write `p̄(x,y)=p(x⁻¹,y⁻¹)`.

The board is

\[
 Q=\{0,1,\ldots,m+1\}\times\{0,1,\ldots,n+1\}.
\]

There are two species `A,B` of coordinates at every board cell. Thus the vector space
`V` has dimension `2(m+2)(n+2)`. Write a vector as a pair `(u,v)` of polynomials supported
on `Q`, with the first polynomial representing species A and the second species B.
Let `P` delete every coefficient outside `Q`, separately in each component.

Put

\[
 f=x+x^2+y^2,\qquad g=1+x^2y+x^2y^2.
\]

The X-anchor and Z-anchor sets are

\[
\begin{aligned}
 I_X&=\{-2,-1,\ldots,m+1\}\times\{0,1,\ldots,n-1\},\\
 I_Z&=\{2,3,\ldots,m+1\}\times\{0,1,\ldots,n+3\}.
\end{aligned}
\]

A set of consecutive integers with lower endpoint greater than its upper endpoint
is empty. The matrix rows are

\[
 H_X[(a,b),:]=P\bigl(x^ay^b(f,g)\bigr),\qquad
 H_Z[(c,d),:]=P\bigl(x^cy^d(\bar g,\bar f)\bigr).
\]

The row space of a matrix is the space of all linear combinations of its rows, and
its rank is the dimension of that space. Put `S_X=rowspan(H_X)` and
`S_Z=rowspan(H_Z)`. For a subspace `S⊆V`, its orthogonal subspace is
`S^⊥={w∈V : s·w=0 for every s∈S}`. The quotient `S_Z^⊥/S_X`, once `S_X⊆S_Z^⊥`
is established, is the space of cosets `w+S_X` for `w∈S_Z^⊥`. For these binary CSS
matrices we use “number of encoded qubits” to mean the dimension of this quotient.

## Polynomial facts

**Lemma 1.** A product of two nonzero univariate polynomials over `F` is nonzero.
The same statement holds for finite Laurent polynomials in one variable. If a
nonzero factor multiplies an unknown polynomial to zero, the unknown is zero.

**Proof.** Let `r` and `s` be the largest exponents with nonzero coefficients in
the two nonzero factors. Every exponent in the first factor is at most `r` and
every exponent in the second is at most `s`. A pair of such exponents adds to
`r+s` only when they are `r,s`: if the first were less than `r`, the second would
have to exceed `s`; if the second were less than `s`, the first would have to
exceed `r`. Consequently the coefficient of the product at `r+s` is the product
of those two nonzero coefficients, hence one. Thus the product is nonzero.
Finite Laurent supports also have largest exponents, so that proof applies to
them. The final assertion follows by contradiction if the unknown is nonzero. ∎

**Lemma 2.** In `F[T]`, put `t=T+T²` and `b=1+T²t=1+T³+T⁴`. Then

\[
 b^2+t=1+T+T^2+T^6+T^8\ne0,
 \qquad b^2+T^4t=1+T^5+T^8\ne0.
\]

**Proof.** Expanding `(1+T³+T⁴)²` gives `1+T⁶+T⁸`: every cross term occurs
twice and vanishes in `F`. Adding `t` gives the first displayed polynomial.
Since `T⁴t=T⁵+T⁶`, adding it to `1+T⁶+T⁸` cancels the two `T⁶` terms and gives
the second. Both have constant coefficient one, so neither is the zero
polynomial. Also `t≠0`, because its coefficient at exponent one is one. ∎

## Commutation on the finite board

**Lemma 3.** Every X row is orthogonal to every Z row.

**Proof.** Choose an allowed X anchor `(a,b)` and Z anchor `(c,d)`. Before
projection to the board, an A-species overlap pairs an exponent `s` of `f` with
an exponent `t` of `g` satisfying

\[
 (a,b)+s=(c,d)-t,
 \quad\hbox{equivalently}\quad s+t=(c-a,d-b).
\]

The parity of the A overlap is therefore the coefficient of `fg` at
`(c-a,d-b)`. The B overlap is the coefficient of `gf` at the same exponent:
its pairs are an exponent of `g` and one of `f`. Exchanging the two exponents
is a bijection between the two finite sets of pairs, so these coefficients
are equal. Their sum is zero in `F`.

It remains to show that projection to `Q` deletes no overlap. Every exponent of
`f` and of `g` has both coordinates in `{0,1,2}`. A point in an unprojected X
row has second coordinate between `b` and `b+2`, hence between `0` and `n+1`,
because `0≤b≤n−1`. A point in an unprojected Z row has first coordinate between
`c−2` and `c`, hence between `0` and `m+1`, because `2≤c≤m+1`. A common point
belongs to both rows, so it satisfies both coordinate bounds and belongs to
`Q`. Thus projection preserves both overlaps and their sum zero. If either
anchor set is empty, the universal orthogonality assertion has no pair of
rows to check. These cases exhaust all `m,n≥0`: the preceding argument applies
whenever the two selected anchors exist. ∎

Each entry of `H_XH_Zᵀ` is the dot product of its selected X and Z rows. Lemma 3
therefore proves `H_XH_Zᵀ=0`.

## Independence of every X row

**Lemma 4.** The X rows are linearly independent.

**Proof.** If `n=0`, the X-anchor set is empty. Its only linear combination is
the empty sum, so the empty family is independent. Now suppose `n≥1`.
An arbitrary linear combination of X rows has an anchor polynomial

\[
 h(x,y)=\sum_{i=-2}^{m+1} h_i(y)x^i,
 \qquad \operatorname{supp}(h_i)\subseteq\{0,\ldots,n-1\}.
\]

Its physical vector is `P(fh,gh)`. Suppose this vector is zero. No coefficient
of either product has second coordinate outside `{0,…,n+1}`, since every
second exponent of `h` lies between `0,n−1` and every second exponent of
`f,g` between `0,2`. Thus for every retained first coordinate `i=0,…,m+1`,
vanishing of all physical coefficients in that slice is exactly vanishing
of these two ordinary polynomials in `y`:

\[
 h_{i-2}+h_{i-1}+y^2h_i=0,
 \qquad t h_{i-2}+h_i=0,
 \qquad t=y+y^2.                       \tag{1}
\]

The second equation gives `h_i=t h_{i−2}`. Substitution in the first gives
`h_{i−1}=b h_{i−2}`, where `b=1+y²t`. Since `m≥0`, the retained indices include
both `0` and `1`. Applying the substituted equation at those two indices gives
`h_{−1}=b h_{−2}` and `h_0=b h_{−1}=b²h_{−2}`. The second equation in (1) at
`i=0` also gives `h_0=t h_{−2}`. Hence `(b²+t)h_{−2}=0`.
By Lemma 2 the first factor is nonzero, so Lemma 1 gives `h_{−2}=0`. It follows
that `h_{−1}=0`.

We prove `h_i=0` for the remaining indices `i=0,…,m+1` by increasing-index
induction using `h_i=t h_{i−2}`. For `i=0`, the right-hand factor is `h_{−2}=0`;
for `i=1`, it is `h_{−1}=0`. For each `i≥2`, the index `i−2` belongs to
`{0,…,i−1}` and its slice has already vanished. Thus the equation gives zero
in every case. The two initial slices and these remaining slices exhaust
`{-2,…,m+1}`. All coefficients of `h` vanish, which says that all coefficients
in the original row combination vanish. ∎

There are `(m+4)n` X anchors. Independence makes the rows a basis of their row
space, so their rank is `(m+4)n`.

## Independence of every Z row

**Lemma 5.** The Z rows are linearly independent.

**Proof.** If `m=0`, there are no Z anchors and the empty family is independent.
Suppose `m≥1`. Reflect physical cells by

\[
 (i,j)\longmapsto(m+1-i,n+1-j)
\]

and exchange species A and B. Reflection maps `Q` bijectively to itself and is
its own inverse; the exchange has the same two properties. Their combination
is therefore a coordinate permutation and maps zero vectors exactly to zero
vectors. An exponent `(c,d)−s` of a Z row is taken to
`(m+1−c,n+1−d)+s`. Exchanging the species consequently maps that row to

\[
 P\bigl(x^{m+1-c}y^{n+1-d}(f,g)\bigr).
\]

The transformed first anchor coordinate ranges over `{0,…,m−1}`. The
transformed second anchor coordinate ranges over `{-2,…,n+1}`. Both ranges
are bijective images of their original anchor-coordinate ranges.

A vanishing Z row combination therefore becomes `P(fh,gh)=0` with

\[
 h(x,y)=\sum_{j=-2}^{n+1}h_j(x)y^j,
 \qquad \operatorname{supp}(h_j)\subseteq\{0,\ldots,m-1\}.
\]

No first-coordinate truncation occurs in `fh` or `gh`, since the first
exponents lie between `0` and `(m−1)+2=m+1`. At each retained second coordinate
`j=0,…,n+1`, the zero physical slices are exactly

\[
 h_{j-2}+t h_j=0,
 \qquad h_j+x^2h_{j-1}+x^2h_{j-2}=0,
 \qquad t=x+x^2.                       \tag{2}
\]

Substituting the first equation into the second gives
`x²h_{j−1}=b h_j`, where `b=1+x²t`. Because `n≥0`, indices `0` and `1` occur.
The substituted equations at these indices yield

\[
 x^2h_{-1}=b h_0,
 \qquad x^2h_0=b h_1,
 \qquad x^4h_{-1}=b^2h_1.
\]

The first equation of (2) at `j=1` gives `h_{−1}=t h_1`, so
`(b²+x⁴t)h_1=0`. Lemmas 2 and 1 give `h_1=0`. Then `x²h_0=b h_1=0` implies
`h_0=0`, because `x²` is nonzero. The first equations of (2) at `j=0,1` give
`h_{−2}=h_{−1}=0`.

For every remaining index `j=2,…,n+1`, increasing-index induction applies to
`t h_j=h_{j−2}`. The smaller slice has vanished; since `t≠0` by Lemma 2,
Lemma 1 gives `h_j=0`. The initial indices `−2,−1,0,1` and these remaining
indices exhaust the transformed anchor range. Every anchor coefficient is
zero. Since the coordinate transformation and the anchor reindexing were
bijections, every coefficient of the original Z row combination is zero. ∎

There are `m(n+4)` Z anchors, so the Z rank is `m(n+4)`.

## Dimension of the logical quotient

We give the finite-dimensional linear algebra argument explicitly.

**Lemma 6.** Let `T:U→W` be a linear map between finite-dimensional vector
spaces. Then `dim U=dim ker T+dim im T`. If `B⊆U` is a subspace, then
`dim(U/B)=dim U−dim B`.

**Proof.** Choose a basis `e₁,…,e_r` of `ker T` and extend it to a basis
`e₁,…,e_r,v₁,…,v_s` of `U`. Such an extension is constructed by repeatedly
adjoining a vector outside the span of the current list. Each addition
increases the number of independent vectors by one; this process must stop
within `dim U` steps. At termination the list spans `U` and is independent.

The vectors `Tv₁,…,Tv_s` span `im T`: expand any `u∈U` in the displayed basis
and apply `T`, which kills every `e_i`. They are independent: a linear
combination `∑ a_iTv_i=0` means `∑ a_iv_i∈ker T`, hence expresses this
combination as a combination of the `e_i`. Independence of the extended basis
forces every `a_i=0`. Thus `dim im T=s` and `dim U=r+s`.

For the quotient assertion, choose a basis of `B` and extend it to a basis of
`U` by the same construction. The cosets of the added vectors span `U/B`,
because the original basis vectors lie in `B` and hence have zero coset.
A linear combination of the added cosets vanishes exactly when that
combination of added vectors belongs to `B`; independence of the extended
basis forces every coefficient to vanish. These cosets are a basis of
`U/B`, proving the asserted dimension. ∎

**Lemma 7.** If independent vectors `s₁,…,s_r` lie in `F^D`, then the map
`T:F^D→F^r` given by `Tw=(s₁·w,…,s_r·w)` is onto.

**Proof.** Suppose its image were proper. Choose a basis of the image and
extend it to a basis of `F^r`. At least one vector is added. Assign value one
to the first added vector and zero to every other vector of this extended
basis. Extending by linearity gives a nonzero linear functional `ℓ:F^r→F`
that vanishes on the image. If `u₁,…,u_r` are the standard coordinate vectors
of `F^r` and `a_i=ℓ(u_i)`, every vector `z` has expansion `∑z_iu_i`, so
`ℓ(z)=∑a_iz_i`. At least one `a_i` is nonzero, because `ℓ` is nonzero.
For every `w`, the identity `ℓ(Tw)=0` gives
`(∑a_is_i)·w=0`. Testing successively on every standard coordinate vector of
`F^D` shows that every coordinate of `∑a_is_i` is zero. This contradicts the
independence of the `s_i`. Therefore the image is all of `F^r`. If `r=0`, the
target is the zero vector space and the map is onto by its definition, so the
statement covers that case as well. ∎

By Lemma 3 every X row is orthogonal to every Z row. Bilinearity of the dot
product gives `S_X⊆S_Z^⊥`, so the quotient in the main theorem exists.
Apply Lemma 7 to the independent Z rows. The corresponding map is precisely
`T(w)=H_Zw`; its kernel is `S_Z^⊥`, and its image has dimension `m(n+4)`.
Lemma 6 therefore gives

\[
 \dim S_Z^\perp=2(m+2)(n+2)-m(n+4).
\]

The X rows are independent, so `dim S_X=(m+4)n`. Apply the quotient part of
Lemma 6 inside `S_Z^⊥` to obtain

\[
\begin{aligned}
 \dim(S_Z^\perp/S_X)
 &=2(m+2)(n+2)-m(n+4)-(m+4)n\\
 &=(2mn+4m+4n+8)-(mn+4m)-(mn+4n)\\
 &=8.
\end{aligned}
\]

Every subtraction here subtracts the dimension of a subspace or an image
from that of its ambient space, so no negative dimension is introduced.
For `m=n=0`, the formula gives `V=F⁸`, `S_X=S_Z={0}`, and
`S_Z^⊥/S_X=F⁸`. For `m=0,n>0`, only the Z rows are absent; Lemma 4 and the
same quotient argument apply. For `n=0,m>0`, only the X rows are absent;
Lemma 5 and the same quotient argument apply. Together with `m>0,n>0`, these
four mutually exclusive cases exhaust all nonnegative `m,n`. This proves
the main theorem.

## Lean correspondence

The module `lean/QldpcVerification/Planar/RectangleFamily.lean` uses
`Cell m n=Fin(m+2)×Fin(n+2)` and `Q m n=Bool×Cell m n`. The Boolean value
`false` denotes species A and `true` species B. `XAnchor` stores an anchor's
first coordinate shifted upward by two; `ZAnchor` stores its first coordinate
shifted downward by two. The definitions `HX` and `HZ` are exactly the rows
in this document.

The declarations `xSynthesis_eq` and `zSynthesis_eq` identify the generic
polynomial recurrence maps with these matrices' transposed multiplication
maps. Their injectivity is proved for arbitrary dimensions by the existing
`Planar.BoundaryRecurrence` domain and polynomial lemmas; no matrix-rank
certificate is an assumption. `parameters` states the matrix ranks,
commutation, and dimension of the actual logical quotient. `code_parameters`
provides the same ranks and encoded dimension for `Input.CSSCode`, the
project's QECLean-backed CSS interface. `RectangleFamilyAudit.lean` guards the
axioms of these capstones.

## Attribution and scope

This is a family-level analytic formalization of an established construction.
The same polynomials, open rectangular family `[[2L_xL_y,8,d(L_x,L_y)]]`, and
fixed logical dimension eight appear in Liang, Eberhardt, and Chen,
*Planar quantum low-density parity-check codes with open boundaries*,
[arXiv:2504.08887v4](https://arxiv.org/html/2504.08887v4), Figure 1 caption and
Section II. That caption reports distances computed by integer programming.
The present proof uses no such computation and asserts no distance value.
The mathematical proof above is self-contained; this citation identifies
prior work and is not a substitute for any step.
