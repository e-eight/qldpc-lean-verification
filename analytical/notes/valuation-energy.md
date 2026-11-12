# Valuation energy for the width-19 rectangle

Date: 2026-11-11. Independent analytical note. All results below marked
**PROPOSITION** are pending independent review and formalization; none is
advertised as a kernel proof. **CONJECTURE** means unproved. **FALSE** labels
a statement with an explicit counterexample.

Outcome: a two-injection cancellation classification for **mixed physical
blocks**, a binary-digit valuation/weight inequality, and a precise obstruction
to extending them to distance 20. This does **not** close distance 20.
There is no zero-gap counting argument here.

## Model and charge interface

Source: `analytical/rectangle722-distance17/PROOF.tex`, explicit model and
complete charges, especially Sections 1, 6, 7 and the exact recurrences.
Source SHA256 at reading:
`6dcccb32f1b11e0c2eae81ace1e94c0f995971daeac73b39a66f2b09bff80cab`.

**PROPOSITION (model transcription; pending review/formalization).** Work over
F₂. Physical pairs `(u,v)` have exponents in `[0,18]²`, and physical weight
counts coefficients in both blocks separately. Put

```
f = x+x²+y²,   g = 1+x²(y+y²),   sigma = gu+fv.
```

For X cycles, syndrome rows 2 through 18 vanish, as whole polynomials, including
column coefficients 19 and 20. Write the physical rows as `(a_i,b_i)` in `T=y`.
For reflected Z cycles, syndrome columns 2 through 18 vanish; use physical
columns `(a_i,b_i)` in `T=x`. The respective equations are

```
F: a_i = t a_(i-2)+b_(i-1)+b_(i-2)+T²b_i,
B: t b_i = a_i+T²a_(i-1)+T²a_(i-2)+b_(i-2),
t = T(1+T),                         2 <= i <= 18.
```

Every physical slice polynomial has degree at most 18. No equation is reduced
modulo `T^19`. The complete X charge is the low-row syndrome evaluated at
`(X,y)` in `F₂[y]/(1+y+y²+y⁶+y⁸)`. The complete reflected Z charge is the
low-column syndrome in the same algebra; using its x basis, its modulus is
`1+x⁵+x⁸`. Vanishing charge is equivalent to being a stabilizer, as proved
in the source. Reflection exchanges physical blocks and reverses coordinates;
it is not an assumed X/Z symmetry. Proof of this transcription: coefficient
extraction from the displayed `f,g` and the two charge constructions in the
source.

## A shared exact transport equation

**PROPOSITION 1 (pending review/formalization).** Define `B=1+T³+T⁴`.
Both directions have the following canonical form:

```
c_i = t c_(i-2) + lambda h_(i-1) + B h_(i-2),       2 <= i <= 18.
```

For F, `c_i=a_i+T²b_i`, `h_i=b_i`, `lambda=1`. For B, reverse the
index first: `c_i=T²a_(18-i)+b_(18-i)`, `h_i=a_(18-i)`, `lambda=T²`.
In either direction the physical slice, up to block order, is
`(c_i+T²h_i,h_i)`. Thus

```
deg h_i <= 18,  deg(c_i+T²h_i) <= 18,  deg c_i <= 20,
w_i = wt(c_i+T²h_i)+wt(h_i).
```

Proof. Substitute `a=c+T²b` in F. In B first solve
`c_(j-2)=t c_j+B a_j+T²a_(j-1)`, then put `i=20-j`.
These substitutions also prove the degree and weight assertions. Notice the
degree cap 20 on `c`, rather than 18: conflating them would give a false bound.

## Three places, binary multiplicity, and width

For nonzero `P`, write `alpha=ord_0(P)`, `beta=ord_1(P)` and `d=deg P`.
Define coefficient span `s=d-alpha` (the inclusive width is `s+1`).
Let `pop(m)` be the number of 1 bits in the nonnegative integer `m`.

**PROPOSITION 2 (pending review/formalization).** For every nonzero P,

```
alpha+beta <= d,             wt(P) >= 2^pop(beta),
(alpha,beta,d,s)(t^k P) = (alpha+k,beta+k,d+2k,s+k).
```

In particular, if an exact physical block propagates as `t^k P`, then
`d+2k<=18`. For a canonical `c` block the necessary cap is `d+2k<=20`.
These are degree and coefficient-width bounds, not weight-growth assertions.

Proof. The relatively prime factors `T^alpha` and `(1+T)^beta` divide P;
degrees give the first inequality. Multiplication adds the two valuations and
degree, proving the last formula. For the weight bound use induction on degree
and write `P=E(T²)+T O(T²)`. Then `wt(P)=wt(E)+wt(O)` and, with `T=1+U`,

```
P(1+U) = (E+O)(1+U²) + U O(1+U²).
```

If `beta=2m`, the even part has order `2m` and the odd part has larger
order. Consequently `ord_1(E+O)=m`, so
`wt(P)>=wt(E+O)>=2^pop(m)=2^pop(beta)`.
If `beta=2m+1`, then `ord_1(O)=m` and `ord_1(E+O)>=m+1`
(allowing `E+O=0`). Hence `ord_1(E)=m` also, and induction gives
`wt(P)>=2*2^pop(m)=2^pop(beta)`. Constants start the induction.

**PROPOSITION 3 (packet energy; pending review/formalization).** On any
distinct slices where the exact canonical values are `c_(r+2j)=t^j P`,
`0<=j<=k`, irrespective of how those values were produced,

```
sum_(j=0)^k w_(r+2j) >= sum_(j=0)^k 2^pop(beta+j),
deg P+2k <= 20.
```

If all their `h` values vanish, replace 20 by 18. Proof: the triangle
inequality gives `w_i>=wt(c_i)`, and Proposition 2 applies separately to
each disjoint slice. For example a constant packet on ten successive
same-parity slices costs at least
`1+2+2+4+2+4+4+8+2+4=33`. This is a conditional packet bound; arbitrary
mixed-block cycles need not contain such a packet.

## Exact physical cost of cancelling a packet

**PROPOSITION 4 (overlap accounting; pending review/formalization).** At each
slice let `I=|supp(c) intersect supp(T²h)|`. Then

```
w = wt(c)+2(wt(h)-I).
```

Moreover coefficients 19 and 20 of `c` must equal coefficients 17 and 18
of `h`, respectively. Proof: use the symmetric-difference formula for the
support of `c+T²h`, then the degree-18 constraint on that physical block.
Thus cancellation of a transported coefficient can cost no *extra* weight
at the current slice: an h coefficient already matched inside c has zero
increment in this formula. Its delayed contribution in the transport equation
must be accounted for instead.

**PROPOSITION 5 (two-injection annihilator; pending review/formalization).**
This is an exact local mixed-block mechanism, without singleton hypotheses.
Take `1<=r<=15`, so the next three canonical equations are tested. Suppose

```
c_(r-1)=h_(r-1)=0,   c_r=P,
h_r=H,  h_(r+1)=K,  h_(r+2)=h_(r+3)=0,
c_(r+2)=c_(r+3)=0.
```

The initial value P is supplied by the earlier history; no equation before
`r+1` is replaced by a boundary condition. Define

```
D = B²+t lambda²
  = 1+T+T²+T⁶+T⁸      (F),
  = 1+T⁵+T⁸           (reversed B).
```

Then necessarily, for a polynomial S,

```
P=D S,       H=B t S,       K=lambda t² S,
c_(r+1)=lambda B t S.
```

Conversely these expressions satisfy all three local equations and the
annihilation conditions. The two physical slices, in canonical block order,
are exactly

```
r:   ((B+t lambda²)S, B t S),
r+1: (lambda t S,    lambda t² S).
```

For nonzero S, width 19 requires and suffices for these two slices that
`deg S<=12`. Put `m=ord_1(S)`. Their **physical**, not canonical, weight obeys

```
w_r+w_(r+1)
 = wt((B+t lambda²)S)+wt(BtS)+wt(lambda t S)+wt(lambda t² S)
 >= 2^pop(m)+2*2^pop(m+1)+2^pop(m+2).                 (E)
```

Proof. The three recurrence equations give

```
c_(r+1)=lambda H,
tP+BH+lambda K=0,
t lambda H+BK=0.
```

Multiply the middle equation by B and add lambda times the last:
`D H=BtP`. Since `B(0)=B(1)=D(0)=D(1)=1`, both B and D are coprime
to t. Also `gcd(D,B)=gcd(t lambda²,B)=1`, since B is coprime to T.
Thus `gcd(D,Bt)=1`. A Bezout identity from polynomial division implies
`D|P`. Substitute `P=DS`, cancel D, then cancel B in the last equation,
to obtain the formulas. Conversely substitute them directly. The physical
formulas use `B+T²t=1`. The maximum degree of their four fixed multipliers
is six in both directions, with nonzero leading coefficients, proving the
degree cap. Their orders at 1 are respectively `0,1,1,2`; apply Proposition 2
to prove (E). No cancellation is hidden between physical blocks.

The corresponding orders at 0 are `0,1,e+1,e+2`, where
`e=0` for F and `e=2` for reversed B; multiplication by S adds `ord_0(S)`.
Their multiplier degrees are `(4,6,2,4)` for F and `(6,6,4,6)` for
reversed B. These give the simultaneous 0/1/infinity constraints explicitly.

Interpretation: a pure incoming canonical packet cannot be erased in two
mixed slices unless it contains the **degree-eight charge modulus itself**.
The annihilator has order zero at both 0 and 1. This identifies information
that an argument retaining only those two valuations would lose.

The local example `S=1` costs exactly 13 in both directions and satisfies
the width bound. It is a local transfer example, not an asserted global
nontrivial logical. For an interior feed with `h_(r-2)=0`, the equation at r
also requires `t|P`, hence `t|S`; S=1 does not meet that additional condition.

**PROPOSITION 6 (weight-19 mixed cycles with zero charge; pending
review/formalization).** The interior-feed condition is realized explicitly
by the following full 19-slice canonical history, in either direction:

```
c_0=D,  c_2=tD,  c_3=lambda B t²,
h_2=B t²,       h_3=lambda t³,
all other c_i,h_i zero.
```

Its physical weight is exactly 19, both physical blocks occur, and its charge
is zero. This is an example of an allowed stabilizer, not a distance
counterexample. Proof: equation 2 reads `c_2=t c_0`, equation 3 reads
`c_3=lambda h_2`, and equations 4 and 5 are Proposition 5 with `r=2,S=t`.
All later equations vanish termwise. The physical block degrees are at most
8. In F the slice weights at indices `0,2,3` are `(5,8,6)`; in reversed B
they are `(3,10,6)`. Expansion of the four multipliers in Proposition 5
gives these counts. For F the low syndrome is exactly D, whose charge is
zero. For reversed B, occupied canonical indices 0,2,3 correspond to
reflected physical columns 18,16,15, so the low-column syndrome is zero.
Completeness of the respective charges identifies both as stabilizers.

This example shows why excluding *all* weight-19 mixed histories would be
incorrect: a successful energy inequality must detect nonzero charge.

## Explicit failure modes and the remaining gap

**FALSE (linear valuation energy).** The tempting inequality
`wt(P)>=ord_1(P)+1`, even with degree at most 18 and with both valuations
positive, fails for

```
P=t⁸=T⁸+T¹⁶:    (alpha,beta,d,s,wt)=(8,8,16,8,2).
```

Also `t⁷` has weight 8 whereas `t⁸` has weight 2. Coefficient width grows
under multiplication by t, but coefficient weight need not grow.
The equality `t⁸=t*t⁷` already exhibits this failure inside the exact
transport equation with zero forcing. This is not a counterexample to the
code's conjectured distance.

**FALSE (positive surcharge for every mixed cancellation).** Take `c=T²`
and `h=1`. The physical slice is `(0,1)`, of weight 1, exactly `wt(c)`;
the mixed injection is nonzero but the instantaneous surcharge is zero.
Future equations, rather than a positive local surcharge, must pay for it.

**CONJECTURE (distance-20 target; unproved here).** Every physical X or
reflected Z cycle of weight at most 19 has zero complete charge.

**Named gap: overlapping-injection charge accounting.** To deduce that
conjecture from this approach, one still needs a disjoint physical-weight
bound for histories with both initial canonical states nonzero and arbitrary
overlapping injections. Precisely, the exact unrolling is

```
c_n = t^k c_(n-2k)
    + sum_(j=0)^(k-1) t^j (lambda h_(n-2j-1)+B h_(n-2j-2)),
```

whenever all k equations have indices in `[2,18]`. This identity follows
by repeated substitution (**PROPOSITION**, pending review/formalization).
The summands can cancel at 0, at 1, and at the leading degree, and a single
h slice feeds two different parity chains. Proposition 5 does not classify
these overlapping histories or their interactions with either boundary.
Proposition 3 cannot be summed over hypothetical packets sharing physical
slices. Proposition 4 explains exactly why charging each injection separately
can double-count or charge zero-cost replacements. The missing bound must
retain residue modulo D as well as the three valuations: D itself is a unit
at 0 and 1, while it annihilates the complete charge. No assertion of
relative exactness below 20 is used as a substitute for this missing step.

## Persisted closed-form checks

`valuation_energy_check.py` checks the two annihilator identities, their
physical slice formulas, degree caps, the closed-form S=1 examples, the
Frobenius counterexamples, and the ten-term packet energy. It additionally
checks one explicitly chosen polynomial multiplier S=t; it does not enumerate
supports, cycles, candidate words, or certificates. The arguments above are
algebraic proofs; the script is only an arithmetic transcription check.
It verifies the two full weight-19 histories by direct substitution in all
17 required equations. The Python 3.13 closed-form check and the file's Ruff
lint and format checks passed. Commands (the cache override keeps writes
inside the permitted temporary directory):

```
UV_CACHE_DIR=/tmp/valuation-energy-uv-cache uv run --locked --offline --python 3.13 python analytical/notes/valuation_energy_check.py
UV_CACHE_DIR=/tmp/valuation-energy-uv-cache uv run --locked --offline ruff check --no-force-exclude analytical/notes/valuation_energy_check.py
UV_CACHE_DIR=/tmp/valuation-energy-uv-cache uv run --locked --offline ruff format --check --no-force-exclude analytical/notes/valuation_energy_check.py
```
