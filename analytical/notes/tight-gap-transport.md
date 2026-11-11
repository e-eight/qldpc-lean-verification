# Exact transport through an incoming gap of excess two

2026-11-11. **All mathematical claims in this note are PROPOSITION,
pending independent review and formalization.** In particular the final
weight-17 exclusion is conditional on the tightness classification in
`strip-deficits.md`, Proposition 24. It is not a new formalized distance
claim. Only this new note is written; no existing note or proof is changed.

Result: a forward incoming gap of excess two cannot follow a monomial-seed
short run of length one or two. In the backward direction exactly two local
forms survive. Both have gap length four and force an outgoing polynomial
with three coefficients. Thus neither can precede the monomial-seed short
run required at weight 17. This gives an exclusion, rather than a drift bound.

## Sources and scope

Read root `AGENTS.md`, `strip-deficits.md` Propositions 22–26 and their
tightness discussion, and the canonical injection equation in
`valuation-energy.md`. The explicit model and complete-charge interface
are those of `analytical/rectangle722-distance17/PROOF.typ`.

Source hashes at reading:

```
strip-deficits.md:
5ad5c03aac2161f358e078151bac7de9f1e45ddca3c2e2ba3f62d0068e0dd04e
valuation-energy.md:
d0b0e8af418699102b413077750719838e6479fbd8ade5d760f160eec42f2d93
rectangle722-distance17/PROOF.typ:
6dcccb32f1b11e0c2eae81ace1e94c0f995971daeac73b39a66f2b09bff80cab
```

The argument is a symbolic classification of a weight-two slice into its
three possible block allocations. Monomial exponents remain arbitrary.
There is no error/support search, computational enumeration, LP, Lean run,
or symbolic-check script. All substitutions needed for the result appear
below, including the surviving forms and outgoing polynomials.

## PROPOSITION 1: exact local setup and parity budget

Put `s=T²`, `t=T+T²`, `B=1+st`. Use the forcing direction as increasing
index. In the forward system define

```
c_i=a_i+s b_i,    h_i=b_i,    lambda=1.
```

In the backward system first reverse the physical slice index and define

```
c_i=s a_(18-i)+b_(18-i),    h_i=a_(18-i),    lambda=s.
```

Then the canonical equation and physical slice, in canonical block order,
are

```
c_i = t c_(i-2)+lambda h_(i-1)+B h_(i-2),
(primary,injection) = (c_i+s h_i,h_i).
```

Canonical block order is `(a,b)` in F and `(b,a)` after reversal in B.
All coefficients are in F₂. Physical degree is at most 18; canonical c
can have degree 20. Every equation here is exact, without truncation.
The equation follows by substitution in the two original recurrences;
in B the unreversed identity is
`c_(j-2)=t c_j+B a_j+s a_(j-1)`.

Translate the initial zero of the longer gap to index 0 and its final
zero to index d, with `d>=4`. Every interior is occupied. Suppose the
preceding short run has length `m in {1,2}` and monomial seed `M=T^q`.
The incoming terminal middle is `(t^(m-1)M,0)` in canonical block order,
at index -1. Consequently

```
c_0=h_0=0,       c_1=t^m M,
c_2=lambda h_1,
c_d=h_d=0.
```

Suppose the gap has excess exactly two:

```
sum_(i=1)^(d-1) w_i = d+1,
w_i=wt(c_i+s h_i)+wt(h_i).
```

Then `w_1=2`, and among slices 2 through d-1 exactly one has weight two;
all the others have weight one. To prove this, `tM` and `t²M` both have
two coefficients, so `w_1>=2`. Also

```
w_i = wt(c_i)+2(wt(h_i)-|supp(c_i) intersect supp(s h_i)|),
```

and therefore `w_i` and `wt(c_i)` have the same parity. The budget permits
at most weight three at any interior, so the even weight `w_1` must be two.
Exactly one excess unit remains. This overlap identity is the essential
injection-cost constraint: no positive cost is assigned to a cancellation
unless it occurs in the actual physical weight.

## PROPOSITION 2: a first slice supported in only one block is impossible

Under Proposition 1, slice 1 must have one monomial in each physical
block. The proof treats both one-block possibilities for both directions.

### Primary-only first slice

Here `h_1=0`, so `c_2=0`. Occupancy forces slice 2 to be the unique
remaining weight-two slice, of form `(sH,H)` with H monomial. Thus

```
c_3=t^(m+1)M+lambda H.
```

Slice 3 is a singleton. For `m=2`, `t³M` has four coefficients and adding
one monomial cannot give a monomial. For `m=1`, the monomial `lambda H`
must cancel one of the two terms of `t²M`; write the remaining monomial
as `c_3=N`. Since slice 3 is a singleton, `h_3` is either 0 or `N/s`.
But

```
c_4=B H+lambda h_3.
```

The first summand has three coefficients. Adding zero leaves weight three;
adding a monomial gives weight two or four. This is neither zero (required
when `d=4`) nor a monomial (required when `d>4`). Contradiction.

### Injection-only first slice

Here `c_1=s h_1`, with `h_1` a binomial. Thus `c_2=lambda h_1` is a
binomial, and slice 2 is the unique remaining weight-two slice. Using
`st+B=1` gives

```
c_3=h_1+lambda h_2.
```

Slice 3 is a singleton. Since `h_1` has even weight, `h_2` must have odd
weight. Its slice has weight two, so `h_2` is a monomial and slice 2 is
mixed. Write `h_1=H+J`, choosing H so that `s h_2=lambda H`. Set
`eta=lambda²/s`, a Laurent monomial used only for algebraic comparison.
Then

```
c_3=H+J+eta H.
```

Here `eta=T^-2` in F and `eta=T²` in B; it is never 1. For c_3 to be a
monomial one must have `J=eta H`, and then `c_3=H`. In particular the
binomial separation is two, forcing `m=2`. The next singleton has
`h_3=0` or `H/s`. Direct substitution yields

```
c_4=(lambda/s)(H+t lambda² H+s h_3).
```

If `h_3=0`, this is a monomial times `1+t lambda²`, which has exactly
three coefficients in either direction. If `h_3=H/s`, it is a monomial
times t, with exactly two coefficients. Again it is neither zero nor a
monomial. This proves the proposition. All displayed divisions by monomials
are Laurent identities; a case requiring a negative physical exponent is
already inadmissible and cannot create an extra solution.

## PROPOSITION 3: the mixed first slice excludes the entire forward case

By Proposition 2 write slice 1 as `(A,H)`, where A,H are monomials:

```
c_1=A+sH=t^m M,       c_2=lambda H.
```

The second canonical value is a monomial. Its physical weight is odd,
and the remaining excess is only one, so slice 2 is a singleton. Hence
`h_2=0` or `h_2=lambda H/s`, and

```
c_3=tA+H+lambda h_2.
```

If `h_2=0`, this polynomial has odd coefficient parity, so slice 3 must
also be a singleton. That requires `H=TA` or `H=T²A`. But then the two
terms of `A+sH` have exponent separation three or four, whereas `t^m M`
has separation m, equal to one or two. Thus

```
h_2=lambda H/s,
c_3=tA+(1+eta)H,       eta=lambda²/s.
```

This has even parity. Since slice 3 is occupied, it is the unique second
weight-two slice, and all later interiors are singletons. In particular
`wt(c_3)<=2`. Write `sH=A T^delta`; the incoming binomial forces
`delta in {m,-m}`. The exponents of `c_3/A` are

```
F: 1, 2, delta-2, delta-4;
B: 1, 2, delta-2, delta.
```

In F, for every `delta in {1,-1,2,-2}`, the last two exponents are
distinct, at most zero, and hence different from 1 and 2. Thus c_3 has
four coefficients, contradicting its physical weight bound. This proves
that **no incoming excess-two gap with m=1 or m=2 exists in F**.

This is an extreme-exponent obstruction: it uses the relative transverse
positions of two monomials, not a run count or a linear valuation estimate.

## PROPOSITION 4: complete backward classification and outgoing cost

In B, negative delta again gives four distinct exponents. Positive delta
gives exactly the following alternatives:

```
m=1: A=TH,    c_3=H+T³H;
m=2: A=H,     c_3=H+TH.
```

In both cases `h_2=H`. Put `N=T³H` for m=1 and `N=TH` for m=2.
Then `c_3=H+N`, and the next equation is particularly simple:

```
c_4=H+s h_3.
```

Since slice 3 has physical weight two and its canonical value is the
binomial `H+N`, its only possible injection polynomials are

```
h_3=0, (H+N)/s, H/s, N/s.
```

These are the two one-block allocations and the two mixed allocations;
there can be no hidden overlap because its physical weight equals its
canonical weight.

If `d=4`, the condition `c_4=h_4=0` forces `h_3=H/s`. Slice 3 is then
`(N,H/s)`. This is a valid ending and will be displayed explicitly below.

Suppose instead `d>=5`. Slice 4 must be a singleton.
The option `h_3=H/s` gives `c_4=0` and cannot be a singleton.
The option `h_3=N/s` gives `c_4=H+N` and cannot be a singleton either.
There remain two cases.

* If `h_3=0`, then `c_4=H` and `h_4=0` or `H/s`. Therefore
  `c_5=t(H+N)+s h_4`. For m=1 the first term is
  `H(T+T²+T⁴+T⁵)`, with four coefficients; adding zero or H cannot
  make zero or a monomial. For m=2 the first term is `H(T+T³)`;
  adding zero or H gives two or three coefficients. Both contradict the
  required zero at `d=5` or singleton at `d>5`.
* If `h_3=(H+N)/s`, then `c_4=N` and `h_4=0` or `N/s`. Now
  `c_5=(H+N)/s+s h_4`, using `t+B/s=1/s`. Its first two terms
  are H/s and N/s; the optional third term N equals neither of them,
  since `N/H` is T³ or T, never `T^-2`. Thus c_5 has two or three
  coefficients, again impossible.

It follows that **d=4 is necessary**, with physical interior forms below.
Here M is the original run seed; entries are in canonical block order
`(b,a)` along decreasing original slice index.

| Run length | Slice 1 | Slice 2 | Slice 3 |
|---|---|---|---|
| m=1 | `(TM,M)` | `(0,M)` | `(T³M,T^-2M)` |
| m=2 | `(T²M,T²M)` | `(0,T²M)` | `(T³M,M)` |

The directional weights are `(2,1,2)`, giving exactly excess two. The
width-19 condition on these interiors is `2<=q<=15` in the first row
and `0<=q<=15` in the second, for `M=T^q`. The preceding run also fits
these ranges. These bounds follow by inspecting the smallest and largest
physical exponents, and are sufficient for the local patch.

For completeness, substitution verifies the surviving local equations:
`c_1=t^m M`, `c_2=sH`, `c_3=H+N`, `h_2=H`, `h_3=H/s`, and

```
c_3=t c_1+s h_2+B h_1,
c_4=t c_2+s h_3+B h_2=stH+H+BH=0.
```

If the next slice is on board and its equation is tested, then, with
`c_4=h_4=0`, its canonical polynomial is forced independently of how
its two physical blocks are split:

```
c_5=t c_3+B h_3=tN+H/s
   = (T⁴+T⁵+T^-2)M       (m=1),
   = (1+T⁴+T⁵)M          (m=2).
```

Both have exactly three distinct coefficients. Thus the outgoing physical
weight is at least three. If it starts a short run, its injection is zero,
so this is its actual seed polynomial, not merely a canonical lower bound.
Its first-middle surplus is at least two.

These expressions also record the transverse behavior exactly: the outgoing
orders at zero are `q-2` and q, the degrees are both `q+5`, and the orders
at one are zero. Thus the viable backward local patches do not obey a
universal positive shift of the minimum transverse exponent. The obstruction
needed here is the unavoidable three-coefficient output. A following short
run additionally requires `q<=13` just for this outgoing slice to fit.

## PROPOSITION 5: conditional exclusion of total weight 17

Assume the exact recurrences and adjacent nonemptiness of the physical strip,
and the tightness conclusions of `strip-deficits.md`, Proposition 24,
with the packet surplus bounds of Propositions 25–26. Then **W=17 is
impossible in either direction**.

Proof. The cited tightness conclusions say that at least one longer gap
exists; every such gap has excess exactly two, is fed by a monomial-seed
short run of length one or two, and is followed by another monomial-seed
short run. All longer gaps have length at least four. The final run is the
missing-exit run; it is not a longer gap. Proposition 3 excludes every
such longer gap in F. In B, Proposition 4 forces a length-four gap with
outgoing seed of weight three, contradicting the monomial seed, or
equivalently the required `Delta=0`. No new surplus is added to an already
counted quantity: this is a contradiction to equality's existing budget.

The index requirements are satisfied. In canonical board coordinates the
zero beginning an incoming longer gap is at some K>=2, because a short gap
precedes it. The equations used locally have board indices K+1 through
K+4, and K+5 only when d>=5 or an outgoing slice is used. They all lie
in `[2,18]`. In the surviving d=4 backward case, a following short gap
requires `K+6<=18`, so the outgoing equation at K+5 is tested. Reversing
back maps these to precisely the original backward equations; no equation
at the missing final exit is used. Even if the following run is the final
missing-exit run, its first middle is on board and the contradiction remains.

Combined with the existing lower bound 17 and its charge-to-adjacent-
nonemptiness interface, this would give **distance at least 18**, conditional
on review/formalization of the cited allocation result and this note. It
does not establish distance 19 or 20. The local statements, Propositions
1–4, need neither charge completeness nor the global allocation result.

## Review targets

The new algebraic claim to review is the complete local classification in
Propositions 2–4, including physical block order in B and both tested-index
endpoints. The only imported global step is the necessary weight-17
structure, including existence of a longer gap. No claim is made that
every scalar tight profile realizes a cycle. In fact the local result
excludes precisely the transitions that such a profile would require.
