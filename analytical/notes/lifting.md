# An analytic lifting route for the literal 566-qubit code

This note derives a conditional distance-transfer proposition with an explicit
stabilizer correction. It does **not** certify distance twenty for the target:
source distance lower bounds and a target support-overlap statement remain
unproved. The argument uses physical Hamming weight throughout. There is no
assumption that a CNOT circuit preserves weight.

Scope: mathematical derivation and read-only inspection of the submitted
matrices, on 2026-11-11. No Lean run, distance search, exhaustive logical
enumeration, or new computer certificate was used. Existing formal results
are identified separately below. Only this note is owned by this work.

## Claim grading (applies globally)

- **PROPOSITION — independent review and formalization pending:** every
  mathematical derivation in this note, including identities, lemmas,
  corollaries, conditional implications, and counterexample calculations.
  A supplied proof is a proposed mathematical proof, not an independently
  reviewed or kernel-checked result. This grade applies also to derived
  sentences without a repeated inline label.
- **NAMED UNPROVED HYPOTHESIS:** H_X, H_Z, H_corr (also written Hcorr), H_C,
  and the proposed target descent property. None is established here.
- **CHECKED DATA:** input hashes, literal row identities, support tables,
  and direct dot-product checks. These are read-only finite data checks,
  not distance certificates. Section 1 uses this grade unless explicitly
  referring to a prior formal result or drawing a mathematical inference.
- **EXISTING FORMAL RESULT (reported):** explicitly named Lean results and
  their recorded audits. They were inspected but not rerun in this work.
- **FALSE:** an explicitly rejected implication, accompanied by a concrete
  counterexample. The counterexample derivation itself has PROPOSITION status.

No derived result in this note is assigned a stronger grade than PROPOSITION.

## 1. Start with the actual matrices

The inputs are `codes/578-18-20.json` and `codes/566-18-20.json` in the sibling
`qldpc-challenge` checkout. Their raw SHA-256 hashes, checked for this note, are

```text
578: 440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514
566: 061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be
```

These agree with the pinned inputs in the
[lifting investigation](../../data/lifting-566-investigation/README.md) and
[removal proof record](../../data/removal566-evaluation/README.md).
The source has 280 X rows and 280 Z rows, both independent. The target has
274 independent rows on each side. Thus both encode eighteen qubits.
These rank statements already have the capstone `Removal566.ranks` in
[Boundary566.lean](../../lean/QldpcVerification/Boundary566.lean).

The source's bulk family is specified by the binary polynomials

```text
f(u,v) = 1 + v^3 + u^2 v^2 + u^3,
g(u,v) = v + uv + u^2 + u^3 v^3.
```

Use two species of cells A(i,j), B(i,j), with `0 <= i,j < 17`, indexed by
`17i+j` and `289+17i+j`. An X bulk row at (i,j) has f on A and g on B.
Read-only comparison with the raw JSON verified that all 196 such rows for
`0 <= i,j < 14` occur in the source. Thus the upstream source note's
“14 x 14 bulk” counts fully supported translates; it is compatible with
the 17 x 17 cell array and 578 qubits. The boundary rows are part of the
literal input, not determined by these bulk polynomials alone.

The local `research/local2d/boundary_engine.py` describes boundary-module,
corner-completion, and cleanup choices. It also distinguishes this g from
the published tile support and other supports used by the builder. Consequently
neither a distance statement for a different tile nor a parameter match
establishes a lower bound for this source. No family-builder equivalence is
assumed here; the source below means exactly the hashed matrices.

All indices in this note are zero based. Delete source coordinates
`272..277` and `564..569`, retaining all other coordinates in source order;
call the retained set K. Define pairs `a_i=272+i`, `b_i=564+i` for `0<=i<6`.
The following supports use the **target** numbering of K:

| i | Source X row | Source Z row | Retained fan r_i |
| --- | --- | --- | --- |
| 0 | 182 | 201 | 221,224,257,505,522,538 |
| 1 | 183 | 207 | 222,225,258,506,523,539 |
| 2 | 184 | 213 | 223,226,259,507,524,540 |
| 3 | 185 | 219 | 224,227,260,508,525,541 |
| 4 | 186 | 225 | 225,228,261,509,526,542 |
| 5 | 187 | 231 | 226,229,262,510,527,543 |

The distinguished X row is `r_i+e_a_i+e_b_i`. Every other source X row
vanishes on these twelve coordinates. The distinguished Z row is
`e_a_i+e_b_i`. Deleting those six rows on each side and the twelve columns
gives the target matrices literally, in row order. These identities were
rechecked directly on the sparse JSON lists for this note, independently of
the search history. The existing removal proof recognizes twelve elementary
steps, not the upstream note's unreconstructed “ten accepted moves”.

## 2. Exact block algebra and its proof

All vector spaces are over F2. Write A and B for the target X and Z row
spaces. CSS commutation says `A <= B^perp`. Define

```text
L_X = B^perp \ A,       L_Z = A^perp \ B,
R(z)_i = r_i dot z,     r(t) = sum_i t_i r_i.
```

These are sets of all nontrivial logical representatives, not selected
logical bases. Let `|v|` mean Hamming weight. Write old vectors in the
coordinate order `(K,a,b)`; this is only a permutation of physical qubits.

**PROPOSITION P1 (block lemma; review/formalization pending).** The source stabilizer spaces are exactly

```text
A_old = { (a+r(t), t, t) : a in A, t in F2^6 },
B_old = { (b, R(b)+q, q) : b in B, q in F2^6 }.
```

Source X logicals are exactly `(x+r(t),t,t)` with `x in L_X`.
Source Z logicals are exactly `(z,R(z)+q,q)` with `z in L_Z`.
In particular,

```text
dX_old = min_{x in L_X, t in F2^6} (|x+r(t)| + 2|t|),
dZ_old = min_{z in L_Z} (|z| + |R(z)|).                 (1)
```

**Proof.** The claimed X span follows immediately from the distinguished
X rows and the zero-padded remaining rows. For a source Z row with retained
part b and pair entries alpha,beta, commutation with each distinguished
X row gives `alpha+beta=R(b)`. Its retained part is a target Z row, or zero
for a distinguished pair row. Adding pair rows independently changes both
entries of any pair. Since the other retained rows span B, this proves both
inclusions in the displayed description of `B_old`.

An X vector `(y,alpha,beta)` commuting with all pair Z rows must have
`alpha=beta=t`. Its pairing with `(b,R(b)+q,q)` is
`b dot (y+r(t))`. Thus it is a cycle precisely when `x=y+r(t)` belongs to
`B^perp`, and the X span description says it is a stabilizer precisely when
`x in A`. This proves the X claim including nontriviality.

A Z vector `(z,alpha,beta)` commuting with all zero-padded X rows must have
`z in A^perp`. Commuting with the distinguished X rows further forces
`alpha+beta=R(z)`. The description of `B_old` then says it is a stabilizer
precisely when `z in B`, proving the Z claim including nontriviality.

The X weight is `|x+r(t)|+2|t|`. For Z, a pair of parity zero costs at least
zero and a pair of parity one costs at least one. Both minima can be achieved
independently, for example by `q=0`. Minimizing gives (1). All sets are finite,
and the nontrivial sets are nonempty because k=18. This proves the lemma.

The maps also preserve logical pairing: pairing the displayed X and Z lifts
gives `x dot z`, since the two contributions `t dot R(z)` cancel. Replacing
z by `z+b`, `b in B`, changes its lift by a source Z stabilizer, so it preserves
the corresponding source logical class, not merely nontriviality.

The immediate comparisons are

```text
dX_target >= dX_old,
dZ_target <= dZ_old <= dZ_target + 6.                  (2)
```

For the first, choose `t=0` for any target X logical. For Z, every term in
(1) is at least `dZ_target`, and a shortest target Z logical has at most six
extra bits. This proves (2). In particular, hypothetical source lower bounds
twenty yield only target lower bounds twenty/fourteen without correction.

The elementary normal form and logical/weight results are in
[QubitRemoval.lean](../../lean/QldpcVerification/QubitRemoval.lean):
`old`, `liftZ_logical_iff`, `liftZ_weight`, `new_X_lower`, and `new_Z_lower`.
Transport and composition are in `QubitRemovalTransport.lean`,
`QubitRemovalSequence.lean`, and `Boundary566.lean`. The block proof here is
a mathematical derivation, not a claim that its exact formulas or the
following correction lemmas have been formalized.

## 3. Stabilizer correction with an exact weight budget

For binary vectors v,b let
`I(v,b)=|supp(v) intersect supp(b)|`. Counting the coordinates in the
symmetric difference proves

```text
|v+b| = |v| + |b| - 2 I(v,b).                          (3)
```

**PROPOSITION P2 (correction lemma; review/formalization pending).** Suppose a source/target pair has the
block description above, with r pairs instead of necessarily six. Let D be
a positive integer and assume every source Z logical has weight at least D.
It suffices for `dZ_target >= D` to prove the following statement:

For every `z in L_Z` with `D-r <= |z| <= D-1` and
`|R(z)| >= D-|z|`, there is a `b in B` such that

```text
2 I(z,b) >= |b| + |R(z)+R(b)| - (D-1-|z|).            (4)
```

One may weaken this requirement to representatives z that have minimum
weight in their own coset `z+B`.

**Proof.** Suppose a target Z logical of weight below D exists, and choose
one of minimum weight in its nontrivial coset if using the weaker condition.
It remains nontrivial. The source lift `(z,R(z),0)` and the source lower bound
give `D <= |z|+|R(z)| <= |z|+r`. Thus z meets both the weight interval and
parity condition. Choose b as in (4). Since `b in B <= A^perp`, `z+b` is a
cycle in the same nonzero quotient class. By the block lemma it lifts to a
nontrivial source logical of weight

```text
|z+b| + |R(z+b)|
  = |z| + |b| - 2 I(z,b) + |R(z)+R(b)|
  <= D-1,
```

contradicting the source lower bound. This proves the claim. The argument
requires no known exact target minimum and no distance search.

For the target and D=20, only weights 14 through 19 remain. If `w=|z|`, the
uncorrected parity must have weight at least `20-w`; otherwise its canonical
lift already contradicts the source lower bound. Correction may increase
retained weight, but its total lifted weight must stay at most nineteen.
This slack is useful: full weight preservation is unnecessarily strong.

For a single elementary removal, if `s dot z=1` and a stabilizer b satisfies
`s dot b=1`, then `z+b` has zero lift parity. Equation (3) shows that its lift
does not exceed `|z|` exactly when `2 I(z,b) >= |b|`. This proves the elementary
half-overlap observation in the lifting record, and (4) is its multi-pair,
threshold-sensitive version. Repairing individual bits in sequence without
tracking the other bits is insufficient: a correction can turn them back on.

## 4. An explicit right inverse for the target parity map

**CHECKED DATA; PROPOSITION P3 for the resulting right inverse
(review/formalization pending).** Let `h_j` denote target Z row j as a binary vector. The following actual
stabilizers c_i satisfy `R(c_i)=e_i`:

| i | c_i as target Z rows | Support in target coordinates | Weight |
| --- | --- | --- | --- |
| 0 | h_209 + h_235 | 257,262,276,543,548 | 5 |
| 1 | h_214 | 258,272,544 | 3 |
| 2 | h_197 | 238,258,524,539 | 4 |
| 3 | h_199 | 255,541,556 | 3 |
| 4 | h_204 | 256,542,557 | 3 |
| 5 | h_235 | 262,276,548 | 3 |

These identities can be checked by taking six dot products with the r_i
table. For example, `h_209={257,543}` has parity `e_0+e_5`, and h_235 has
parity e_5; their sum gives c_0. For c_1 the intersection with r_1 is {258}
and all other fan intersections are empty, giving exactly e_1. The other
rows follow by the same explicit support intersections.

Define the linear stabilizer-valued map

```text
C(p) = sum_{i=0}^5 p_i c_i.                           (5)
```

Linearity proves `R(C(p))=p` for every p, without enumerating parity patterns.
Thus `R|B` is surjective and every logical class has a representative with
zero lift parity. The correction in (5) is supported on the set
`T={238,255,256,257,258,262,272,276,524,539,541,542,543,544,548,556,557}`;
it has seventeen elements. All overlaps among corrections must be handled
by binary addition in (5), rather than summing their weights.

This yields a particularly concrete sufficient hypothesis for distance 20:

> For every coset-minimum nontrivial target Z cycle z of weight w from 14 to
> 19 with `|R(z)| >= 20-w`, set p=R(z) and c=C(p). Prove
> `2 I(z,c) >= |c| - (19-w)`.

Call this **H_C — NAMED UNPROVED HYPOTHESIS**. It is (4) with zero residual parity. The correction lemma
therefore proves that a source Z lower bound twenty plus H_C implies a target
Z lower bound twenty. H_C is a precise, unproved sufficient condition; these
particular c_i need not be the best corrections for deriving a contradiction
from a hypothetical short logical. The parity identities alone do not prove
the overlap inequality. If the target distance is twenty, H_C holds vacuously;
using that fact to establish H_C here would be circular.

There is more freedom without changing parity: replace C(p) by `C(p)+b_0`
for any `b_0 in B intersect ker R`. Conversely every stabilizer with parity p
has this form, because subtracting C(p) gives parity zero. Thus an analytic
proof can use bulk and boundary stabilizers to improve overlap before lifting.
The unrestricted condition (4) additionally allows a nonzero residual parity
when the nineteen-qubit budget permits it.

## 5. What a geometric argument must actually show

**PROPOSITION P4 (minimum-weight consequences; review/formalization pending).**
For a representative of minimum weight in `z+B`, (3) implies

```text
2 I(z,b) <= |b|   for every b in B.                    (6)
```

Thus a no-growth correction to such a representative must satisfy equality,
not merely a large unspecified overlap. In particular an odd-weight
stabilizer cannot give a weight-preserving move from a coset minimum. Five
of the six displayed c_i have odd weight. This is a concrete reason why
independent single-bit repair is too strong near w=19; sums and changes
within `B intersect ker R` may be needed.

For H_C, the required retained-weight increase is at most `19-w`: respectively
5,4,3,2,1,0 for w=14,15,16,17,18,19. At w=19 it must be an equal-weight
zero-parity representative. This is a real geometric obligation, not supplied
by the rank-six parity calculation.

A stronger **NAMED UNPROVED HYPOTHESIS (target descent)** asserts that every coset-minimum
nontrivial cycle of weight below twenty and nonzero R admits a stabilizer b
with `2 I(z,b)=|b|` and `|R(z+b)|<|R(z)|`. Repeating this move terminates in
at most six steps: weight remains constant and the nonnegative integer
parity weight strictly decreases. Every intermediate vector is still a
coset minimum in the same nonzero class. The terminal zero-parity vector
lifts at unchanged weight, contradicting the source bound. This proves the
conditional descent criterion (PROPOSITION, review/formalization pending),
but its existence hypothesis is unproved for the target.

There is a small boundary interface for trying to prove these statements.
Direct row inspection shows that the only 21 target Z generators with nonzero
R are rows

```text
182..190, 197,199,202,204,207,209,212,214,219,224,229,235.
```

All other target Z generators have parity zero and are available for reshaping
the representative without changing its lift cost. An analytic approach can
use the explicit bulk recurrence from f,g and the literal boundary checks
to constrain how a small cycle meets T and these boundary rows. It must prove
that every relevant nontrivial cycle obeys (4), or H_C, or the stronger descent
condition. A proof just for stored logical witnesses or eighteen basis vectors
does not suffice. A finite list of local pictures also needs a proof that
the cycle equations, the weight budget, and coset minimality force every
candidate into those pictures. No such classification is asserted here.

**FALSE: surjectivity of stabilizer lift parity implies distance preservation.**
**PROPOSITION P5 (counterexample; review/formalization pending).** Take the retained
three-qubit code with no X checks, Z space `span{110,001}`, and elementary
fan `s=111`. Its nontrivial Z representatives are exactly
`100,010,101,011`. Their weights are 1,1,2,2 and their fan parities are
1,1,0,0. The graph extension therefore has Z distance two, while the retained
code has Z distance one, despite `s dot 001=1` making the stabilizer parity
map onto. This also demonstrates why choosing a zero-parity representative
without bounding its weight proves no lower bound after removal.

## 6. Conditional certification proposition and remaining obligations

**PROPOSITION P6 (conditional certification; review/formalization pending).**
For the literal matrices in Section 1, suppose the following named unproved hypotheses:

1. Every nontrivial source X logical has weight at least twenty (**H_X**).
2. Every nontrivial source Z logical has weight at least twenty (**H_Z**).
3. The target correction condition (4) holds with D=20 and r=6 for the
   coset-minimum candidates specified there (**H_corr**). H_C suffices.

Then the target has parameters `[[566,18,20]]`.

**Proof.** The existing ranks give k=18. The zero-padded X lift and H_X give
`dX_target>=20`. The correction lemma and H_Z,H_corr give `dZ_target>=20`.
For a CSS Pauli represented by (x,z), commuting means `x in B^perp` and
`z in A^perp`; being nontrivial means at least one of `x notin A`, `z notin B`.
Its physical support is the union of the two supports, whose size is at least
the weight of that nontrivial component. Hence every nontrivial Pauli has
weight at least twenty. Conversely the existing literal target X witness of
weight twenty supplies a nontrivial Pauli of weight twenty, giving equality.
The witness is recorded in the input and covered by the existing direct
distance proof; a weight-twenty Z witness is not required. This proves the
conditional proposition.

The remaining obligations are substantive and separate:

| Obligation | Status and required content |
| --- | --- |
| Literal source/target recognition, ranks, elementary removals | Existing formal results; raw block identities also rechecked for this note. No distance-twenty assumption follows. |
| H_X | NAMED UNPROVED HYPOTHESIS, not supplied by the lifting/removal records. Needs an analytic lower bound for all source X logicals, or a direct target X lower bound replacing this premise. |
| H_Z | NAMED UNPROVED HYPOTHESIS, not supplied by the source's randomized searches. Needs a lower bound for every source Z logical. |
| H_corr / Hcorr (or H_C) | NAMED UNPROVED HYPOTHESIS. Must give a stabilizer correction with the stated total weight budget for all relevant short coset minima. The explicit right inverse proves only the parity equation. |
| Family-to-source bridge, if using a family theorem | Must identify all boundary and corner row spaces with the literal hashed source via physical permutations and row operations. The verified 196 bulk rows alone are insufficient. This extra bridge is unnecessary if H_X and H_Z are proved directly for the literal matrices. |
| Formalization of this route | The correction lemma, its target overlap hypothesis, and any new family distance theorem are not Lean results. No new axiom audit or Lean validation was performed. |

The source files' distance fields and stored witnesses establish upper bounds
only. In particular H_X and H_Z must not be inferred from the name
`578-18-20`, an RIS search that found nothing lighter, or a theorem about a
different tile support. The independent analytic route is now explicit:
prove source side bounds, prove the boundary correction budget, then apply
the conditional proposition above. It does not yet close either of those analytic gaps.

## 7. Weight nineteen: an exact parity obstruction and an overlap mechanism

All results P7–P10 below are **PROPOSITION — independent review and
formalization pending**. Their proofs do not assume any target distance.

### P7. Which parity repairs can even have equal weight?

Let z be a minimum-weight representative of z+B, with `|z|=19`, and put
`p=R(z)`. Define the linear weight-parity functional and the weight increment

```text
chi(b) = |b| mod 2,     B_even = B intersect ker chi,
Delta_z(b) = |z+b|-|z| = |b|-2 I(z,b).
```

Then `Delta_z(b)>=0` for all b in B, and

```text
|z+b| + |R(z+b)| <= 19
  iff Delta_z(b)=0 and R(b)=p.                        (7)
```

Every such b lies in B_even. In particular an odd-weight stabilizer cannot
repair z within the nineteen-qubit lift budget, regardless of which lift
parities it changes. The exact algebraic obstruction is

```text
p not in R(B_even)  implies that no budget-preserving repair exists. (8)
```

There is a useful dichotomy for computing this obstruction without minimum
weight searches. Let `K_0=B intersect ker R`.

1. If K_0 contains an odd-weight element k, then `R(B_even)=R(B)`.
2. Otherwise chi factors through R: there is a unique linear functional
   lambda on R(B) with `chi(b)=lambda(R(b))`, and
   `R(B_even)=ker lambda` inside R(B).

**Proof.** Formula (7) follows because its left side is
`19+Delta_z(b)+|p+R(b)|`, a sum of nineteen and two nonnegative integers.
Equality of retained weights forces `chi(b)=0` by (3), proving (8).
Weight parity is linear because symmetric difference subtracts twice an
intersection size. If k is odd with R(k)=0, replace any odd preimage b of a
parity by b+k; this makes it even without changing R(b). This proves case 1.
If all elements of K_0 are even, two preimages of a parity differ by an even
element, so they have the same chi. Defining lambda by this value is
well-defined and linear. Its kernel consists exactly of the parities of
even stabilizers, proving case 2 and uniqueness. These cases are exhaustive.

**CHECKED DATA and consequence for the target.** The target is in case 1.
Using the rows and c_i already displayed, set

```text
k = h_182 + c_0 + c_2
  = {221,238,241,258,262,276,507,522,524,539,543,548,555}.
```

Here `R(h_182)=e_0+e_2`, `R(k)=0`, and `|k|=13`. Thus even-weight target
stabilizers reach **all six-bit parities**. Explicitly, replace each odd c_i
by c_i+k and leave c_2 unchanged. The resulting six even stabilizers have
weights `10,14,4,16,16,10`, respectively, and parity images e_i.
Their membership and images follow from the displayed row sums; their
supports and weights were rechecked by direct set operations on the input.

This rules out a global weight-parity obstruction for the actual target.
It does not establish equal-weight repair: (7) also needs Delta_z(b)=0.
In contrast, the fixed right inverse C has

```text
chi(C(p)) = p_0+p_1+p_3+p_4+p_5  in F2.
```

If this value is one, C(p) specifically cannot repair a weight-19 coset
minimum. For such a hypothetical candidate, H_C's prescribed correction
is impossible. One must use a different stabilizer or exclude the candidate;
this does not refute H_C for the target, since no such candidate is known.
Adding k removes the parity obstruction, but can still increase weight.

### P8. Two odd generators can cooperate through their intersection

For any b,c in B define the signed intersection

```text
J_z(b,c) = |(supp(b) intersect supp(c)) minus supp(z)|
           - |supp(b) intersect supp(c) intersect supp(z)|.
```

Then the exact identity is

```text
Delta_z(b+c) = Delta_z(b)+Delta_z(c)-2 J_z(b,c).       (9)
```

If b and c are odd and z is a coset minimum, both individual increments
are positive odd integers. Their sum preserves weight exactly if and only if

```text
J_z(b,c) = (Delta_z(b)+Delta_z(c))/2.                 (10)
```

In particular, disjoint odd generators cannot cooperate to preserve weight.
If they meet in exactly one qubit q, equality holds if and only if
`z_q=0` and `Delta_z(b)=Delta_z(c)=1`. If their combined parity is p, these
conditions force a budget-preserving correction by b+c through (7).

**Proof.** Give each coordinate weight +1 outside supp(z) and -1 inside it.
Delta_z(b) is the sum of these signs over supp(b). Summing for b and c counts
their intersection twice, while b+c contains none of that intersection.
Subtracting twice its signed sum proves (9). Oddness and minimality imply
each increment is at least one and odd. This proves (10), the disjoint case,
and the one-point case, since then J is either +1 or -1. Conversely, an
outside intersection qubit and two increments of one make (9) zero.

**Concrete target consequence.** The odd stabilizers c_0 and c_5 have sum
`h_209={257,543}`, with `R(h_209)=e_0+e_5`. Consequently a weight-19 coset
minimum z with `R(z)=e_0+e_5` admits this particular repair exactly when
one of coordinates 257 and 543 is occupied. Two occupied coordinates would
contradict minimality, since adding h_209 would lower weight by two.
Under H_Z, one occupied coordinate is also impossible: this repair would
lift to a source logical of weight nineteen. Thus H_Z forces

```text
|z|=19, z coset-minimum nontrivial, R(z)=e_0+e_5
    implies z_257=z_543=0.                           (11)
```

This is a derived, explicit necessary boundary condition under the named
unproved hypothesis H_Z, not a new hypothesis or an assertion that such z
exists. It replaces one parity sector's unrestricted support by a two-qubit
exclusion. It does not exclude that entire sector.

### P9. Counterexample: even-weight parity surjectivity still does not force repair

**FALSE:** odd generators, an odd zero-parity stabilizer, and surjectivity
of `R(B_even)` together force weight-19 minimum representatives to have a
budget-preserving parity repair.

Here is an explicit CSS counterexample with an exact side-distance calculation.
Take 23 coordinates, numbered 1 through 23 for this example only. Define

```text
b={1,2,3},  c={4,5,6},  B=span{b,c},
z={1,4,7,8,...,23},     R(v)=v_1,
A=(span(B,z))^perp.
```

Then B is orthogonal to A by construction, the ranks are `dim B=2`,
`dim A=20`, and k=1. Since `A^perp=span(B,z)` and z is not in B (it has
spectator coordinates 7 through 23), all nontrivial Z representatives are
exactly z+B. The following four calculations describe this two-dimensional
coset symbolically; no computer enumeration or certificate is involved.

| Representative | Retained weight | R | Weight of its elementary graph lift |
| --- | --- | --- | --- |
| z | 19 | 1 | 20 |
| z+b | 20 | 0 | 20 |
| z+c | 20 | 1 | 21 |
| z+b+c | 21 | 0 | 21 |

**Proof.** Both disjoint weight-three generators meet z in one coordinate,
so each increment is one. Disjointness makes the combined increment two.
Only b toggles coordinate 1. These facts give the table. The retained Z
distance is therefore nineteen and z is its unique minimum. The elementary
extension with fan s=e_1 has Z distance twenty by its exact graph weight
formula. Yet c is odd with R(c)=0, and the even stabilizer b+c has R=1;
thus `R(B_even)=F2`. There is no equal-weight parity repair, and in fact
every odd-generator step here strictly increases the weight at z.

This is a counterexample about Z distance and correction. It makes no claim
that the X distance or the full quantum distance is nineteen or twenty.
It also is not a counterexample to the actual 566-qubit code.

### P10. Counterexample to the opposite claim: odd generators do not forbid repair

**FALSE:** if each odd generator strictly increases weight at a coset minimum,
then their sums cannot give an equal-weight parity repair.

Keep the same 23 coordinates, z, R, and b as in P9, but set
`c={3,4,5}`, `B=span{b,c}`, and again `A=(span(B,z))^perp`. The ranks and
nontrivial-coset argument are unchanged. Both generators are odd, each has
increment one, and their intersection is the single unoccupied qubit 3.
P8 therefore gives `Delta_z(b+c)=0`. Since `R(b+c)=1`, z+b+c has weight
nineteen and zero parity. The four retained weights are now `19,20,20,19`
and the parities remain `1,0,1,0`; hence z really is a coset minimum.
Its elementary source Z distance is nineteen because the last representative
lifts without growth, and every source Z lift has weight at least nineteen.

This calculation proves the claimed counterexample and explains the new
mechanism: the shared unoccupied coordinate pays for the two positive
individual increments. Odd generator weights alone neither force nor forbid
repair. For the target, the global parity obstruction is absent by P7, while
P8 supplies exact intersection conditions and the concrete boundary exclusion
(11). No claim is made that these consequences settle H_corr.

## 8. Final status and independent-review handoff

**STATUS: distance twenty is not established by this route.** H_X, H_Z,
and H_corr remain NAMED UNPROVED HYPOTHESES. P1–P10 retain PROPOSITION
status with independent review and formalization pending. The counterexamples
P5, P9, and P10 are preserved; none concerns the literal target's distance.
This investigation stops here for independent review.

**Exact blocked method family.** Arguments using only surjectivity of R on
stabilizers, surjectivity on even-weight stabilizers, and oddness of individual
generators cannot force a weight-nineteen repair. P9 satisfies all those
algebraic properties and still loses one unit of Z distance on removal.
Conversely, forbidding repair solely because each odd generator increases
weight is invalid by P10. The fixed correction C(p) is specifically unusable
at a weight-nineteen minimum whenever
`p_0+p_1+p_3+p_4+p_5=1`. These are limitations of these methods, not a
refutation of H_corr for the target.

**Exact unresolved target candidate family.** With the literal A,B,R, define

```text
F_19 = { z in A^perp minus B :
    |z|=19,
    Delta_z(b)>=0 for every b in B,
    p=R(z) is nonzero,
    Delta_z(b)>=2 for every b in B_even with R(b)=p }.
```

**PROPOSITION P11 (residual characterization; review/formalization pending).**
Among nontrivial weight-nineteen coset minima with nonzero R, F_19 is exactly
the family for which no stabilizer-corrected source lift has weight at most
nineteen. Indeed P7 requires an equal-weight even stabilizer of parity p.
For an even stabilizer Delta is an even nonnegative integer, so failure of
equality is exactly Delta>=2. Odd stabilizers have positive odd Delta and
cannot meet the budget. This proves the characterization. It neither proves
F_19 empty nor constructs a member. Under H_Z, every hypothetical
weight-nineteen target coset minimum must lie in F_19. In its sector
`p=e_0+e_5`, (11) additionally forces coordinates 257 and 543 to be zero.

Weights fourteen through eighteen remain unresolved as well: for each such
coset minimum of weight w, the obstruction is
`Delta_z(b)+|R(z+b)| >= 20-w` for every b in B. This is just the exact
negation of the correction budget, not a new bound. Source X and Z lower
bounds are separate outstanding tasks even if these target families are
eventually excluded.

**NEXT DIRECTION — research proposal, not a proved claim.** Use the literal
X-check cycle equations together with signed support overlaps, rather than
another parity right inverse. Start with the sector `R(z)=e_0+e_5` and the
forced zeros at 257 and 543. Propagate these constraints through the actual
boundary X rows and their adjacent bulk translates. The concrete desired
output is a finite symbolic implication: every cycle satisfying these
conditions and all stabilizer-minimum inequalities either belongs to B,
requires at least twenty occupied qubits, or admits an explicitly exhibited
even stabilizer b with R(b)=p and Delta_z(b)=0. Such an implication must
include its boundary conditions and prove completeness; checking a collection
of local pictures is insufficient. P8 supplies exact tests for overlapping
odd-row pairs, while zero-parity stabilizers permit further support changes.
This direction adds the spatial cycle constraints missing from P9. It has
not been executed or assumed to succeed, and the other parity sectors and
weights still need coverage.

For independent referees, the separable review units are P1–P6 (block algebra
and conditional transfer), P7–P8/P11 (parity and overlap obstructions), and
P5/P9/P10 (counterexamples). The source hashes and explicit row sums make the
data claims independently checkable without Lean or a distance search.

## 9. Validation scope

Read `AGENTS.md`, the lifting investigation and evaluation, the removal
evaluation, the qubit-removal/transport/sequence sources, `Boundary566.lean`,
the upstream notes, and the boundary builder's family conventions. A small
read-only Python 3.13 check verified the two input hashes, all literal deletion
identities, pair-row identities, the 196 X bulk translates, and the parity
images of the target Z generators. The proofs above use binary span algebra
and the explicit support tables, not any exhaustive certificate. Existing
kernel-check claims refer to the cited repository records, not a replay in
this work. The follow-up also directly checked the thirteen-qubit odd
zero-parity stabilizer k, the six even-weight repair images and weights,
and `c_0+c_5=h_209`. P9 and P10 are analytic four-representative coset
calculations, not computer certificates or searches. All derived results
remain PROPOSITION with independent review and formalization pending.
No assertion of mathematical novelty is made.
