# Minimum circuits and overlap cleaning in rectangle722

2026-11-11. Owned outputs: this note and `minimal_circuit_overlap_check.py`.
**PROPOSITION** throughout means a supplied mathematical proof with independent
review and formalization pending. **FALSE** marks an explicitly refuted shortcut.
Distance twenty remains **CONJECTURE**. No Lean execution, support search,
exhaustive error enumeration, or search certificate is used.

The concrete new exclusions are in Proposition 4: three saturated bulk checks,
three saturated weight-four boundary checks, or five saturated weight-three
boundary checks, with their shared qubits absent, cannot occur in a nontrivial
logical of weight 17, 18, or 19. These are exclusions of specified configurations
at each weight, **not exclusions of the entire three weight levels**. Proposition
5 gives additional boundary forbidden pairs and a weight-preserving normal form.

## Model and dependency boundary

Read root `AGENTS.md` and the explicit model, charge results, and lower bound in
[`rectangle722-distance17/PROOF.typ`](../rectangle722-distance17/PROOF.typ).
The only imported distance statement used below is its bound that every
nontrivial sector logical has weight at least 17. The overlap identities and
normal forms do not need that bound. No assertion about a submitted JSON is used.

Coordinates are A(i,j), B(i,j), with 0 <= i,j <= 18. Put
f = x + x² + y² and g = 1 + x²y + x²y². Write C(a,b) for the support of
T(x^a y^b(f,g)). Explicitly, before deleting off-board coordinates it is

```
A(a+1,b), A(a+2,b), A(a,b+2),
B(a,b),   B(a+2,b+1), B(a+2,b+2).
```

For X, allowed anchors are -2 <= a <= 18, 0 <= b <= 16. For Z we use the
coordinate permutation M(A(i,j)) = B(18-i,18-j), and conversely for B.
The reflected Z stabilizers, denoted Z', are C(a,b) with 0 <= a <= 16,
-2 <= b <= 18. This transports the Z sector, **not** an assertion that M is
an X/Z symmetry. All statements for Z' return to Z by applying M again.

Here are all boundary supports. Unlisted anchors are bulk checks of weight six.

| Sector | Anchor | Retained support | Weight |
| --- | --- | --- | --- |
| X | (-2,b) | A(0,b), B(0,b+1), B(0,b+2) | 3 |
| X | (-1,b) | A(0,b), A(1,b), B(1,b+1), B(1,b+2) | 4 |
| X | (17,b) | A(18,b), A(17,b+2), B(17,b) | 3 |
| X | (18,b) | A(18,b+2), B(18,b) | 2 |
| Z' | (a,-2) | A(a,0), B(a+2,0) | 2 |
| Z' | (a,-1) | A(a,1), B(a+2,0), B(a+2,1) | 3 |
| Z' | (a,17) | A(a+1,17), A(a+2,17), B(a,17), B(a+2,18) | 4 |
| Z' | (a,18) | A(a+1,18), A(a+2,18), B(a,18) | 3 |

The free boundary anchor ranges from 0 to 16. Each sector has 289 weight-six,
34 weight-three, 17 weight-four, and 17 weight-two checks.

## Proposition 1: which minima are circuits?

For a fixed sector let S be the same-sector stabilizer space and K the
opposite-check kernel. A **coset minimum** minimizes weight in one fixed
nonzero class of K/S. A **sector minimum** minimizes over all of K minus S.

Every sector minimum w is a support circuit: no nonempty proper subset of its
support is a cycle. Indeed, suppose v is such a subset cycle. If v is not in S,
it is a smaller nontrivial cycle. If v is in S, then w+v is a smaller member of
the same nonzero coset. Both contradict minimality. More generally, a smallest
nontrivial cycle contained in any given nontrivial cycle support is a circuit,
by exactly the same two-case proof.

A coset minimum only rules out the second case. A smaller logical subset can
have a different nonzero class, so circuit minimality must not be inferred from
coset minimality alone. An arbitrary representative has neither property.
The generic definition `IsCircuit` and argument `exists_detected_circuit` in
`lean/QldpcVerification/IrreducibleSearchSoundness.lean` use this same distinction;
they were read as source only, not run or used as an executable search.

## Proposition 2: slack for a stabilizer sum

Identify binary vectors with supports; addition is symmetric difference.
For any support W and same-sector stabilizer support D, define

```
delta_W(D) = |D| - 2|W intersect D|.
|W xor D| = |W| + delta_W(D).
```

For a coset minimum, delta_W(D) >= 0 for **every** D in S, not just a
generating check. Individual bulk, weight-four, weight-three, and weight-two
checks therefore have intersection caps 3, 2, 1, and 1, respectively.
These caps are not assertions about every representative.

For two check supports D,E, coefficient counting gives the stronger identity

```
delta_W(D xor E)
  = delta_W(D) + delta_W(E)
    - 2|D intersect E| + 4|W intersect D intersect E|.       (1)
```

In particular, if their unique shared qubit is absent, the two slacks must
sum to at least two in a coset minimum. Two tight even checks (slack zero)
are impossible in this situation. A tight even and a tight odd check
(slacks zero and one) are also impossible. Two tight odd checks survive this
pair test; longer sums are essential below. If the shared qubit is present,
(1) imposes no additional restriction beyond the individual nonnegative slacks.

## Proposition 3: exact chain cleaning

Suppose D_0,...,D_(m-1) are same-sector checks of a common weight k. Consecutive
checks meet in a single qubit q_i, all q_i are distinct, and nonconsecutive
checks are disjoint. Let h_i = |W intersect D_i| and
r = number of q_i in W. For D = D_0 xor ... xor D_(m-1),

```
|D| = km - 2(m-1),
|W intersect D| = sum_i h_i - 2r,
|W| - |W xor D| = 2 sum_i h_i - km + 2(m-1) - 4r.         (2)
```

Proof: each shared site occurs twice and disappears in D; every other site
occurs once. The same count applied only to sites in W proves the second
identity. Subtract twice that identity from the first. No cycle assumption
on W is needed for (2). If W is a cycle, W xor D is in the same logical class.

Write e_i = floor(k/2) - h_i. For a coset minimum e_i >= 0. Its exact necessary
chain inequalities are

```
sum_i e_i + 2r >= m-1          (k even),
2 sum_i e_i + 4r >= m-2        (k odd).                    (3)
```

These are **single combined-stabilizer inequalities**. Adding reductions from
overlapping chains is not justified: their cancelled and occupied sites can
coincide. We only apply (2) to one explicitly specified sum at a time.

The following actual rectangle chains satisfy all the hypotheses:

| Sector | D_i, 0 <= i < m | Shared q_i | k | Anchor condition |
| --- | --- | --- | --- | --- |
| X or Z' | C(a+i,b) | A(a+i+2,b) | 6 | 0 <= a, a+m-1 <= 16; 0 <= b <= 16 |
| X | C(-1,b+i) | B(1,b+i+2) | 4 | 0 <= b, b+m-1 <= 16 |
| X | C(-2,b+i) | B(0,b+i+2) | 3 | same |
| Z' | C(a+i,17) | A(a+i+2,17) | 4 | 0 <= a, a+m-1 <= 16 |
| Z' | C(a+i,18) | A(a+i+2,18) | 3 | same |

To check the table by hand, the bulk A positions at column b have consecutive
rows a+1,a+2; the third A lies at column b+2. Bulk B positions at different
anchors in this chain cannot coincide, since equal rows would require their
columns b and b+1 or b+2 to coincide. Thus only neighboring A positions meet.
For X boundary chains only the displayed two consecutive B positions meet;
for Z' boundary chains only the two consecutive A positions meet.
This also proves nonconsecutive disjointness, including both ends of the board.

## Proposition 4: explicit exclusions at weights 17, 18, 19

Call a chain saturated when every h_i = floor(k/2), and suppose all its shared
q_i are absent from W (r=0). These hypotheses specify actual physical overlap
patterns, rather than scalar strip weights. Equation (2) gives:

| Pattern from the preceding table | Weight of D | Overlap with D | Exact drop |
| --- | --- | --- | --- |
| Three bulk checks, each with three occupied sites | 14 | 9 | 4 |
| Three weight-four boundary checks, each with two occupied sites | 8 | 6 | 4 |
| Five weight-three boundary checks, each with one occupied site | 7 | 5 | 3 |

If a nontrivial cycle W had weight 17, 18, or 19 and any one of these patterns,
then W xor D would be a nontrivial cycle of weight at most 16, contradicting
the imported lower bound of 17. Thus all three configurations are excluded
at **each** of those three weights, for every representative. The first two
also exclude weight 20 with their specified patterns.

Smaller patterns give additional graded exclusions: two saturated even checks
with shared site absent reduce by two, excluding weights 17 and 18; three or
four saturated weight-three boundary checks with all shared sites absent
reduce by one or two, excluding weight 17 or weights 17 and 18, respectively.
For coset minima all these positive-drop patterns are excluded at every weight,
without importing the distance-17 theorem.

More generally, for any nontrivial representative of weight W <= 19, (2) and
the lower bound give the useful numerical constraints

```
2 sum_i h_i - km + 2(m-1) - 4r <= W-17.                  (4)
```

Thus the permissible drop budgets at weights 17,18,19 are precisely 0,1,2.
One must not replace those budgets by zero unless W is known to be a coset
minimum. In particular a nonminimal weight-19 representative could allow a
two-qubit reduction to a weight-17 representative. This note has not shown
that such representatives exist or that any of the forbidden motifs must occur.

## Proposition 5: weight-two boundary cleaning and new forbidden pairs

The X weight-two checks P_b = C(18,b), 0 <= b <= 16, are pairwise disjoint.
Each contains A(18,b+2), B(18,b). In a coset minimum they cannot both be
occupied. If only B is occupied, add P_b to move that occupation to A at equal
weight. Consequently every nonzero coset has a minimum with

```
B(18,b) absent for every 0 <= b <= 16.                    (5)
```

These moves are simultaneous and disjoint, so this is a proved normal form,
not an assumption that a greedy reduction finds a global minimum. Start with
an already attained coset minimum. Its weight and logical class are unchanged.
If it was a sector minimum, the result remains a sector minimum and therefore
remains a circuit by Proposition 1. Other boundary coordinates are not cleaned
by (5).

For 2 <= b <= 16, the sum C(17,b) xor P_(b-2) is the weight-three stabilizer

```
{ A(17,b+2), B(17,b), B(18,b-2) }.                        (6)
```

The sole cancelled site is A(18,b). Therefore **every coset minimum**, even
without choosing (5), has at most one of the three sites in (6). In particular
it cannot contain B(18,b-2) together with either A(17,b+2) or B(17,b).
Those are cross-generator forbidden pairs; the pair A(17,b+2), B(17,b)
was already forbidden by C(17,b) alone. The restriction b >= 2 matters:
P_(b-2) is not an allowed check for b=0 or 1. These two exceptional columns
must not be silently removed. This forbidden pair is stronger than merely
checking the original two generators separately.

In Z', the weight-two checks P_a = C(a,-2) are also pairwise disjoint. The
corresponding normal form removes B(a+2,0) for all 0 <= a <= 16 by transferring
it to A(a,0). The sum C(a,-1) xor P_a has weight-three support

```
{ A(a,0), A(a,1), B(a+2,1) }.                            (7)
```

Every Z' coset minimum has at most one site in (7). For example it cannot have
both A(a,0) and A(a,1), a condition not implied by the two separate check caps.
The conclusions for original Z follow by the explicit inverse permutation M;
there is no need to infer a corresponding X statement by symmetry.

## A precise shortcut that fails

**FALSE:** for these boundary chains, satisfying all single-check and all
two-check-sum overlap inequalities guarantees the overlap inequality for the
whole chain. Take the three X checks C(-2,b), C(-2,b+1), C(-2,b+2), with
0 <= b <= 14, and the fixed physical support

```
W = {A(0,b), A(0,b+1), A(0,b+2)}.
```

Each individual overlap is one out of three. Neighboring pair sums have
weight four and overlap two; the nonneighboring sum has weight six and overlap
two. All these inequalities pass. The triple sum has weight five and overlap
three, violating minimality and reducing weight by one. The script checks
this fixed identity. W is **not a cycle**: the retained Z check at (2,b+1)
has odd overlap with W. Thus this is a counterexample to the claimed implication
between local inequalities, not a claimed logical, circuit, or globally
single-check-stable trap. No stronger counterexample is being inferred.

## What remains, and validation

To prove distance twenty by this route it suffices to consider a sector
minimum of weight at most 19: it is a circuit, obeys every combined-stabilizer
inequality, and can be put in the appropriate boundary normal form above.
The unresolved task is to force a forbidden overlap pattern (or some other
positive-drop stabilizer sum) using its opposite-check cycle equations.
Circuit connectivity and the individual overlap caps alone have not supplied
that implication. No claim that all short cycles are boundaries is assumed.

The companion script uses exact finite support identities for the stated
check formulas, boundary table, chain intersections, and one fixed noncycle
counterexample. It enumerates check geometry, **not errors, logicals, cosets,
or candidate supports**. Its arithmetic checks supplement the proofs here;
they are not a distance certificate or Lean verification. Run from the root:

```
UV_CACHE_DIR=/tmp/qldpc-minimal-circuit-uv uv run --offline --locked --python 3.13 \
  python analytical/notes/minimal_circuit_overlap_check.py
```

Independent mathematical review and formalization remain pending for all new
propositions. Only the two owned outputs were changed.

Validation on 2026-11-11: Python 3.13 exact checks passed for all 2,856 translated
chains in the five specified families, the boundary table, the cleaning sums,
and the fixed noncycle example. Ruff lint and formatting checks passed for the
owned script. The script prints SHA-256 hashes of itself, this note, and its
model source. The model source read for this work had SHA-256
`6dcccb32f1b11e0c2eae81ace1e94c0f995971daeac73b39a66f2b09bff80cab`.
