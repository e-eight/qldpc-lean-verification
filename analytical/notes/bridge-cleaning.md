# Repeated-center bridges: what local cleaning actually proves

2026-11-11. **All results here are unreviewed PROPOSITION**, with independent
review and formalization pending. Only this file is owned and changed.

**Result.** Minimum-weight cleaning deletes a repeated center's entire middle
network, but it need not give a profitable exchange of the two remaining bridge
qubits. For a mixed-species bridge pair in an allowed weight-six check, the
exact weight change is **2 minus twice the number of other occupied check
sites**. The bridge condition does not force that number to be positive.
The existing weight-20 Z witness is an explicit nontrivial **support circuit**
with two such double bridges and zero additional occupation in either natural
check patch. Every nonzero stabilizer confined to the union of those patches
strictly increases its weight, not merely the two generating checks separately.

This is a counterexample to the proposed **patch-local** reduction from a
double bridge. It is **not** a proof that this witness is a global coset minimum,
nor a counterexample of weight below 20. Thus the global assertion that a
sector minimum below 20 cannot have repeated centers remains unresolved.
In particular the residual families in charge-factors Propositions 18–21
cannot yet be replaced by the already bounded path cases using this shortcut.

## Definitions and input boundary

Read root `AGENTS.md`,
[`charge-factors.md`](charge-factors.md), especially Propositions 3, 7, 11,
14, and 18–21, and [`minimal-circuit-overlap.md`](minimal-circuit-overlap.md).
The matrices are exactly those in
[`rectangle722-distance17/PROOF.typ`](../rectangle722-distance17/PROOF.typ).
No JSON recognition is assumed. No Lean execution or support search is used.

Work in X coordinates or reflected-Z coordinates Z'. The physical sites are
A(i,j), B(i,j), 0 <= i,j <= 18, and their full syndrome hyperedges are

```
V(A(i,j)) = {(i,j), (i+2,j+1), (i+2,j+2)},
V(B(i,j)) = {(i+1,j), (i+2,j), (i,j+2)}.
```

Put F={(1,0),(2,0),(0,2)} and G={(0,0),(2,1),(2,2)}. A stabilizer check
C(h), with h=(a,b), consists of A(h+F) and B(h+G), cropped to the physical
board. Allowed X anchors are [-2,18] x [0,16]; allowed Z' anchors are
[0,16] x [-2,18]. Tested syndrome vertices have row in [2,18] for X and
column in [2,18] for Z'. All other syndrome vertices are on the two wired
boundaries. Full syndrome vertices are never cropped out of the graph.

A bridge is an occupied **qubit node** whose deletion separates the wired
boundaries S and T. Its center is the unique vertex on the singleton side
of its one-versus-two syndrome split, as in charge-factors Proposition 11.
A coset minimum minimizes one fixed nonzero class. A sector minimum minimizes
over all nonzero classes and is a support circuit. A general coset minimum
need not be a circuit. These distinctions will be kept throughout.

## Proposition 1: the repeated-center middle contains no occupied qubits at a minimum

Let e,f be successive bridges with the same center v. In the decomposition
obtained by deleting e,f, let L contain S, R contain T, and M be the middle
network. Then

```
V(e) intersect M = V(f) intersect M = {v}.
```

Indeed f and all its incident vertices are on the T side after deleting e;
otherwise a path through f would bypass e. Since v is incident to f and is
e's singleton, it is the singleton on that T side. Similarly it is f's
singleton on the S side. The other two vertices of e are in L and the other
two vertices of f are in R. Every middle component touches both bridges by
the layer lemma, so there is just the component containing v.

Let U be the occupied qubits in M. It contains no boundary vertex. At a
syndrome vertex other than v, U receives no contribution from e,f or the
outside components. Its syndrome there is consequently zero. At v, the
contributions from e and f cancel, so U's syndrome is zero there too. Thus
U has **zero full polynomial syndrome**, not just zero tested syndrome.
Bulk exactness for the explicit model makes U a same-sector stabilizer:
U=(fh,gh), with h supported in [0,16]^2. This is allowed in both X and Z'.

If W is a coset minimum, U must be empty, since removing this contained
stabilizer would reduce weight by |U|. A support circuit also forces U empty,
because U would be a proper nonempty cycle subset. In particular, at such a
minimum **v is incident to exactly the two occupied qubits e,f**.

This proves a genuine cleaning statement. It removes an attached zero-syndrome
network, not the two-qubit connection e–v–f itself. The empty middle has zero
layer cost; circuit minimality does not turn it into a positive-cost layer.

## Proposition 2: exact common-check exchange, including its limitations

Suppose e=A(v-g_j) and f=B(v-f_i) have the same center v, for g_j in G and
f_i in F. Their unique possible common generator has anchor

```
h = v - f_i - g_j,
e = A(h+f_i),  f = B(h+g_j).                              (1)
```

The anchor must be allowed in the relevant sector. The mere fact that both
qubits are on the physical board does not establish this: transverse cropping
can place h outside the allowed anchor rectangle. If the pair has the same
species, there is no common generator. Indeed differences between two F
positions are, up to sign, (1,0),(1,-2),(2,-2), whereas differences between
two G positions are (2,1),(2,2),(0,1); the lists are disjoint.

When C=C(h) is allowed, put k=|C| and
t=|W intersect (C minus {e,f})|. For every representative W containing e,f,

```
|W xor C| - |W| = k - 4 - 2t.                            (2)
```

There is also a graph restriction: the extra occupied sites cannot include
both an A site and a B site. To prove it, suppose A(h+f_k) and B(h+g_l) are
occupied, k != i and l != j. The former shares the noncenter vertex
h+f_k+g_j with f, hence is in R after e,f are removed. The latter shares
h+f_i+g_l with e, hence is in L. But they share h+f_k+g_l, connecting L
to R without e or f, a contradiction. All nine positions h+F+G are distinct:

```
          g_0=(0,0)   g_1=(2,1)   g_2=(2,2)
f_0=(1,0)    (1,0)       (3,1)       (3,2)
f_1=(2,0)    (2,0)       (4,1)       (4,2)
f_2=(0,2)    (0,2)       (2,3)       (2,4)
```

Coordinates in the table are relative to h. Boundary wiring cannot invalidate
the exhibited bypass. Consequently t <= 2, all on one species, and (2) gives:

| Allowed common-check weight | Necessary condition at a coset minimum | Exchange |
| --- | --- | --- |
| 2 or 3 | impossible: e,f alone exceed half the check | strictly reducing |
| 4 | t=0 | weight-preserving |
| 6 | t=0 or 1 | increase by 2, or preserve weight |

For a bulk check t=2 gives a reduction of exactly two and is therefore
impossible at a minimum. With the independent lower bound 17 it is also
impossible for **any** nontrivial representative of weight 17 or 18, but it
does not by itself exclude a weight-19 representative reducing to weight 17.
There is no reduction in the surviving bulk t=0 case.

Even a weight-preserving swap only shows that another minimum exists. It
does not prove that the number of bridges decreases: the outside attachment
sets change, and new separating qubits may appear. A separate invariant
would be needed before iterating such swaps to invoke the disjoint-path bound.

## Proposition 3: an explicit circuit with two uncleanable local double bridges

Use Z' and label the following 20 occupied qubits by 0 through 19:

| Label | Qubit | Label | Qubit |
| --- | --- | --- | --- |
| 0 | A(10,5) | 10 | B(11,1) |
| 1 | A(12,6) | 11 | B(12,1) |
| 2 | A(12,7) | 12 | B(13,16) |
| 3 | A(13,18) | 13 | B(14,14) |
| 4 | A(14,7) | 14 | B(15,9) |
| 5 | A(14,9) | 15 | B(15,10) |
| 6 | A(15,11) | 16 | B(15,12) |
| 7 | A(15,12) | 17 | B(15,14) |
| 8 | A(16,8) | 18 | B(16,9) |
| 9 | B(10,3) | 19 | B(16,10) |

This is the already supplied Z witness from `scripts/check_rectangle722_witness.py`,
under M(A(i,j))=B(18-i,18-j) and M(B(i,j))=A(18-i,18-j). Its original physical
labels are

```
46,47,61,63,65,66,80,97,131,150,167,
409,424,425,446,448,456,486,487,526.
```

It was taken as fixed input, not found by a support search for this note.

### Cycle, charge, and support circuit

Direct multiplication gives full syndrome

```
x^12 y + x^14 y + x^15 y^19 + x^15 y^20.                 (3)
```

Only columns 1,19,20 occur, so this is a Z' cycle. Its low-column charge is
rho(x^12 y(1+x^2))=rho(x^10 y^5), since f=0 gives
y^4=x^2+x^4. The latter is a unit monomial in the charge algebra, nonzero
in both field factors. Charge completeness makes the cycle nontrivial.

Here is the **complete** tested incidence table. Each listed syndrome vertex
has exactly the two indicated occupied qubits, and there are no other occupied
tested syndrome vertices:

```
(10,5): 0,9    (11,3): 9,10   (12,3): 9,11
(12,6): 0,1    (12,7): 0,2    (13,18): 3,12
(14,7): 1,4    (14,8): 1,2    (14,9): 2,5
(14,16): 12,13 (15,11): 6,14  (15,12): 7,15
(15,14): 13,16 (15,16): 12,17 (16,8): 4,8
(16,9): 4,14   (16,10): 5,15  (16,11): 5,18
(16,12): 16,19 (16,14): 13,17 (17,9): 14,18
(17,10): 15,19 (17,12): 6,16  (17,13): 6,7
(17,14): 7,17  (18,9): 8,18   (18,10): 8,19
```

The boundary incidences are (12,1):10, (13,1):10,11, (14,1):11,
(15,19):3, and (15,20):3. The table accounts for all 60 incidences.
For a cycle subset of this support, each tested row equates the membership
bits of its two qubits. The displayed pair graph is connected, so all 20
membership bits agree. Hence the only cycle subsets are empty and the whole
support. This proves the circuit property without enumerating subsets.

### The actual repeated centers

Wire columns 0,1 to S and 19,20 to T. The pairs are

```
(9,0)  = (B(10,3), A(10,5)),   center v=(10,5),
(12,3) = (B(13,16), A(13,18)), center w=(13,18).           (4)
```

The pair-incidence table gives a short hand check of separation. For the
first pair, deleting 9 and 0 leaves qubits {10,11} with S, the remaining
16 qubits with T, and v isolated. Restoring either one alone still cannot
connect S to T; restoring both does. The two noncenter vertices of qubit 9
are (11,3),(12,3), in the low component; those of qubit 0 are (12,6),(12,7),
in the high component. Thus both have singleton center v.

For the second pair, deleting 12 and 3 leaves all other 18 qubits with S,
T connected to the boundary vertices but no occupied qubit, and w isolated.
Qubit 12 has noncenter vertices (14,16),(15,16), in the low component;
qubit 3 has (15,19),(15,20), wired to T. Again both are bridges with center w.
The table also checks that the other qubits are not separating nodes.

In the normalized Z coordinates used in charge-factors Proposition 21, the
centers are (20-18,13)=(2,13) and (20-5,10)=(15,10), in that order. Their
displacement is (13,-3), and the lower row is 2. Thus this is exactly the
geometry of its four-bridge family, at weight **20**, not below its threshold.

### Exact obstruction to local cleanup

The common stabilizer patches for (4) are D=C(10,3) and E=C(13,16). Both
are allowed weight-six Z' checks. Their supports and occupations are

```
D occupied: A(10,5), B(10,3)
D absent:   A(11,3), A(12,3), B(12,4), B(12,5)

E occupied: A(13,18), B(13,16)
E absent:   A(14,16), A(15,16), B(15,17), B(15,18).
```

The patches are disjoint. Adding D or E raises weight from 20 to 22;
adding both raises it to 24. This is not just a generator-level observation:

**Every tested-syndrome-zero vector supported in D union E is one of
0, D, E, D xor E.** To prove this, on a full check the nine vertices in the
table h+F+G impose equations alpha_i=beta_j on the six possible physical
coefficients. For D every one of those vertices is tested, giving the
connected K(3,3) system. For E the only untested ones are (15,19),(15,20),
the entries (f_2,g_1),(f_2,g_2). Removing those two equations leaves the
system connected: beta_0 joins all three alpha_i, and alpha_0 joins the
other two beta_j. In either patch all six coefficients must agree.
The two patches have disjoint full syndrome ranges, columns [3,7] and [16,20],
so no equation can cancel a contribution from one against the other. This
proves the assertion. D and E are themselves stabilizers.

Consequently W is a **strict minimum with its outside-of-(D union E) support
fixed**, even allowing every stabilizer combination supported in that union.
It is also a support circuit. Neither fact asserts unrestricted coset minimality.
Any profitable stabilizer cleanup of this witness must change a qubit outside
those two natural patches. This is the precise scope of the counterexample.

As a supplementary fixed arithmetic check, all 357 Z' generators individually
have nonnegative slack on this witness. The slack histogram is
{0:1, 1:4, 2:27, 3:30, 4:50, 6:245}. This rules out even a different
single-generator strict reduction. It does **not** rule out a combination
of generators extending outside the patches.

## Consequence for the residual problem

Proposition 1 justifies replacing a repeated-center middle by the bare
two-qubit connection when studying a minimum. Proposition 2 excludes any
mixed pair whose allowed common check has weight two or three, and gives
precise conditional reductions for the remaining check weights. However,
the bulk case with no additional occupied check site survives both circuit
minimality and every stabilizer perturbation in its natural patch. The fixed
circuit above realizes this obstruction at both centers simultaneously.

To exclude all residual W<20 families, a new argument must force additional
occupation outside these patches, force a profitable larger stabilizer sum,
or control how a weight-preserving exchange changes all bridge layers.
The existing circuit and overlap inequalities do not yet do any of these.
No inference of global coset minimality from absence of local reductions is made.

## Reproducible fixed-identity check (embedded; no second owned file)

The following standard-library Python checks the **one supplied support**,
its complete syndrome, the connected degree-two incidence relations, its
four bridge deletions, and the two check identities. Iterating over nodes of
this fixed graph and over the 357 specified generators is not a search over
supports, errors, logical classes, or stabilizer combinations. The patch-kernel
argument above is the proof for all combinations; no combination enumeration
is used. Save or execute the block with Python 3.13 if desired.

```python
from collections import Counter, defaultdict

F = ((1, 0), (2, 0), (0, 2))
G = ((0, 0), (2, 1), (2, 2))
W = [
    ("A", 10, 5), ("A", 12, 6), ("A", 12, 7), ("A", 13, 18),
    ("A", 14, 7), ("A", 14, 9), ("A", 15, 11), ("A", 15, 12),
    ("A", 16, 8), ("B", 10, 3), ("B", 11, 1), ("B", 12, 1),
    ("B", 13, 16), ("B", 14, 14), ("B", 15, 9), ("B", 15, 10),
    ("B", 15, 12), ("B", 15, 14), ("B", 16, 9), ("B", 16, 10),
]
assert len(set(W)) == 20
edges = {
    k: {(i + a, j + b) for a, b in (G if s == "A" else F)}
    for k, (s, i, j) in enumerate(W)
}
inc = defaultdict(set)
for k, vertices in edges.items():
    for v in vertices:
        inc[v].add(k)
assert {v for v, ks in inc.items() if len(ks) % 2} == {
    (12, 1), (14, 1), (15, 19), (15, 20)
}
tested = {v: ks for v, ks in inc.items() if 2 <= v[1] <= 18}
assert len(tested) == 27 and all(len(ks) == 2 for ks in tested.values())


def component(graph, start):
    seen, todo = {start}, [start]
    while todo:
        for q in graph.get(todo.pop(), ()):
            if q not in seen:
                seen.add(q)
                todo.append(q)
    return seen


pair_graph = defaultdict(set)
for ks in tested.values():
    a, b = sorted(ks)
    pair_graph[a].add(b)
    pair_graph[b].add(a)
assert component(pair_graph, 0) == set(range(20))


def wired_graph(deleted):
    graph = defaultdict(set)

    def link(a, b):
        graph[a].add(b)
        graph[b].add(a)

    for v in inc:
        node = ("v",) + v
        graph[node]  # Keep isolated centers after deleting their two qubits.
        if v[1] <= 1:
            link("S", node)
        if v[1] >= 19:
            link("T", node)
    for k, vertices in edges.items():
        if k not in deleted:
            for v in vertices:
                link(k, ("v",) + v)
    return graph


bridges = {}
for k in range(20):
    low = component(wired_graph({k}), "S")
    if "T" not in low:
        left = {v for v in edges[k] if ("v",) + v in low}
        right = edges[k] - left
        assert sorted((len(left), len(right))) == [1, 2]
        bridges[k] = next(iter(left if len(left) == 1 else right))
assert bridges == {0: (10, 5), 9: (10, 5), 3: (13, 18), 12: (13, 18)}
for pair, center, low_ids in (
    ({0, 9}, (10, 5), {10, 11}),
    ({3, 12}, (13, 18), set(range(20)) - {3, 12}),
):
    graph = wired_graph(pair)
    assert not graph[("v",) + center]
    low = component(graph, "S")
    assert {q for q in low if isinstance(q, int)} == low_ids
    assert "T" not in low


def check(a, b):
    return {
        (s, a + i, b + j)
        for s, offsets in (("A", F), ("B", G))
        for i, j in offsets
        if 0 <= a + i <= 18 and 0 <= b + j <= 18
    }


patches = [check(10, 3), check(13, 16)]
assert not patches[0] & patches[1]
for patch, pair in zip(patches, ({0, 9}, {3, 12}), strict=True):
    assert len(patch) == 6 and patch & set(W) == {W[k] for k in pair}
    assert len(set(W) ^ patch) == 22
assert len(set(W) ^ patches[0] ^ patches[1]) == 24
slacks = Counter(
    len(c) - 2 * len(c & set(W))
    for a in range(17)
    for b in range(-2, 19)
    for c in [check(a, b)]
)
assert slacks == Counter({0: 1, 1: 4, 2: 27, 3: 30, 4: 50, 6: 245})
print("PASS: fixed nontrivial-cycle syndrome, circuit incidences, four bridges,")
print("      patch overlaps and all generating-check slacks; no support search.")
```

Validation: the embedded block passed under Python 3.13. Mathematical
nontriviality uses the displayed charge identity and charge completeness;
the script does not replace those arguments or claim global minimum weight.
No Lean run or axiom audit was performed, and no Lean files were edited.
The source snapshots read for this task had SHA-256 values:

```
charge-factors.md:
c49d65877a551d0d34ea7eac28ec3d130e71110eb362881234351e54704f1a30
minimal-circuit-overlap.md:
26da78bcb8cd3d7e1b9df9911f1f75a89c7e8436c936503f4671ffa9a997fb67
rectangle722-distance17/PROOF.typ:
6dcccb32f1b11e0c2eae81ace1e94c0f995971daeac73b39a66f2b09bff80cab
scripts/check_rectangle722_witness.py:
716f7af2875ca7d0ff206257122783a54857d7739c3c74072aa9ddbfaa56a1a5
```

Concurrent changes to those source files are outside this note's ownership.
