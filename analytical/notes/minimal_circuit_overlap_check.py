"""Exact check-geometry identities; no errors, logicals, or cosets are searched.

Run with Python 3.13 and uv; see the companion minimal-circuit-overlap.md.
"""

from collections import Counter
from functools import reduce
from hashlib import sha256
from itertools import combinations
from operator import xor
from pathlib import Path

F = ((1, 0), (2, 0), (0, 2))
G = ((0, 0), (2, 1), (2, 2))


def check(a, b):
    return {
        (species, a + i, b + j)
        for species, offsets in (("A", F), ("B", G))
        for i, j in offsets
        if 0 <= a + i <= 18 and 0 <= b + j <= 18
    }


def chain_identity(checks, shared, weight):
    """Check the geometric hypotheses, from which the arbitrary-W formula follows."""
    assert all(len(c) == weight for c in checks)
    assert len(shared) == len(checks) - 1
    assert len(set(shared)) == len(shared)
    for i, j in combinations(range(len(checks)), 2):
        assert checks[i] & checks[j] == ({shared[i]} if j == i + 1 else set())
    total = reduce(xor, checks, set())
    incidence = Counter(q for c in checks for q in c)
    assert {q for q, n in incidence.items() if n == 2} == set(shared)
    assert all(n in (1, 2) for n in incidence.values())
    assert len(total) == weight * len(checks) - 2 * (len(checks) - 1)
    assert total == set(incidence) - set(shared)


def main():
    expected = Counter({6: 289, 3: 34, 4: 17, 2: 17})
    assert Counter(len(check(a, b)) for a in range(-2, 19) for b in range(17)) == expected
    assert Counter(len(check(a, b)) for a in range(17) for b in range(-2, 19)) == expected

    for t in range(17):
        boundary = [
            ((-2, t), {("A", 0, t), ("B", 0, t + 1), ("B", 0, t + 2)}),
            ((-1, t), {("A", 0, t), ("A", 1, t), ("B", 1, t + 1), ("B", 1, t + 2)}),
            ((17, t), {("A", 18, t), ("A", 17, t + 2), ("B", 17, t)}),
            ((18, t), {("A", 18, t + 2), ("B", 18, t)}),
            ((t, -2), {("A", t, 0), ("B", t + 2, 0)}),
            ((t, -1), {("A", t, 1), ("B", t + 2, 0), ("B", t + 2, 1)}),
            ((t, 17), {("A", t + 1, 17), ("A", t + 2, 17), ("B", t, 17), ("B", t + 2, 18)}),
            ((t, 18), {("A", t + 1, 18), ("A", t + 2, 18), ("B", t, 18)}),
        ]
        for anchor, support in boundary:
            assert check(*anchor) == support
        assert check(t, -1) ^ check(t, -2) == {("A", t, 0), ("A", t, 1), ("B", t + 2, 1)}
        if t >= 2:
            assert check(17, t) ^ check(18, t - 2) == {
                ("A", 17, t + 2),
                ("B", 17, t),
                ("B", 18, t - 2),
            }
    for i, j in combinations(range(17), 2):
        assert not check(18, i) & check(18, j)
        assert not check(i, -2) & check(j, -2)

    # All translations/lengths of five named check-chain families, not support search.
    families = 0
    for m in range(2, 18):
        for start in range(18 - m):
            for b in range(17):
                chain_identity(
                    [check(start + i, b) for i in range(m)],
                    [("A", start + i + 2, b) for i in range(m - 1)],
                    6,
                )
                families += 1
            for anchor, row, weight in ((-1, 1, 4), (-2, 0, 3)):
                chain_identity(
                    [check(anchor, start + i) for i in range(m)],
                    [("B", row, start + i + 2) for i in range(m - 1)],
                    weight,
                )
                families += 1
            for col, weight in ((17, 4), (18, 3)):
                chain_identity(
                    [check(start + i, col) for i in range(m)],
                    [("A", start + i + 2, col) for i in range(m - 1)],
                    weight,
                )
                families += 1

    for k, m, total_weight, overlap, drop in ((6, 3, 14, 9, 4), (4, 3, 8, 6, 4), (3, 5, 7, 5, 3)):
        assert k * m - 2 * (m - 1) == total_weight
        assert m * (k // 2) == overlap
        assert 2 * overlap - total_weight == drop
        assert all(w - drop < 17 for w in (17, 18, 19))

    # One fixed noncycle refutes only the local-inequality implication in the note.
    checks = [check(-2, i) for i in range(3)]
    support = {("A", 0, i) for i in range(3)}
    for c in checks:
        assert len(c) == 3 and len(c & support) == 1
    for c, d in combinations(checks, 2):
        assert 2 * len(support & (c ^ d)) <= len(c ^ d)
    total = reduce(xor, checks, set())
    assert len(total) == 5 and len(total & support) == 3
    # Actual Z(2,1): A positions are obtained from bar(g).
    z_a = {("A", 2 - i, 1 - j) for i, j in G if 0 <= 2 - i <= 18 and 0 <= 1 - j <= 18}
    assert len(z_a & support) == 1

    print(f"PASS: boundary table, cleaning sums, disjoint pairs, {families} check chains")
    print("PASS: three conditional weight-17/18/19 exclusions; fixed noncycle counterexample")
    print("No error/support search, distance certificate, or Lean execution.")
    root = Path(__file__).resolve().parents[2]
    for relative in (
        "analytical/rectangle722-distance17/PROOF.tex",
        "analytical/notes/minimal-circuit-overlap.md",
        "analytical/notes/minimal_circuit_overlap_check.py",
    ):
        print(f"sha256 {sha256((root / relative).read_bytes()).hexdigest()}  {relative}")


if __name__ == "__main__":
    main()
