"""Diagnostic arithmetic only for DRAFT.tex; no candidate/vector search.

Each assertion compares printed integers or finite polynomial products.
Run with: python3 analytical/rectangle722-submitted/referee_2_check.py
Only DRAFT.tex is read. No output files are created.
"""

import re
from collections import Counter
from pathlib import Path

text = re.sub(r"\\\((-?\d+|[CR])\\\)", r"\1", Path(__file__).with_name("DRAFT.tex").read_text())


def pairs(s):
    return [tuple(map(int, p)) for p in re.findall(r"\((-?\d+), (-?\d+)\)", s)]


def ints(s):
    return list(map(int, re.findall(r"-?\d+", s)))


f = [(1, 0), (2, 0), (0, 2)]
g = [(0, 0), (2, 1), (2, 2)]
matrices = {}
appendix = text.split("\\section{Complete numerical support matrices}")[1]
for sector, divisor in [("X", 17), ("Z", 21)]:
    section = appendix.split(f"\\subsection{{{sector} supports}}")[1].split("\\subsection")[0]
    rows = re.findall(r"^  (\d+) & \((-?\d+), (-?\d+)\) & ([\d, ]+) \\\\$", section, re.M)
    assert len(rows) == 357, (sector, len(rows))
    matrices[sector] = []
    counts = Counter()
    for position, (r, i, j, support) in enumerate(rows):
        r, i, j = int(r), int(i), int(j)
        assert r == position
        a, b = divmod(r, divisor)
        assert (i, j) == ((a - 2, b) if sector == "X" else (a + 2, b))
        actual = ints(support)
        assert actual == sorted(set(actual))
        assert all(0 <= q < 722 for q in actual)
        offsets = (f, g) if sector == "X" else (g, f)
        sign = 1 if sector == "X" else -1
        direct = sorted(
            361 * block + 19 * (i + sign * di) + j + sign * dj
            for block, terms in enumerate(offsets)
            for di, dj in terms
            if 0 <= i + sign * di <= 18 and 0 <= j + sign * dj <= 18
        )
        if sector == "X":
            U = 19 * a + b
            if a == 0:
                case, formula = 0, [b, b + 362, b + 363]
            elif a == 1:
                case, formula = 1, [b, b + 19, b + 381, b + 382]
            elif a <= 18:
                case, formula = 2, [U - 36, U - 19, U, U + 323, U + 362, U + 363]
            elif a == 19:
                case, formula = 3, [b + 325, b + 342, b + 684]
            else:
                case, formula = 4, [b + 344, b + 703]
        else:
            U = 19 * a + b
            if b == 0:
                case, formula = 0, [19 * a + 38, 19 * a + 361, 19 * a + 380]
            elif b == 1:
                case, formula = 1, [19 * a, 19 * a + 39, 19 * a + 362, 19 * a + 381]
            elif b <= 18:
                case, formula = 2, [U - 2, U - 1, U + 38, U + 361, U + 380, U + 397]
            elif b == 19:
                case, formula = 3, [19 * a + 17, 19 * a + 18, 19 * a + 416]
            else:
                case, formula = 4, [19 * a + 18, 19 * a + 417]
        assert actual == formula == direct, (sector, r, actual, formula, direct)
        counts[case] += 1
        matrices[sector].append(set(actual))
    print(sector, "357 ordered rows: exact clipping and five-case identity PASS;", dict(counts))

witnesses = {}
for sector, n in [("X", 23), ("Z", 20)]:
    support = ints(text.split(f"{sector} support ({n} distinct qubits):")[1].split("\n\n")[1])
    assert len(support) == len(set(support)) == n
    witnesses[sector] = set(support)
    section = re.split(r"\\(?:sub)*section\{", text.split(f"{sector} multiplication}}")[1])[0]
    rows = re.findall(r"^  (\d+) & ([AB])\((\d+), (\d+)\) & (.*?) \\\\$", section, re.M)
    assert [int(row[0]) for row in rows] == support
    products = Counter()
    for q, block, i, j, terms in rows:
        q, i, j = int(q), int(i), int(j)
        assert q == 361 * (block == "B") + 19 * i + j
        assert 0 <= i <= 18 and 0 <= j <= 18
        offsets = (g if block == "A" else f) if sector == "X" else (f if block == "A" else g)
        sign = 1 if sector == "X" else -1
        expected = [(i + sign * di, j + sign * dj) for di, dj in offsets]
        assert pairs(terms) == expected, (sector, q)
        products.update(pairs(terms))
    cancellation = Counter(
        pairs(
            section.split("Cancellation multiset C (each entry cancels twice):")[1].split(
                "Residual multiset R:"
            )[0]
        )
    )
    residual = Counter(pairs(section.split("Residual multiset R:")[1]))
    assert products == residual + cancellation + cancellation
    assert all(v == 1 for v in residual.values())
    assert all(
        not (2 <= i <= 18 and 0 <= j <= 20)
        if sector == "X"
        else not (-2 <= i <= 18 and 0 <= j <= 16)
        for i, j in residual
    )
    opposite = "Z" if sector == "X" else "X"
    assert all(len(witnesses[sector] & row) % 2 == 0 for row in matrices[opposite])
    print(
        sector,
        "witness: all products, C+C+R, support weight and 357 fixed dot products PASS;",
        "product terms",
        sum(products.values()),
        "cancellation pairs",
        sum(cancellation.values()),
        "residual",
        sorted(residual),
    )
assert witnesses["X"] & witnesses["Z"] == {65}
print("Witness intersection exactly {65}: PASS")


# Finite polynomial identities, represented by sets of exponent pairs over F_2.
def add(*polys):
    result = set()
    for poly in polys:
        result.symmetric_difference_update(poly)
    return result


def mul(a, b):
    result = set()
    for i, j in a:
        for k, ell in b:
            result.symmetric_difference_update({(i + k, j + ell)})
    return result


one, x, y = {(0, 0)}, {(1, 0)}, {(0, 1)}
x2, y2 = mul(x, x), mul(y, y)
t = add(y, y2)
B = add(one, mul(y2, t))
r = {(0, j) for j in (0, 1, 2, 6, 8)}
assert add(mul(B, B), t) == r
assert add(mul(B, add(B, t)), mul(mul(t, t), y2)) == r
assert mul(y, {(0, j) for j in (0, 1, 5, 7)}) == add(one, r)
assert mul(t, {(0, j) for j in (0, 5, 6)}) == add(one, r)
L = add(set(g), mul(x2, set(f)))
assert L == {(0, 0), (3, 0), (4, 0), (2, 1)}
p = {(i, 0) for i in (0, 5, 8)}
assert add(mul(L, L), mul(mul(x2, x2), set(f))) == p
alpha = add(x, x2)
beta = add(one, mul(x2, alpha))
assert add(mul(beta, beta), mul(mul(x2, x2), alpha)) == p
print("Printed determinant, inverse and elimination polynomial identities: PASS")
print("All checks passed. No candidate errors or logicals enumerated.")
