"""Diagnostic arithmetic for DRAFT.typ only; no error/logical search.

Checks every printed input row, both supplied witness expansions and their
integer cancellation multisets, and fixed polynomial identities. Uses only
the standard library. Run with python3 referee_3_check.py. No files are written.
The analytic proof, including run accounting, is reviewed by hand, not here.
"""

import re
from collections import Counter
from pathlib import Path


def require(condition, label):
    if not condition:
        raise AssertionError(label)


source = Path(__file__).with_name("DRAFT.typ").read_text()
f = [(1, 0), (2, 0), (0, 2)]
g = [(0, 0), (2, 1), (2, 2)]
bar_f = [(-i, -j) for i, j in f]
bar_g = [(-i, -j) for i, j in g]
row_pattern = re.compile(r"^  \[(\d+)\], \[\((-?\d+), (\d+)\)\], \[([\d, ]+)\],$", re.M)
appendix = source.split("= Appendix A: complete numerical support matrices\n")[1]
x_text, z_text = appendix.split("== Z supports\n")


def five_case(sector, row):
    if sector == "X":
        a, b = divmod(row, 17)
        u = 19 * a + b
        if a == 0:
            return [b, b + 362, b + 363]
        if a == 1:
            return [b, b + 19, b + 381, b + 382]
        if a <= 18:
            return [u - 36, u - 19, u, u + 323, u + 362, u + 363]
        if a == 19:
            return [b + 325, b + 342, b + 684]
        return [b + 344, b + 703]
    c, d = divmod(row, 21)
    v = 19 * c
    u = v + d
    if d == 0:
        return [v + 38, v + 361, v + 380]
    if d == 1:
        return [v, v + 39, v + 362, v + 381]
    if d <= 18:
        return [u - 2, u - 1, u + 38, u + 361, u + 380, u + 397]
    if d == 19:
        return [v + 17, v + 18, v + 416]
    return [v + 18, v + 417]


for sector, section, factors in [("X", x_text, (f, g)), ("Z", z_text, (bar_g, bar_f))]:
    rows = row_pattern.findall(section)
    require(len(rows) == 357, f"{sector}: row count")
    for expected, (number, ai, bj, entries) in enumerate(rows):
        number, ai, bj = int(number), int(ai), int(bj)
        require(number == expected, f"{sector}: ordered row {expected}")
        q, rem = divmod(number, 17 if sector == "X" else 21)
        anchor = (q - 2, rem) if sector == "X" else (q + 2, rem)
        require((ai, bj) == anchor, f"{sector} {number}: anchor")
        printed = [int(n) for n in entries.split(", ")]
        calculated = []
        for block, factor in enumerate(factors):
            for di, dj in factor:
                i, j = ai + di, bj + dj
                if 0 <= i <= 18 and 0 <= j <= 18:
                    calculated.append(361 * block + 19 * i + j)
        require(printed == sorted(set(printed)), f"{sector} {number}: strict ordering")
        require(printed == sorted(calculated), f"{sector} {number}: clipped formula")
        require(printed == five_case(sector, number), f"{sector} {number}: five cases")
    print(f"PASS {sector}: all 357 ordered rows, anchors, clipping and five-case values")


def pairs(text):
    return [(int(a), int(b)) for a, b in re.findall(r"\((-?\d+), (-?\d+)\)", text)]


witness_pattern = re.compile(r"^  \[(\d+)\], \[([AB])\((\d+), (\d+)\)\], \[(.*?)\],$", re.M)
supports = {}
for sector, weight, factors in [("X", 23, (g, f)), ("Z", 20, (bar_f, bar_g))]:
    support_text = source.split(f"{sector} support ({weight} distinct qubits):\n\n")[1].split(
        ".\n", 1
    )[0]
    support = [int(n) for n in support_text.split(", ")]
    require(len(support) == len(set(support)) == weight, f"{sector}: witness weight")
    require(all(0 <= n < 722 for n in support), f"{sector}: witness labels")
    supports[sector] = set(support)
    section = source.split(f"=== {sector} multiplication\n")[1]
    section = section.split("#pagebreak()", 1)[0].split("== Cycle,", 1)[0]
    rows = witness_pattern.findall(section)
    require([int(r[0]) for r in rows] == support, f"{sector}: all witness inputs")
    products = Counter()
    for label, block, si, sj, product_text in rows:
        i, j = int(si), int(sj)
        b = int(block == "B")
        require(int(label) == 361 * b + 19 * i + j, f"{sector} {label}: monomial")
        expected = [(i + di, j + dj) for di, dj in factors[b]]
        require(pairs(product_text) == expected, f"{sector} {label}: product")
        products.update(expected)
    cancellation_text = section.split("Cancellation multiset C (each entry cancels twice):\n\n")[
        1
    ].split(".\n", 1)[0]
    residual_text = section.split("Residual multiset R: ")[1].split(".\n", 1)[0]
    cancellation, residual = Counter(pairs(cancellation_text)), Counter(pairs(residual_text))
    require(products == residual + cancellation + cancellation, f"{sector}: R+C+C integer identity")
    require(all(n == 1 for n in residual.values()), f"{sector}: residual multiplicity")
    for i, j in residual:
        tested = 2 <= i <= 18 and 0 <= j <= 20 if sector == "X" else -2 <= i <= 18 and 0 <= j <= 16
        require(not tested, f"{sector}: residual in tested anchors")
    print(
        f"PASS {sector}: {weight} witness inputs, {3 * weight} products, {sum(cancellation.values())} cancellation pairs; residual {sorted(residual)}"
    )
require(supports["X"] & supports["Z"] == {65}, "witness intersection")
print("PASS witness intersection is exactly {65}")


# Fixed polynomial identities over F_2, represented as exponent sets.
def add(*polys):
    out = set()
    for poly in polys:
        out.symmetric_difference_update(poly)
    return out


def mul(a, b):
    counts = Counter((i + k, j + ell) for i, j in a for k, ell in b)
    return {exponent for exponent, count in counts.items() if count % 2}


def power(a, n):
    out = {(0, 0)}
    for _ in range(n):
        out = mul(out, a)
    return out


one, x, y = {(0, 0)}, {(1, 0)}, {(0, 1)}
t = add(y, power(y, 2))
B = add(one, mul(power(y, 2), t))
r = {(0, n) for n in [0, 1, 2, 6, 8]}
require(add(power(B, 2), t) == r, "rank X resultant")
require(add(mul(B, add(B, t)), mul(power(t, 2), power(y, 2))) == r, "bulk determinant")
require(mul(y, {(0, n) for n in [0, 1, 5, 7]}) == add(one, r), "y inverse identity")
require(mul(t, add(one, mul(power(y, 4), t))) == add(one, r), "t inverse identity")
a = add(x, power(x, 2))
b = add(one, mul(power(x, 2), a))
p = {(n, 0) for n in [0, 5, 8]}
require(add(power(b, 2), mul(power(x, 4), a)) == p, "rank Z resultant")
L = add(set(g), mul(power(x, 2), set(f)))
require(L == {(0, 0), (3, 0), (4, 0), (2, 1)}, "L expansion")
require(add(power(L, 2), mul(power(x, 4), set(f))) == p, "p expansion")


def mod_r(poly):
    require(all(i == 0 for i, _ in poly), "univariate remainder")
    poly = set(poly)
    while poly and max(j for _, j in poly) >= 8:
        degree = max(j for _, j in poly)
        poly = add(poly, mul({(0, degree - 8)}, r))
    return poly


X = {(0, n) for n in [0, 2, 5, 6]}
require(not mod_r(add(X, power(X, 2), power(y, 2))), "f(X,y)")
require(not mod_r(add(one, mul(power(X, 2), t))), "g(X,y)")
require(not mod_r(add(one, power(X, 5), power(X, 8))), "p(X)")
require(not mod_r(add(one, mul(X, add(power(X, 7), power(X, 4))))), "X inverse")
print("PASS fixed rank, determinant and charge-algebra polynomial identities")
print("All diagnostics passed. No candidate errors or logicals were enumerated.")
