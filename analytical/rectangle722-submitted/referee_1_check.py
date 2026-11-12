"""Fixed printed-arithmetic diagnostics for DRAFT.tex only.

No error/logical search, matrix rank computation, or external input.
Checks all printed rows by coordinate addition and the five-case formulas,
then checks the two supplied multiplication/cancellation certificates.
Run with: python3 analytical/rectangle722-submitted/referee_1_check.py
The analytic proof is reviewed separately; this script is not its premise.
"""

import re
from collections import Counter
from pathlib import Path

text = re.sub(r"\\\((-?\d+|[CR])\\\)", r"\1", Path(__file__).with_name("DRAFT.tex").read_text())


def integers(s):
    return [int(n) for n in re.findall(r"-?\d+", s)]


def pairs(s):
    return [tuple(map(int, p)) for p in re.findall(r"\((-?\d+), (-?\d+)\)", s)]


def label(block, i, j):
    return 361 * block + 19 * i + j


f = [(1, 0), (2, 0), (0, 2)]
g = [(0, 0), (2, 1), (2, 2)]
bar_f = [(-i, -j) for i, j in f]
bar_g = [(-i, -j) for i, j in g]

appendix = text.split("\\section{Complete numerical support matrices}")[1]
row_pattern = r"^  (\d+) & \((-?\d+), (\d+)\) & ([\d, ]+) \\\\$"
for sector in ("X", "Z"):
    section = appendix.split(f"\\subsection{{{sector} supports}}")[1].split("\\subsection")[0]
    rows = re.findall(row_pattern, section, re.M)
    assert len(rows) == 357, (sector, "row count", len(rows))
    for index, (r, i, j, support) in enumerate(rows):
        r, i, j = int(r), int(i), int(j)
        actual = integers(support)
        assert r == index, (sector, "ordered index", r, index)
        assert actual == sorted(set(actual)), (sector, r, "duplicates/order")
        assert all(0 <= q < 722 for q in actual), (sector, r, "label range")
        if sector == "X":
            a, b = divmod(r, 17)
            assert (i, j) == (a - 2, b), (sector, r, "anchor")
            generators = (f, g)
            u = 19 * a + b
            if a == 0:
                case = [b, b + 362, b + 363]
            elif a == 1:
                case = [b, b + 19, b + 381, b + 382]
            elif a <= 18:
                case = [u - 36, u - 19, u, u + 323, u + 362, u + 363]
            elif a == 19:
                case = [b + 325, b + 342, b + 684]
            else:
                case = [b + 344, b + 703]
        else:
            c, d = divmod(r, 21)
            assert (i, j) == (c + 2, d), (sector, r, "anchor")
            generators = (bar_g, bar_f)
            u = 19 * c + d
            if d == 0:
                case = [19 * c + n for n in (38, 361, 380)]
            elif d == 1:
                case = [19 * c + n for n in (0, 39, 362, 381)]
            elif d <= 18:
                case = [u + n for n in (-2, -1, 38, 361, 380, 397)]
            elif d == 19:
                case = [19 * c + n for n in (17, 18, 416)]
            else:
                case = [19 * c + n for n in (18, 417)]
        direct = sorted(
            label(block, i + di, j + dj)
            for block, generator in enumerate(generators)
            for di, dj in generator
            if 0 <= i + di <= 18 and 0 <= j + dj <= 18
        )
        assert actual == case == direct, (sector, r, actual, case, direct)
    print(f"{sector}: all 357 rows, anchors, ordered indices, clipping, five cases PASS")

witnesses = {}
product_pattern = r"^  (\d+) & ([AB])\((\d+), (\d+)\) & (.+) \\\\$"
for sector, size in (("X", 23), ("Z", 20)):
    support_text = text.split(f"{sector} support ({size} distinct qubits):\n\n")[1]
    support = integers(support_text.split(".\n", 1)[0])
    assert len(support) == len(set(support)) == size
    section = text.split(f"\\subsubsection{{{sector} multiplication}}")[1]
    section = re.split(r"\\(?:sub)*section\{", section)[0]
    rows = re.findall(product_pattern, section, re.M)
    assert [int(row[0]) for row in rows] == support
    products = Counter()
    for q, block, i, j, printed in rows:
        q, i, j = int(q), int(i), int(j)
        assert 0 <= i <= 18 and 0 <= j <= 18
        assert label(block == "B", i, j) == q
        generator = (
            (g if block == "A" else f) if sector == "X" else (bar_f if block == "A" else bar_g)
        )
        direct = [(i + di, j + dj) for di, dj in generator]
        assert pairs(printed) == direct, (sector, q, "product")
        products.update(direct)
    cancellation = pairs(
        section.split("Cancellation multiset C (each entry cancels twice):")[1].split(
            "Residual multiset R:"
        )[0]
    )
    residual = pairs(section.split("Residual multiset R:")[1])
    assert products == Counter(cancellation + cancellation + residual), sector
    expected = (
        [(1, 12), (19, 10), (19, 11)] if sector == "X" else [(3, -2), (3, -1), (4, 17), (6, 17)]
    )
    assert residual == expected
    assert (
        all(not (2 <= i <= 18 and 0 <= j <= 20) for i, j in residual)
        if (sector == "X")
        else all(not (-2 <= i <= 18 and 0 <= j <= 16) for i, j in residual)
    )
    witnesses[sector] = set(support)
    print(f"{sector}: {size} supplied labels, all products, R+C+C, residual anchors PASS")
assert witnesses["X"] & witnesses["Z"] == {65}
print("Supplied witness intersection = {65}; pairing = 1 PASS")
