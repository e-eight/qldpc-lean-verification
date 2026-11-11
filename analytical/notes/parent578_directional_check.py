#!/usr/bin/env python3.13
"""Read-only reproduction of parent578-directional.md's fixed identities.

Run from any directory with Python 3.13:
    python3.13 analytical/notes/parent578_directional_check.py
    python3.13 analytical/notes/parent578_directional_check.py --upstream PATH

Input: the SHA-256-pinned codes/578-18-20.json in --upstream, QLDPC_REPO,
or the sibling qldpc-challenge checkout. No upstream modules are imported.
Manipulations: clipped sparse translates, binary row operations, and exact
polynomial arithmetic over F2 using sets of exponent pairs. No dependencies,
file writes, logical-vector search, distance calculation, or Lean invocation.
Output: a JSON report of inputs, fixed checks, and their status; failures raise
an exception even with python -O. This is PROPOSITION, not formalization:
the note's derived claims remain PROPOSITION, review/formalization pending.
"""

import argparse
import hashlib
import json
import os
import platform
from dataclasses import dataclass
from pathlib import Path

SOURCE_SHA256 = "440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514"
F_SUPPORT = ((0, 0), (0, 3), (2, 2), (3, 0))
G_SUPPORT = ((0, 1), (1, 1), (2, 0), (3, 3))
BETA = (-1, 14, -2, 15, -3, 16)
GAMMA = (2, 17, 1, 18, 0, 19)


def require(condition, label):
    if not condition:
        raise ValueError(f"FAILED: {label}")


def support(a_cells, b_cells):
    """Clip to the 17x17 board and add physical unit vectors modulo two."""
    result = set()
    for offset, cells in ((0, a_cells), (289, b_cells)):
        for i, j in cells:
            if 0 <= i < 17 and 0 <= j < 17:
                result.symmetric_difference_update({offset + 17 * i + j})
    return sorted(result)


def translate(side, a, b):
    first, second, sign = (F_SUPPORT, G_SUPPORT, 1) if side == "X" else (G_SUPPORT, F_SUPPORT, -1)
    return support(
        [(a + sign * i, b + sign * j) for i, j in first],
        [(a + sign * i, b + sign * j) for i, j in second],
    )


def boundary_x(a):
    """The six independently transcribed X templates in the note's order."""
    return [
        support([(a, 2), (a + 2, 1)], [(a, 0), (a + 1, 0), (a + 3, 2)]),
        support(
            [(a, 14), (a + 2, 16), (a + 3, 14)],
            [(a, 15), (a + 1, 15), (a + 2, 14)],
        ),
        support([(a, 1), (a + 2, 0)], [(a + 3, 1)]),
        support([(a, 15), (a + 3, 15)], [(a, 16), (a + 1, 16), (a + 2, 15)]),
        support([(a, 0)], [(a + 3, 0)]),
        support([(a, 16), (a + 3, 16)], [(a + 2, 16)]),
    ]


def boundary_z(d):
    """The six independently transcribed Z templates in the note's order."""
    return [
        support([(2, d - 1), (1, d - 1), (0, d)], [(2, d), (2, d - 3), (0, d - 2)]),
        support([(16, d - 1), (15, d), (14, d - 3)], [(15, d - 2), (14, d)]),
        support([(1, d - 1), (0, d - 1)], [(1, d), (1, d - 3)]),
        support([(16, d), (15, d - 3)], [(16, d - 2), (15, d)]),
        support([(0, d - 1)], [(0, d), (0, d - 3)]),
        support([(16, d - 3)], [(16, d)]),
    ]


def packed(row):
    return sum(1 << q for q in row)


def reduce_row(value, basis):
    while value and value.bit_length() - 1 in basis:
        value ^= basis[value.bit_length() - 1]
    return value


def row_checks(document):
    require(document["n"] == 578 and document["code_type"] == "CSS", "source type/length")
    actual = document["checks"]
    for side in ("X", "Z"):
        require(len(actual[side]) == 280, f"{side} row count")
        for j, row in enumerate(actual[side]):
            require(
                all(type(q) is int and 0 <= q < 578 for q in row) and row == sorted(set(row)),
                f"{side} row {j} canonical sparse support",
            )
    anchors = {
        "X": [(a, b) for a in range(14) for b in range(14)]
        + [(a, b) for a in range(14) for b in BETA],
        "Z": [(c, d) for c in range(3, 17) for d in range(3, 17)]
        + [(c, d) for d in range(3, 17) for c in GAMMA],
    }
    proposed_anchors = {
        "X": [(a, b) for a in range(-3, 17) for b in range(14)],
        "Z": [(c, d) for c in range(3, 17) for d in range(20)],
    }
    proposed = {
        side: [translate(side, a, b) for a, b in proposed_anchors[side]] for side in ("X", "Z")
    }
    for side, opposite in (("X", "Z"), ("Z", "X")):
        require(len(set(anchors[side])) == 280, f"{side} unique ordered anchors")
        for j, (a, b) in enumerate(anchors[side]):
            require(actual[side][j] == translate(side, a, b), f"ordered {side} row {j}")
            require(
                sorted(577 - q for q in actual[side][j]) == translate(opposite, 16 - a, 16 - b),
                f"reversal/sector exchange {side} row {j}",
            )
        require(
            {(16 - a, 16 - b) for a, b in anchors[side]} == set(proposed_anchors[opposite]),
            f"{side} reversal covers proposed opposite anchors",
        )
        require(
            [j for j, row in enumerate(actual[side]) if row in proposed[side]] == list(range(196)),
            f"{side} exactly 196 bulk rows match proposed rectangle",
        )
        # Diagnostic reproduction of the note's preliminary span observation.
        # The explicit odd-pairing witnesses below establish non-equality without rank.
        basis = {}
        for row in proposed[side]:
            value = reduce_row(packed(row), basis)
            if value:
                basis[value.bit_length() - 1] = value
        require(
            [j for j, row in enumerate(actual[side]) if reduce_row(packed(row), basis)]
            == list(range(196, 280)),
            f"{side} 84 boundary rows outside proposed span (diagnostic)",
        )
    for a in range(14):
        require(boundary_x(a) == actual["X"][196 + 6 * a : 202 + 6 * a], f"X templates a={a}")
    for d in range(3, 17):
        t = d - 3
        require(boundary_z(d) == actual["Z"][196 + 6 * t : 202 + 6 * t], f"Z templates d={d}")
    # These are check-row pairings only, never logical-vector enumeration.
    for label, rows in (("M", proposed), ("N", actual)):
        xs, zs = ([packed(row) for row in rows[side]] for side in ("X", "Z"))
        require(all((x & z).bit_count() % 2 == 0 for x in xs for z in zs), f"{label} CSS")
    require(actual["X"][200] == [0, 340], "literal separating X row")
    require(actual["Z"][200] == [2, 289, 292], "literal separating Z row")
    require(translate("Z", 3, 0) == [17, 289, 340], "model Z separator")
    require(translate("X", -3, 0) == [0, 292], "model X separator")
    require(set(actual["X"][200]) & set(translate("Z", 3, 0)) == {340}, "X odd pairing")
    require(set(actual["Z"][200]) & set(translate("X", -3, 0)) == {292}, "Z odd pairing")
    deleted = set(range(272, 278)) | set(range(564, 570))
    for i in range(6):
        pair = {272 + i, 564 + i}
        fan = support(
            [(13, i), (13, i + 3), (15, i + 2)],
            [(13, i + 1), (14, i + 1), (15, i)],
        )
        require(anchors["X"][182 + i] == (13, i), f"hole {i} X anchor")
        require(anchors["Z"][201 + 6 * i] == (19, i + 3), f"hole {i} Z anchor")
        require(set(actual["Z"][201 + 6 * i]) == pair, f"hole {i} pair row")
        require(set(actual["X"][182 + i]) == pair | set(fan), f"hole {i} fan formula")
        require(not deleted.intersection(fan), f"hole {i} fan retained")
        require(
            [j for j, row in enumerate(actual["X"]) if pair.intersection(row)] == [182 + i],
            f"hole {i} unique X incidence",
        )
    return {
        "ordered_parent_rows": 560,
        "boundary_template_instances": 168,
        "reversal_and_sector_exchange_rows": 560,
        "commutation_pairs_per_rectangle": 280 * 280,
        "same_sector_counterexamples": {"X_row_200_overlap": [340], "Z_row_200_overlap": [292]},
        "proposed_model_matching_rows_per_side": 196,
        "diagnostic_boundary_rows_outside_proposed_span_per_side": 84,
        "removal_pairs_and_fans": 6,
        "cycle_recurrence": "coefficient support equals each fixed X row; boundary templates checked",
    }


@dataclass(frozen=True)
class Poly:
    """F2[x,y]: a monomial (i,j) occurs exactly when x**i*y**j has coefficient 1."""

    terms: frozenset[tuple[int, int]]

    def __add__(self, other):
        return Poly(self.terms ^ other.terms)

    def __mul__(self, other):
        result = set()
        for i, j in self.terms:
            for k, ell in other.terms:
                result.symmetric_difference_update({(i + k, j + ell)})
        return Poly(frozenset(result))

    def __pow__(self, exponent):
        require(type(exponent) is int and exponent >= 0, "nonnegative polynomial exponent")
        result = ONE
        for _ in range(exponent):
            result = result * self
        return result


ZERO = Poly(frozenset())
ONE = Poly(frozenset({(0, 0)}))
X = Poly(frozenset({(1, 0)}))
Y = Poly(frozenset({(0, 1)}))


def ypoly(*exponents):
    require(len(exponents) == len(set(exponents)), "distinct quoted y exponents")
    return Poly(frozenset((0, j) for j in exponents))


def psum(polynomials):
    result = ZERO
    for polynomial in polynomials:
        result = result + polynomial
    return result


def minor(matrix, row, column):
    return [
        [entry for j, entry in enumerate(r) if j != column]
        for i, r in enumerate(matrix)
        if i != row
    ]


def determinant(matrix):
    """Laplace expansion in characteristic two: all permutation signs equal 1."""
    if not matrix:
        return ONE
    return psum(
        entry * determinant(minor(matrix, 0, j))
        for j, entry in enumerate(matrix[0])
        if entry != ZERO
    )


def polynomial_checks():
    passed = []

    def equal(label, left, right):
        require(left == right, label)
        passed.append(label)

    f = ONE + Y**3 + X**2 * Y**2 + X**3
    g = Y + X * Y + X**2 + X**3 * Y**3
    p = ypoly(18, 15, 13, 8, 7, 6, 2, 0)
    q = ypoly(17, 15, 12, 9, 7, 3, 1)
    u, v, w = ypoly(0, 5), Y, ypoly(1, 3, 6)
    h = u * X**2 + v * X + w
    a, b = ypoly(11, 2, 1), ypoly(7, 5, 4, 2, 0)
    d, e, t = ypoly(17, 11, 10, 7, 6, 5, 0), ypoly(10, 7, 5, 3, 1, 0), ypoly(6, 4, 1, 0)
    equal("f support", f, Poly(frozenset(F_SUPPORT)))
    equal("g support", g, Poly(frozenset(G_SUPPORT)))
    equal("bulk commutation fg+gf=0", f * g + g * f, ZERO)
    equal("h=g+y^3*f", h, g + Y**3 * f)
    equal("equation (12)", a * X + b, u**2 * f + (u * X + u * Y**2 + v) * h)
    matrix = [
        [ONE, Y**2, ZERO, ONE + Y**3, ZERO, ZERO],
        [ZERO, ONE, Y**2, ZERO, ONE + Y**3, ZERO],
        [ZERO, ZERO, ONE, Y**2, ZERO, ONE + Y**3],
        [Y**3, ONE, Y, Y, ZERO, ZERO],
        [ZERO, Y**3, ONE, Y, Y, ZERO],
        [ZERO, ZERO, Y**3, ONE, Y, Y],
    ]
    equal("Sylvester det(M)=P", determinant(matrix), p)
    powers = [X**i for i in range(5, -1, -1)]
    products = [
        psum(entry * value for entry, value in zip(row, powers, strict=True)) for row in matrix
    ]
    expected = [X**2 * f, X * f, f, X**2 * g, X * g, g]
    for j, (left, right) in enumerate(zip(products, expected, strict=True)):
        equal(f"Sylvester MV row {j}", left, right)
    # adj(M)[5,j] = cofactor(M)[j,5]; signs disappear over F2.
    adj_last = [determinant(minor(matrix, j, 5)) for j in range(6)]
    for j in range(6):
        equal(
            f"last adjugate row times M column {j}",
            psum(adj_last[i] * matrix[i][j] for i in range(6)),
            p if j == 5 else ZERO,
        )
    equal(
        "P membership via explicit five-by-five minors",
        psum(adj_last[i] * expected[i] for i in range(6)),
        p,
    )
    equal("Bezout d*a+e*P=1", d * a + e * p, ONE)
    equal("d*b+q=t*P", d * b + q, t * p)
    equal("x+q membership", X + q, d * (a * X + b) + (e * X + t) * p)
    sf = ypoly(33, 31, 30, 29, 28, 25, 20, 19, 18, 13, 12, 10, 7, 6, 5, 2, 0)
    sg = ypoly(36, 34, 33, 32, 31, 28, 23, 22, 18, 17, 16, 14, 12, 11, 6, 5, 4, 3, 1)
    equal("f(q,y)=P*E(S_F)", q**3 + Y**2 * q**2 + ONE + Y**3, p * sf)
    equal("g(q,y)=P*E(S_G)", Y**3 * q**3 + q**2 + Y * q + Y, p * sg)
    ell = X + q
    equal("full f quotient identity", f, ell * (X**2 + X * q + q**2 + Y**2 * ell) + p * sf)
    equal("full g quotient identity", g, ell * (Y**3 * (X**2 + X * q + q**2) + ell + Y) + p * sg)
    r = ypoly(16, 15, 10, 7, 4, 1, 0)
    equal("q inverse modulo P", q * r + ONE, p * ypoly(15, 14, 13, 11, 10, 9, 7, 5, 4, 1, 0))
    equal("y inverse modulo P", Y * ypoly(17, 14, 12, 7, 6, 5, 1) + ONE, p)
    require(max(j for _, j in p.terms) == 18 and (0, 0) in p.terms, "P degree and constant term")
    return {
        "passed_identities": passed,
        "P_y_exponents": sorted(j for _, j in p.terms),
        "P_degree": 18,
    }


def main():
    repo = Path(__file__).resolve().parents[2]
    default = Path(os.environ.get("QLDPC_REPO", repo.parent / "qldpc-challenge"))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=default, help="qldpc-challenge checkout")
    args = parser.parse_args()
    source = args.upstream.resolve() / "codes/578-18-20.json"
    raw = source.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    require(digest == SOURCE_SHA256, "pinned source SHA-256")
    result = {
        "status": "PASS",
        "grade": "PROPOSITION; derived propositions still pending independent review/formalization",
        "python": platform.python_version(),
        "input": {"path": str(source), "sha256": digest},
        "rows": row_checks(json.loads(raw)),
        "polynomials": polynomial_checks(),
        "scope": "fixed row/polynomial identities only; no logical search, distance claim, or Lean",
    }
    # Recheck that the input was not changed during the run. This script never writes it.
    require(hashlib.sha256(source.read_bytes()).hexdigest() == digest, "input unchanged during run")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
