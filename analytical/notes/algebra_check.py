#!/usr/bin/env python3
"""Exact polynomial checks for algebra.md; no matrix/codeword/distance search.

Run: python3.13 analytical/notes/algebra_check.py
Standard library only. Polynomials over F2 are encoded by coefficient bits.
"""

from itertools import permutations


def mul(a: int, b: int) -> int:
    """Carryless polynomial multiplication in F2[x], without reduction."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        b >>= 1
    return result


def determinant(matrix: list[list[int]]) -> int:
    """Leibniz determinant; signs equal plus in characteristic two."""
    result = 0
    for permutation in permutations(range(len(matrix))):
        term = 1
        for i, j in enumerate(permutation):
            term = mul(term, matrix[i][j])
        result ^= term
    return result


def exponents(polynomial: int) -> list[int]:
    return [i for i in range(polynomial.bit_length()) if polynomial >> i & 1]


def remainder(polynomial: int, modulus: int) -> int:
    """Polynomial remainder by monic modulus over F2."""
    if modulus == 0:
        raise ValueError("zero modulus")
    while polynomial and polynomial.bit_length() >= modulus.bit_length():
        polynomial ^= modulus << (polynomial.bit_length() - modulus.bit_length())
    return polynomial


def main() -> None:
    # Original symbolic manipulation: descending coefficients in y.
    f = [1, 1 << 2, 0, 1 ^ (1 << 3)]
    g = [1 << 3, 0, 1 ^ 2, 1 << 2]
    sylvester = []
    for coefficients in (f, g):
        for shift in range(3):
            sylvester.append([0] * shift + coefficients + [0] * (2 - shift))
    resultant = determinant(sylvester)

    # Independent multiplication-by-g presentation in basis 1,y,y^2 modulo f.
    # y^3 = a*y^2+c; g mod f = aa*y^2+bb*y+cc.
    a, c = 1 << 2, 1 ^ (1 << 3)
    aa, bb = 1 << 5, 1 ^ 2
    cc = (1 << 2) ^ (1 << 3) ^ (1 << 6)
    dd = bb ^ mul(aa, a)
    multiplication = [
        [cc, mul(aa, c), mul(dd, c)],
        [bb, cc, mul(aa, c)],
        [aa, dd, cc ^ mul(dd, a)],
    ]
    norm = determinant(multiplication)
    expected = [0, 1, 2, 4, 5, 6, 10, 11, 13, 14, 15, 18]
    assert resultant == norm
    assert exponents(resultant) == expected
    print("Sylvester determinant exponents:", exponents(resultant))
    print("Independent multiplication determinant agrees.")

    # Second charge presentation, purely symbolic in y:
    # r = B^2+t = 1+t+y^4*t^2, X=B/t=t^-1+y^2.
    y = 1 << 1
    t = y ^ mul(y, y)
    big_b = 1 ^ mul(1 << 2, t)
    r = mul(big_b, big_b) ^ t
    assert exponents(r) == [0, 1, 2, 6, 8]
    assert r == 1 ^ t ^ mul(1 << 4, mul(t, t))
    t_inverse = 1 ^ mul(1 << 4, t)
    y_inverse = 1 ^ y ^ (1 << 5) ^ (1 << 7)
    x_image = t_inverse ^ (1 << 2)
    assert remainder(mul(t, t_inverse), r) == 1
    assert remainder(mul(y, y_inverse), r) == 1
    assert remainder(mul(x_image, t) ^ big_b, r) == 0
    assert remainder(mul(x_image, x_image) ^ t_inverse, r) == 0
    assert remainder(x_image ^ mul(x_image, x_image) ^ (1 << 2), r) == 0
    assert remainder(1 ^ mul(mul(x_image, x_image), t), r) == 0
    print("Charge y-presentation: r=1+y+y^2+y^6+y^8; inverse identities agree.")

    # Symbolic telescoping for the odd-row X cycle:
    # a = sum_{m=0}^8 x^(1+2m) (y+y^2)^m; g=1+x^2(y+y^2).
    t = (1 << 1) ^ (1 << 2)
    rows = {}
    power = 1
    for m in range(9):
        rows[1 + 2 * m] = power
        power = mul(power, t)
    syndrome = {}
    for i, coefficient in rows.items():
        syndrome[i] = syndrome.get(i, 0) ^ coefficient
        syndrome[i + 2] = syndrome.get(i + 2, 0) ^ mul(coefficient, t)
    syndrome = {i: value for i, value in syndrome.items() if value}
    assert syndrome == {1: 1, 19: power}
    assert sum(value.bit_count() for value in rows.values()) == 29
    print("Odd-row cycle: syndrome x + x^19*(y+y^2)^9; weight 29.")


if __name__ == "__main__":
    main()
