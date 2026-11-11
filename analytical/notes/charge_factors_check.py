#!/usr/bin/env python3
"""Symbolic F2 polynomial checks for charge-factors.md; no support search.

Python 3.13, standard library only. Integer bit i is the coefficient of x^i.
Exploratory output consists of closed identities, not a case certificate.
"""


def mul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out


def rem(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def power(a, n, modulus):
    out = 1
    for _ in range(n):
        out = rem(mul(out, a), modulus)
    return out


def show(a):
    return (
        " + ".join(
            "1" if i == 0 else "x" if i == 1 else f"x^{i}"
            for i in range(a.bit_length())
            if (a >> i) & 1
        )
        or "0"
    )


def check_normalization():
    """Check closed syndrome-kernel identities, including reversed Z.

    Pairs are (x exponent, y exponent). For X, x is the slice axis.
    Reversing the Z syndrome column uses offset 2-y and transverse x;
    exchanging physical types makes old f the new U kernel.
    """
    f = {(1, 0), (2, 0), (0, 2)}
    g = {(0, 0), (2, 1), (2, 2)}
    u_kernel = {(0, 0), (2, 1), (2, 2)}
    assert g == u_kernel
    assert f == {(0, 2), (1, 0), (2, 0)}
    assert {(2 - j, i) for i, j in f} == u_kernel
    assert {(2 - j, i) for i, j in g} == {(0, 2), (1, 2), (2, 0)}
    # The six-singleton proof compares Laurent exponents, not field residues.
    assert {-1, 1}.isdisjoint({3, 4})
    # Closed inverse-matrix identities for the charge-period lattice.
    assert 13 * 16 - 3 * (-3) == 217
    assert 13 * 3 - 3 * 13 == 0
    assert 3 * 16 + 16 * (-3) == 0
    assert 3 * 3 + 16 * 13 == 217


def main():
    check_normalization()
    a = 0b1101  # x^3+x^2+1
    b = 0b111101  # x^5+x^4+x^3+x^2+1
    p = (1 << 8) ^ (1 << 5) ^ 1
    y = (1 << 6) ^ (1 << 3) ^ (1 << 2) ^ (1 << 1)
    assert mul(a, b) == p
    assert rem(a, 0b10) == rem(a, 0b11) == 1
    assert rem(b, 0b10) == rem(b, 0b11) == 1
    assert rem(b, 0b111) == 0b10
    for divisor in (0b111, 0b1011, a):
        print(f"b mod ({show(divisor)}) = {show(rem(b, divisor))}")
    for modulus, period in ((a, 7), (b, 31)):
        yy = rem(y, modulus)
        assert power(2, period, modulus) == 1
        assert rem(2 ^ 4 ^ mul(yy, yy), modulus) == 0
        assert rem(1 ^ mul(4, yy ^ mul(yy, yy)), modulus) == 0
        print(f"y mod ({show(modulus)}) = {show(yy)}")
        # Find an exponent only to suggest a closed identity for the note.
        exponent = next(k for k in range(period) if power(2, k, modulus) == yy)
        print(f"y = x^{exponent} modulo ({show(modulus)})")
    assert rem(y ^ (1 << 3), a) == 0
    assert rem(y ^ (1 << 26), b) == 0
    assert b == mul(0b101, a) ^ 0b100
    assert rem(mul(1 << 3, power(y, 13, p)) ^ 1, p) == 0
    assert rem((1 << 16) ^ power(y, 3, p), p) == 0
    assert mul(0b110, 0b11) == 0b1010
    assert mul(mul(0b110, 0b110), 0b11) == 0b111100
    # A monomial seed under t=z+z^2 has weights 1,2,2,4 at powers 0,1,2,3.
    assert mul(0b110, 0b110) == 0b10100
    assert mul(mul(0b110, 0b110), 0b110) == 0b1111000
    t_squared = mul(0b110, 0b110)
    t_fourth = mul(t_squared, t_squared)
    assert mul(t_fourth, 0b110) == (1 << 5) ^ (1 << 6) ^ (1 << 9) ^ (1 << 10)
    # F3: both normalized sectors, with q/p=z or z^2. Each RHS has three terms.
    # The note proves this by distinct exponents, without relying on these checks.
    for d in (1, 0b100):
        for epsilon in (1, 2):
            rhs = 1 ^ mul(0b100 ^ mul(d, d), 1 << epsilon)
            assert rhs.bit_count() == 3
    print("Factorization, periods, normalized syndromes and sparse identities passed.")


if __name__ == "__main__":
    main()
