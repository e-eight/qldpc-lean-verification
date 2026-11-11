#!/usr/bin/env python3
"""Replay the nine symbolic checks used while drafting ChargeAlgebra.lean.

Run with Python 3.13:
    python analytical/notes/charge-algebra_check.py

No imports, packages, input files, or network access are required. An integer
encodes a polynomial in F2[Y]: bit n is the coefficient of Y^n. XOR is
polynomial addition (also subtraction); shifts multiply by powers of Y.
Multiplication below is carryless polynomial multiplication. Remainders use
long division by the monic polynomial r, cancelling the highest term at each
step. This checks polynomial identities, not an enumeration of ring elements.

Each check forms lhs + rhs, which equals lhs - rhs in characteristic two,
and requires its remainder modulo r to be zero. These independent arithmetic
checks do not replace Lean elaboration or the kernel axiom audit.
"""


def mul(a, b):
    """Multiply two bit-encoded polynomials over F2, without reduction."""
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out


def pw(a, n):
    """Compute a nonnegative polynomial power, without reduction."""
    out = 1
    for _ in range(n):
        out = mul(out, a)
    return out


def rem(a, b):
    """Compute the polynomial remainder by monic long division over F2."""
    if b == 0:
        raise ValueError("The divisor polynomial must be nonzero")
    while a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def polynomial(a):
    """Display every nonzero coefficient explicitly, in ascending degree."""
    return (
        " + ".join(
            "1" if n == 0 else "Y" if n == 1 else f"Y^{n}"
            for n in range(a.bit_length())
            if (a >> n) & 1
        )
        or "0"
    )


def main():
    # Exact inputs and nine expressions from the original drafting check.
    y = 2
    r = 1 ^ y ^ pw(y, 2) ^ pw(y, 6) ^ pw(y, 8)
    x = 1 ^ pw(y, 2) ^ pw(y, 5) ^ pw(y, 6)
    t = y ^ pw(y, 2)
    identities = {
        "t inverse": mul(t, 1 ^ pw(y, 5) ^ pw(y, 6)) ^ 1,
        "y inverse": mul(y, 1 ^ y ^ pw(y, 5) ^ pw(y, 7)) ^ 1,
        "x squared": pw(x, 2) ^ 1 ^ pw(y, 5) ^ pw(y, 6),
        "x squared times t": mul(pw(x, 2), t) ^ 1,
        "f relation": x ^ pw(x, 2) ^ pw(y, 2),
        "g relation": 1 ^ mul(pw(x, 2), y) ^ mul(pw(x, 2), pw(y, 2)),
        "p(x)": pw(x, 8) ^ pw(x, 5) ^ 1,
        "t polynomial": t ^ pw(x, 6) ^ pw(x, 3),
        "y polynomial": y ^ pw(x, 6) ^ pw(x, 3) ^ x ^ pw(x, 2),
    }
    equations = {
        "t inverse": "t * (1 + y^5 + y^6) = 1",
        "y inverse": "y * (1 + y + y^5 + y^7) = 1",
        "x squared": "x^2 = 1 + y^5 + y^6",
        "x squared times t": "x^2 * t = 1",
        "f relation": "x + x^2 + y^2 = 0",
        "g relation": "1 + x^2*y + x^2*y^2 = 0",
        "p(x)": "x^8 + x^5 + 1 = 0",
        "t polynomial": "t = x^6 + x^3",
        "y polynomial": "y = x^6 + x^3 + x + x^2",
    }
    print("Inputs in F2[Y]; identities interpreted in F2[Y]/(r):")
    for name, value in (("r", r), ("y", y), ("x", x), ("t", t)):
        print(f"  {name} = {polynomial(value)}")
    print("Manipulation: expand lhs + rhs over F2, then divide by r.")
    failures = []
    for name, expression in identities.items():
        remainder = rem(expression, r)
        print(f"\n{name}: {equations[name]}")
        print(f"  expanded lhs + rhs = {polynomial(expression)}")
        print(f"  remainder modulo r = {polynomial(remainder)}")
        print(f"  result: {'PASS' if remainder == 0 else 'FAIL'}")
        if remainder != 0:
            failures.append(name)
    if failures:
        raise SystemExit(f"Failed checks: {', '.join(failures)}")
    print("\nNine symbolic polynomial remainder checks passed over F2; no element enumeration.")


if __name__ == "__main__":
    main()
