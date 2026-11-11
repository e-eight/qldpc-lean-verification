"""Closed-form GF(2)[T] checks for valuation-energy.md; no support search."""


def mul(left: int, right: int) -> int:
    result = 0
    while right:
        if right & 1:
            result ^= left
        left <<= 1
        right >>= 1
    return result


def power(poly: int, exponent: int) -> int:
    result = 1
    for _ in range(exponent):
        result = mul(result, poly)
    return result


def degree(poly: int) -> int:
    return poly.bit_length() - 1


def ord_zero(poly: int) -> int:
    assert poly
    return (poly & -poly).bit_length() - 1


def at_one_plus_u(poly: int) -> int:
    result = 0
    for exponent in range(poly.bit_length()):
        if poly >> exponent & 1:
            result ^= power(0b11, exponent)
    return result


def ord_one(poly: int) -> int:
    return ord_zero(at_one_plus_u(poly))


def main() -> None:
    t = 0b110
    big_b = 1 ^ (1 << 3) ^ (1 << 4)
    assert big_b ^ (t << 2) == 1
    for name, lam, expected_d, expected_degrees in (
        ("F", 1, 1 ^ 2 ^ 4 ^ (1 << 6) ^ (1 << 8), (4, 6, 2, 4)),
        ("reversed B", 4, 1 ^ (1 << 5) ^ (1 << 8), (6, 6, 4, 6)),
    ):
        annihilator = mul(big_b, big_b) ^ mul(t, mul(lam, lam))
        assert annihilator == expected_d
        assert ord_zero(annihilator) == ord_one(annihilator) == 0
        multipliers = (
            big_b ^ mul(t, mul(lam, lam)),
            mul(big_b, t),
            mul(lam, t),
            mul(lam, mul(t, t)),
        )
        assert tuple(map(degree, multipliers)) == expected_degrees
        assert tuple(map(ord_one, multipliers)) == (0, 1, 1, 2)
        e = degree(lam)
        assert tuple(map(ord_zero, multipliers)) == (0, 1, e + 1, e + 2)
        # Only these two named closed-form examples, not candidate enumeration.
        for label, seed in (("1", 1), ("t", t)):
            packet = mul(annihilator, seed)
            h = mul(mul(big_b, t), seed)
            k = mul(mul(lam, mul(t, t)), seed)
            c_next = mul(lam, h)
            assert mul(t, packet) ^ mul(big_b, h) ^ mul(lam, k) == 0
            assert mul(t, c_next) ^ mul(big_b, k) == 0
            physical = (packet ^ (h << 2), h, c_next ^ (k << 2), k)
            assert physical == tuple(mul(p, seed) for p in multipliers)
            assert max(map(degree, physical)) == degree(seed) + 6 <= 18
            m = ord_one(seed)
            bound = (1 << m.bit_count()) + 2 * (1 << (m + 1).bit_count())
            bound += 1 << (m + 2).bit_count()
            weight = sum(p.bit_count() for p in physical)
            assert weight >= bound
            if seed == 1:
                assert weight == 13
            print(f"{name}, S={label}: physical weight={weight}, bound={bound}")
        # One specified full cycle per direction; substitute every tested equation.
        canonical = [0] * 19
        injections = [0] * 19
        canonical[0] = annihilator
        canonical[2] = mul(t, annihilator)
        injections[2] = mul(big_b, power(t, 2))
        injections[3] = mul(lam, power(t, 3))
        canonical[3] = mul(lam, injections[2])
        for i in range(2, 19):
            assert canonical[i] == (
                mul(t, canonical[i - 2])
                ^ mul(lam, injections[i - 1])
                ^ mul(big_b, injections[i - 2])
            )
        pairs = [(c ^ (h << 2), h) for c, h in zip(canonical, injections, strict=True)]
        assert max(degree(p) for pair in pairs for p in pair) <= 18
        weights = [sum(p.bit_count() for p in pair) for pair in pairs]
        assert sum(weights) == 19
        assert tuple(weights[i] for i in (0, 2, 3)) == ((5, 8, 6) if lam == 1 else (3, 10, 6))
        if lam == 1:
            assert canonical[0] == annihilator and canonical[1] ^ injections[0] == 0
        else:
            assert pairs[17] == pairs[18] == (0, 0)
        print(f"{name}: specified full mixed cycle has weight 19 and zero charge.")
    eighth = power(t, 8)
    assert eighth == (1 << 8) ^ (1 << 16)
    assert (ord_zero(eighth), ord_one(eighth), degree(eighth)) == (8, 8, 16)
    assert power(t, 7).bit_count() == 8 and eighth.bit_count() == 2
    assert mul(t, power(t, 7)) == eighth
    c, h = 4, 1
    assert (c ^ (h << 2)).bit_count() + h.bit_count() == c.bit_count() == 1
    # Ten terms of the stated monomial packet, not a search over packets.
    energy = sum(1 << j.bit_count() for j in range(10))
    assert energy == sum(power(t, j).bit_count() for j in range(10)) == 33
    print("Closed-form identities and counterexamples passed; packet energy=33.")


if __name__ == "__main__":
    main()
