"""Bounded numerical cross-check, outside the trusted Lean proof."""

import json
from itertools import product


def span(rows):
    result = {0}
    for row in rows:
        result |= {x ^ row for x in tuple(result)}
    return frozenset(result)


def spaces(n):
    result = {frozenset({0})}
    for x in range(1, 1 << n):
        result |= {span((*u, x)) for u in tuple(result)}
    return result


def dot(x, y):
    return (x & y).bit_count() % 2


def logicals(n, boundaries, checks):
    return [
        x for x in range(1 << n) if x not in boundaries and all(not dot(x, row) for row in checks)
    ]


def distance(vectors):
    return min(map(int.bit_count, vectors))


def old_spaces(n, u, v, s):
    return span((*u, s | (1 << n))), frozenset(b | (dot(s, b) << n) for b in v)


def parameters(n, u, v):
    return {
        "n": n,
        "k": n - (len(u).bit_length() - 1) - (len(v).bit_length() - 1),
        "rank_X": len(u).bit_length() - 1,
        "rank_Z": len(v).bit_length() - 1,
        "d_X": distance(logicals(n, u, v)),
        "d_Z": distance(logicals(n, v, u)),
    }


def main():
    checked = 0
    for n in range(4):
        for u, v in product(spaces(n), repeat=2):
            if any(dot(a, b) for a, b in product(u, v)):
                continue
            lx, lz = logicals(n, u, v), logicals(n, v, u)
            for s in range(1 << n):
                ou, ov = old_spaces(n, u, v, s)
                ox, oz = logicals(n + 1, ou, ov), logicals(n + 1, ov, ou)
                assert len(ou) == 2 * len(u) and len(ov) == len(v)
                assert len(ox) == 2 * len(lx) and len(oz) == len(lz)
                assert set(oz) == {z | (dot(s, z) << n) for z in lz}
                if lx:
                    a, b, c, d = map(distance, (lx, lz, ox, oz))
                    assert c == min(a, 1 + min((y ^ s).bit_count() for y in lx))
                    assert b <= d <= b + 1
                    assert (d == b + 1) == all(dot(s, z) for z in lz if z.bit_count() == b)
                    coset_weight = min((s ^ x).bit_count() for x in u)
                    assert a <= c + max(coset_weight - 1, 0)
                    assert min(a, b) >= min(c, d) - 1
                checked += 1
    assert checked == 583
    examples = []
    for name, n, xs, zs, s in [
        ("preserving", 4, [15], [15], 1),
        ("losing", 3, [], [3, 4], 7),
        ("increasing", 4, [15], [15], 3),
    ]:
        u, v = span(xs), span(zs)
        ou, ov = old_spaces(n, u, v, s)
        examples.append(
            {
                "name": name,
                "s": s,
                "old": parameters(n + 1, ou, ov),
                "new": parameters(n, u, v),
            }
        )
    assert [(e["old"]["d_X"], e["old"]["d_Z"]) for e in examples] == [(2, 2), (2, 2), (1, 2)]
    assert [(e["new"]["d_X"], e["new"]["d_Z"]) for e in examples] == [(2, 2), (2, 1), (2, 2)]
    print(
        json.dumps({"status": "success", "models_checked": checked, "examples": examples}, indent=2)
    )


if __name__ == "__main__":
    main()
