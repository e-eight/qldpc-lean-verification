"""Line-packing certificate for laid-out codes (CERTIFICATES.md, instance A).

Qubits are grouped into lines of the layout: same x, same y, and both diagonals
mod the side length. A line that commutes with the opposite checks is a logical
representative, and its class is read off by pairing with a basis of
opposite-type logicals. Lines of one orientation are pairwise disjoint. So a
class with V disjoint representatives forces weight >= V on every logical that
anticommutes with it. If the classes used span the logical space, d >= the
smallest V in the span.

Exploratory: this shows that a certificate exists. It is not a trusted checker.

Usage: python scripts/line_check.py <code json or slug> ...
"""
import os
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
from common import gf2  # noqa: E402


def lines(coords):
    side = len({c[0] for c in coords})
    keys = {
        "col": lambda c: c[0],
        "row": lambda c: c[1],
        "diag": lambda c: round(c[0] + c[1]) % side,
        "anti": lambda c: round(c[0] - c[1]) % side,
    }
    out = {}
    for name, key in keys.items():
        groups = defaultdict(list)
        for q, c in enumerate(coords):
            groups[key(c)].append(q)
        out[name] = list(groups.values())
    return out


def side_bound(H_opp, opp_logicals, n, line_sets):
    """Lower bound on the distance of the logicals that these lines meet."""
    k = len(opp_logicals)
    best = {}  # class vector -> most disjoint representatives in one orientation
    for groups in line_sets.values():
        per_class = defaultdict(int)
        for g in groups:
            v = np.zeros(n, dtype=np.int8)
            v[g] = 1
            if (H_opp @ v % 2).any():
                continue  # not a logical
            b = tuple(int(x) for x in (opp_logicals @ v) % 2)
            if any(b):
                per_class[b] += 1
        for b, cnt in per_class.items():
            best[b] = max(best.get(b, 0), cnt)
    # Greedy by count gives the basis that maximizes the minimum count (matroid
    # bottleneck), so no subset enumeration is needed.
    chosen = []
    for b in sorted(best, key=lambda b: -best[b]):
        if gf2.rank(np.array(chosen + [b], dtype=np.int8)) > len(chosen):
            chosen.append(b)
        if len(chosen) == k:
            return min(best[c] for c in chosen)
    return None  # the lines found do not span the logical space


def main(args):
    for arg in args:
        d = common.load(common.code_file(arg))
        n = d["n"]
        HX = common.matrix(d["checks"]["X"], n)
        HZ = common.matrix(d["checks"]["Z"], n)
        LX = gf2.logical_basis(HZ, HX)  # X-type logicals: ker HZ mod rowspace HX
        LZ = gf2.logical_basis(HX, HZ)  # Z-type logicals
        ls = lines(d["locality"]["coordinates"])
        dx_lb = side_bound(HX, LX, n, ls)  # Z-type lines bound d_X
        dz_lb = side_bound(HZ, LZ, n, ls)  # X-type lines bound d_Z
        cx, cz = d["distance"]["X"]["value"], d["distance"]["Z"]["value"]
        exact = dx_lb is not None and dz_lb is not None and dx_lb >= cx and dz_lb >= cz
        print(f"{d['name'][:46]:46s} k={len(LX)} claim dX={cx:2d} dZ={cz:2d}  "
              f"line bound dX>={dx_lb} dZ>={dz_lb}  {'EXACT' if exact else ''}")


if __name__ == "__main__":
    main(sys.argv[1:])
