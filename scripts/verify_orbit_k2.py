"""Independent re-derivation of k = 2 orbit certificates for two-block abelian
codes. It uses only rank tests against the stabilizer row spaces: no logical
bases and no class coordinates.

Representatives (Z-type): the stored Z witness, the dual image of the stored X
witness, and, with --reps-dir, the certificate representatives that
class_search.py wrote to DIR/<slug>.json. The file's class labels and values are
ignored; every representative is re-checked here. X-type representatives are
the stored X witness and the dual images of the Z-type ones.

Checks, per code and side:
  1. k = 2 from ranks. Every generator translation maps every row of H_X and H_Z
     into its own row space, and the duality (A,g) <-> (B,g^-1) maps H_X's rows
     into H_Z's row space and back.
  2. Each representative is a logical of the right type and is not a stabilizer.
  3. Each generator translation keeps each representative in its class
     (rep + t(rep) is a stabilizer). So the whole group fixes the class, and a
     qubit of block A lies in exactly a = |rep ∩ A| translates.
  4. Representatives are grouped into classes by testing whether their sums are
     stabilizers.

Class value: the best single orbit, |G| / max(a, b), or the best weighted pair
of an A-heavy and a B-heavy orbit, |G| (a_i - b_i + b_j - a_j) /
(a_i b_j - a_j b_i), computed exactly with fractions. With k = 2, every nonzero
opposite class anticommutes with exactly two of the three nonzero classes. So
the side bound is the ceiling of the median of the three class values, with a
missing class counting as 0.

Usage: python scripts/verify_orbit_k2.py [--reps-dir DIR] <code json or slug> ...
"""

import argparse
import json
import math
import os
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
from common import gf2  # noqa: E402


class Rejected(Exception):
    pass


def class_value(splits, G):
    best = Fraction(0)
    for a, b in splits:
        best = max(best, Fraction(G, max(a, b)))
    for ai, bi in splits:
        for aj, bj in splits:
            if ai > bi and aj < bj:
                best = max(best, Fraction(G * ((ai - bi) + (bj - aj)), ai * bj - aj * bi))
    return best


def verify(path, reps_dir):
    slug = os.path.basename(path)[:-5]
    d = common.load(path)
    n = d["n"]
    dims = np.array(common.group_dims(slug, n))
    G = int(np.prod(dims))
    HX = common.matrix(d["checks"]["X"], n)
    HZ = common.matrix(d["checks"]["Z"], n)
    rX, rZ = gf2.rank(HX), gf2.rank(HZ)
    coords = np.array(np.unravel_index(np.arange(G), dims)).T
    gens = []
    for i in range(len(dims)):
        idx = np.ravel_multi_index(((coords + np.eye(len(dims), dtype=int)[i]) % dims).T, dims)
        gens.append(np.concatenate([idx, idx + G]))
    inv = np.ravel_multi_index(((-coords) % dims).T, dims)
    pi = np.concatenate([inv + G, inv])

    def move(p, M):
        out = np.zeros_like(M)
        out[..., p] = M
        return out

    if n - rX - rZ != 2 or 2 * G != n:
        raise Rejected(f"needs k = 2 and n = 2|G| (k = {n - rX - rZ})")
    if not all(gf2.rank(np.vstack([H, move(p, H)])) == gf2.rank(H) for p in gens for H in (HX, HZ)):
        raise Rejected("translations are not automorphisms")
    if (
        gf2.rank(np.vstack([HZ, move(pi, HX)])) != rZ
        or gf2.rank(np.vstack([HX, move(pi, HZ)])) != rX
    ):
        raise Rejected("duality does not map the checks onto each other")

    def vec(support):
        v = np.zeros(n, dtype=np.int8)
        v[list(support)] = 1
        return v

    wX, wZ = vec(d["distance"]["X"]["witness"]), vec(d["distance"]["Z"]["witness"])
    zreps = [wZ, move(pi, wX)]
    reps_file = os.path.join(reps_dir, f"{slug}.json") if reps_dir else None
    if reps_file and os.path.exists(reps_file):  # no file: stored witnesses only
        with open(reps_file) as fh:
            zreps += [vec(r["support"]) for r in json.load(fh)["certificate"]["reps"]]
    xreps = [wX] + [move(pi, z) for z in zreps]

    parts = []
    for target, reps, H_same, H_opp, r_same, wt in (
        ("d_X", zreps, HZ, HX, rZ, int(wX.sum())),
        ("d_Z", xreps, HX, HZ, rX, int(wZ.sum())),
    ):

        def stab(v, H_same=H_same, r_same=r_same):
            return gf2.rank(np.vstack([H_same, v])) == r_same

        classes = []  # [(one representative, set of splits)]
        for v in reps:
            if (H_opp @ v % 2).any():
                raise Rejected(f"{target}: a representative is not a logical")
            if stab(v):
                raise Rejected(f"{target}: a representative is a stabilizer")
            if not all(stab((move(p, v) + v) % 2) for p in gens):
                raise Rejected(f"{target}: a translation moves a representative's class")
            split = (int(v[:G].sum()), int(v[G:].sum()))
            for rep, splits in classes:
                if stab((rep + v) % 2):
                    splits.add(split)
                    break
            else:
                classes.append((v, {split}))
        if len(classes) > 3:
            raise Rejected(f"{target}: more than three classes with k = 2")
        values = sorted(
            [class_value(s, G) for _, s in classes] + [Fraction(0)] * (3 - len(classes))
        )
        lb = math.ceil(values[1])
        detail = ", ".join(f"{float(v):.2f}" for v in values)
        verdict = "EXACT" if lb >= wt else ("no full certificate" if lb == 0 else "")
        parts.append(f"{target} >= {lb} (class values {detail}; witness {wt}) {verdict}".rstrip())
    return " | ".join(parts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("codes", nargs="+")
    ap.add_argument("--reps-dir")
    args = ap.parse_args()
    for arg in args.codes:
        path = common.code_file(arg)
        name = os.path.basename(path)[:-5]
        try:
            print(f"{name:10s} {verify(path, args.reps_dir)}", flush=True)
        except Rejected as e:
            print(f"{name:10s} REJECTED: {e}", flush=True)


if __name__ == "__main__":
    main()
