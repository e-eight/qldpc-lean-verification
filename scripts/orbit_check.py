"""Orbit-packing lower bounds for two-block abelian group codes (cyclic GB,
quadricycle). See CERTIFICATES.md, instances B and C.

Setup: H_X = [A | B] over F2[G], with G = Z_l1 x ... x Z_lr. Qubit i of each
block is the mixed-radix (row-major) index of a group element. Each generator
shift is verified to preserve rowspace(H_X) and rowspace(H_Z) before use, so a
wrong guess about the indexing fails the check instead of producing a bound.
The duality (A, g) <-> (B, g^-1), which maps X checks onto Z checks for
H_Z = [B^T | A^T], is verified the same way before use.

For a representative w of one Pauli type:
  * class(v) = pairing of v with a basis of opposite-type logicals;
  * S = {g in G : class(g.w) = class(w)}; the S-orbit of w is a family of
    same-class representatives;
  * if c is the largest number of family members on any one qubit, then every
    opposite-type logical that anticommutes with class(w) has weight >= |S|/c;
  * translating the family by g gives the same bound for class(g.w).
Representatives used: each stored witness and the dual image of the other
side's witness. The bound covers an opposite class a when some family's class b
has a.b = 1. A side is fully certified when every nonzero class is covered.

Soundness check built in: a stored witness of the target side that meets a
covered class must not be lighter than that class's bound; the script aborts
if it is.

Exploratory: this shows that a certificate exists. It is not a trusted checker.

Usage: python scripts/orbit_check.py <code json or slug> ...
"""
import itertools
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
from common import gf2  # noqa: E402


def translation_group(dims):
    G = int(np.prod(dims))
    coords = np.array(np.unravel_index(np.arange(G), dims)).T

    def perm(shift):
        idx = np.ravel_multi_index(((coords + shift) % dims).T, dims)
        return np.concatenate([idx, idx + G])  # qubit i -> perm[i]

    return coords, perm


def apply(p, v):
    out = np.zeros_like(v)
    out[p] = v
    return out


def maps_into(H_from, H_to, p):
    """Does permuting the columns of H_from by p land inside rowspace(H_to)?"""
    Hp = np.zeros_like(H_from)
    Hp[:, p] = H_from
    return gf2.rank(np.vstack([H_to, Hp])) == gf2.rank(H_to)


def duality_perm(dims, coords, G):
    """(A, g) <-> (B, g^-1): maps the X checks of [A|B], [B^T|A^T] onto the Z checks."""
    inv = np.ravel_multi_index(((-coords) % dims).T, dims)
    return np.concatenate([inv + G, inv])


def family(w, H_opp, L_opp, coords, perm, G):
    """Orbit family of w.

    Returns ({class: V} for each class in the G-orbit of class(w), V, |S|, c,
    the best V any representative of this weight could reach under the same S,
    the block split of w, and one representative per class).
    """
    assert not (H_opp @ w % 2).any(), "representative is not a logical of this type"
    base = tuple(int(x) for x in L_opp @ w % 2)
    assert any(base), "representative is trivial"
    members, reps = [], {}
    for g in coords:
        gw = apply(perm(g), w)
        b = tuple(int(x) for x in L_opp @ gw % 2)
        reps.setdefault(b, gw)
        if b == base:
            members.append(gw)
    S = len(members)
    c = int(np.sum(members, axis=0).max())
    best_c = math.ceil(int(w.sum()) / (2 * G // S))  # weight spread evenly over S-cosets
    split = (int(w[:G].sum()), int(w[G:].sum()))
    V = S / c
    return {b: V for b in reps}, V, S, c, S / best_c, split, reps


def combine(class_V, k):
    """Return (min over nonzero opposite classes a of max{V_b : a.b = 1}, #uncovered)."""
    worst, uncovered = None, 0
    for a in itertools.product((0, 1), repeat=k):
        if not any(a):
            continue
        vals = [V for b, V in class_V.items() if sum(x * y for x, y in zip(a, b)) % 2]
        if not vals:
            uncovered += 1
            continue
        worst = max(vals) if worst is None else min(worst, max(vals))
    return worst, uncovered


def main(args):
    for arg in args:
        path = common.code_file(arg)
        slug = os.path.basename(path)[:-5]
        d = common.load(path)
        n, k = d["n"], d["k"]
        dims = np.array(common.group_dims(slug, n))
        HX = common.matrix(d["checks"]["X"], n)
        HZ = common.matrix(d["checks"]["Z"], n)
        coords, perm = translation_group(dims)
        G = len(coords)
        gens = [np.eye(len(dims), dtype=int)[i] for i in range(len(dims))]
        if not all(maps_into(HX, HX, perm(e)) and maps_into(HZ, HZ, perm(e)) for e in gens):
            print(f"{slug:10s} translations NOT verified as automorphisms; skipped")
            continue
        pi = duality_perm(dims, coords, G)
        dual_ok = maps_into(HX, HZ, pi) and maps_into(HZ, HX, pi)
        LX = gf2.logical_basis(HZ, HX)  # X-type logicals
        LZ = gf2.logical_basis(HX, HZ)  # Z-type logicals
        assert len(LX) == len(LZ) == k
        wit = {}
        for s in ("X", "Z"):
            wit[s] = np.zeros(n, dtype=np.int8)
            wit[s][d["distance"][s]["witness"]] = 1
        commute = int(wit["X"] @ wit["Z"] % 2) == 0
        out = []
        # d_X is bounded by Z-type families (they meet X logicals): the Z witness
        # and the dual image of the X witness. d_Z mirrors it.
        for tgt, own, H_opp, L_opp in (("X", "Z", HX, LX), ("Z", "X", HZ, LZ)):
            claim = d["distance"][tgt]["value"]
            sources = [("witness", wit[own])]
            if dual_ok:
                sources.append(("dual", apply(pi, wit[tgt])))
            class_V, notes = {}, []
            for label, w in sources:
                cv, V, S, c, Vmax, split, reps = family(w, H_opp, L_opp, coords, perm, G)
                for b, v in cv.items():
                    class_V[b] = max(class_V.get(b, 0), v)
                    if int(wit[tgt] @ reps[b] % 2) and int(wit[tgt].sum()) < math.ceil(v - 1e-9):
                        raise SystemExit(f"{slug}: bound {v:.2f} beats a stored witness: BUG")
                notes.append(f"{label}: |S|={S} c={c} split={split} V={V:.1f} "
                             f"(best {Vmax:.1f}) classes={len(cv)}")
            worst, unc = combine(class_V, k)
            lb = math.ceil(worst - 1e-9) if worst is not None else None
            if unc:
                verdict = f"{unc} class(es) uncovered; covered ones >= {lb}"
            else:
                verdict = "EXACT" if lb >= claim else f"d{tgt} >= {lb}"
            out.append(f"d{tgt} (claim {claim}): {verdict}\n        " + "\n        ".join(notes))
        print(f"{slug:10s} G={tuple(int(x) for x in dims)} dual={'ok' if dual_ok else 'FAILED'} "
              f"witnesses commute={commute}\n    " + "\n    ".join(out))


if __name__ == "__main__":
    main(sys.argv[1:])
