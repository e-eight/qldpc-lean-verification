"""Constrained search for orbit-certificate representatives in k = 2
two-block codes (CHECKS_AND_RESULTS.md, "Targets for closing the k = 2 codes").

What it looks for: Z-logicals in each of the three nonzero logical classes
whose weight is spread evenly over the two blocks. The translation group must
fix every class; this is checked before the search starts. Given that:
  * a representative with block split (a, b) proves weight >= |G| / max(a, b)
    on every opposite-type logical it anticommutes with;
  * an A-heavy and a B-heavy representative of one class, weighted to even out
    the coverage, prove |G| (a_i - b_i + b_j - a_j) / (a_i b_j - a_j b_i).
With k = 2 the distance bound is the median of the three class values
(CERTIFICATES.md). The dual map turns this Z-side certificate into the X-side
one.

How: random information sets on ker(H_X). Each trial orders the columns at
random, reduces a kernel basis with the repo's C++ RREF, and scans the
systematic rows and all their pairwise sums. Every nontrivial Z-logical up to
the weight cap is classified by pairing with an X-logical basis, and one is kept
per (class, split). The search stops once the certificate closes, or at the
trial or time budget.

Refutations: a Z-logical lighter than the claimed d_Z, or one whose dual image
is lighter than the claimed d_X, contradicts a board claim. It is re-validated
with the user's audit harness (research/audits/leader_audit.validate_witness)
and written at once to data/refutations/ with the harness's atomic writer.

Exploratory. The record is the independent re-derivation by
verify_orbit_k2.py --reps-dir, not this script's own evaluation.

Usage: python scripts/class_search.py [--trials N] [--seconds S] [--seed s] <code json or slug>
"""

import argparse
import json
import math
import os
import sys
import tempfile
import time
from fractions import Fraction

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
from common import gf2  # noqa: E402

BLOCK = 64  # rows per block in the pairwise scan
REPS_DIR = os.path.join(common.DATA, "reps")
REFUTATIONS_DIR = os.path.join(common.DATA, "refutations")


def pack(M):
    """Rows of a 0/1 matrix as little-endian uint64 words."""
    M = np.atleast_2d(np.asarray(M, dtype=np.uint8))
    pad = (-M.shape[1]) % 64
    if pad:
        M = np.hstack([M, np.zeros((M.shape[0], pad), dtype=np.uint8)])
    return np.packbits(M, axis=1, bitorder="little").view(np.uint64)


def unpack(words, n):
    return np.nonzero(np.unpackbits(words.view(np.uint8), bitorder="little")[:n])[0]


def popcount(words):
    return int(np.bitwise_count(words).sum())


def write_json(path, payload):
    """Atomic write, so a killed run never leaves a half-written file."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    fd, tmp = tempfile.mkstemp(
        dir=os.path.dirname(path), prefix=os.path.basename(path) + ".", suffix=".tmp"
    )
    with os.fdopen(fd, "w") as fh:
        json.dump(payload, fh, indent=1)
        fh.write("\n")
    os.chmod(tmp, 0o644)
    os.replace(tmp, path)


def class_value(splits, G):
    """Best exact orbit-family value for one class from its (a, b) splits."""
    best, how = Fraction(0), []
    for a, b in splits:
        v = Fraction(G, max(a, b))
        if v > best:
            best, how = v, [(a, b)]
    for ai, bi in [s for s in splits if s[0] > s[1]]:
        for aj, bj in [s for s in splits if s[0] < s[1]]:
            v = Fraction(G * ((ai - bi) + (bj - aj)), ai * bj - aj * bi)
            if v > best:
                best, how = v, [(ai, bi), (aj, bj)]
    return best, how


def certificate(per_class, G):
    """(bound, {class: (value, splits used)}) with bound = ceil(median of 3 class values)."""
    vals = {c: class_value(list(reps), G) for c, reps in per_class.items()}
    three = sorted([v for v, _ in vals.values()] + [Fraction(0)] * (3 - len(vals)))
    return math.ceil(three[1]), vals


def translation_perms(dims):
    G = int(np.prod(dims))
    coords = np.array(np.unravel_index(np.arange(G), dims)).T

    def perm(shift):
        idx = np.ravel_multi_index(((coords + shift) % dims).T, dims)
        return np.concatenate([idx, idx + G])

    gens = [perm(np.eye(len(dims), dtype=int)[i]) for i in range(len(dims))]
    inv = np.ravel_multi_index(((-coords) % dims).T, dims)
    return gens, np.concatenate([inv + G, inv])


def maps_into(H_from, H_to, p):
    Hp = np.zeros_like(H_from)
    Hp[:, p] = H_from
    return gf2.rank(np.vstack([H_to, Hp])) == gf2.rank(H_to)


def moved(p, v):
    out = np.zeros_like(v)
    out[p] = v
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("code")
    ap.add_argument("--trials", type=int, default=20000)
    ap.add_argument("--seconds", type=float, default=600)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument(
        "--seed-trials",
        type=int,
        default=20000,
        help="trials for each C++ constrained RIS seeding run",
    )
    args = ap.parse_args()

    try:
        import gf2_fast
    except ImportError as exc:
        raise SystemExit(
            "Build the optional accelerator first: "
            "uv run --group search python scripts/build_fast_backend.py"
        ) from exc

    # Load the accelerator before the audit helper changes sys.path transitively.
    sys.path.insert(0, os.path.join(common.REPO, "research", "audits"))
    import leader_audit

    path = common.code_file(args.code)
    slug = os.path.basename(path)[:-5]
    d = common.load(path)
    n, k = d["n"], d["k"]
    dims = np.array(common.group_dims(slug, n))
    G = int(np.prod(dims))
    assert k == 2 and 2 * G == n, f"{slug}: needs k = 2 and n = 2|G|"
    HX = common.matrix(d["checks"]["X"], n)
    HZ = common.matrix(d["checks"]["Z"], n)

    gens, pi = translation_perms(dims)
    assert all(maps_into(HX, HX, p) and maps_into(HZ, HZ, p) for p in gens), (
        f"{slug}: translations not verified"
    )
    assert maps_into(HX, HZ, pi) and maps_into(HZ, HX, pi), f"{slug}: duality not verified"
    LX = gf2.logical_basis(HZ, HX)  # X-logical basis, used to read Z classes
    LZ = gf2.logical_basis(HX, HZ)
    LXp = pack(LX)

    def cls(words):
        return "".join(str(popcount(words & LXp[j]) % 2) for j in range(len(LXp)))

    # The mixing formula needs every translation to fix every class.
    for p in gens:
        for z in LZ:
            assert cls(pack(moved(p, z))[0]) == cls(pack(z)[0]), (
                f"{slug}: a translation moves a class"
            )

    claim = {s: d["distance"][s]["value"] for s in ("X", "Z")}
    target = min(claim.values())
    m_target = math.ceil(Fraction(G, target - 1)) - 1  # largest m with ceil(G/m) >= target
    cap = max(2 * m_target + 4, claim["Z"] + 4)
    maskA = pack(np.r_[np.ones(G), np.zeros(G)])[0]
    Kb = gf2_fast.kernel_basis(HX)

    per_class, supports = {}, {}  # class -> set of (a, b); (class, a, b) -> support
    refuted = {}

    def record(words, trial):
        c = cls(words)
        if c == "00":
            return False  # a stabilizer
        w = popcount(words)
        a = popcount(words & maskA)
        sup = [int(q) for q in unpack(words, n)]
        for side, support in (("Z", sup), ("X", sorted(int(q) for q in pi[sup]))):
            if w < claim[side] and w < refuted.get(side, math.inf):
                ok, why = leader_audit.validate_witness(n, HX, HZ, side, w, support)
                if not ok:
                    raise SystemExit(
                        f"{slug}: proposed {side} logical of weight {w} failed validation: {why}"
                    )
                best = {
                    "weight": w,
                    "side": side,
                    "support": support,
                    "tool": "class_search.py",
                    "seed": args.seed,
                    "trial": trial,
                }
                leader_audit._write_witness(
                    os.path.join(REFUTATIONS_DIR, f"{slug}.{side}.witness.json"),
                    leader_audit._best_payload(
                        f"codes/{slug}.json", n, k, claim[side], best, leader_audit.VERDICT_REFUTED
                    ),
                )
                refuted[side] = w
                print(
                    f"{slug}: REFUTATION {side}: weight {w} < claim {claim[side]} (validated, saved)",
                    flush=True,
                )
        key = (c, a, w - a)
        if key in supports:
            return False
        supports[key] = sup
        per_class.setdefault(c, set()).add((a, w - a))
        return True

    # Earlier runs' representatives, re-checked, so reruns accumulate.
    earlier = []
    reps_path = os.path.join(REPS_DIR, f"{slug}.json")
    if os.path.exists(reps_path):
        earlier = [r["support"] for r in common.load(reps_path)["archive"]]
    for sup in earlier:
        v = np.zeros(n, dtype=np.int8)
        v[sup] = 1
        if not (HX @ v % 2).any():
            record(pack(v)[0], trial=-1)
    for w0 in (d["distance"]["Z"]["witness"], pi[d["distance"]["X"]["witness"]]):
        v = np.zeros(n, dtype=np.uint8)
        v[w0] = 1
        record(pack(v)[0], trial=-1)

    rng = np.random.default_rng(args.seed)
    t0, trials_done = time.time(), 0
    bound, vals = certificate(per_class, G)

    def save(final=False):
        cert_reps = []
        for c, (_v, used) in vals.items():
            for a, b in used:
                cert_reps.append({"class": c, "split": [a, b], "support": supports[(c, a, b)]})
        write_json(
            os.path.join(REPS_DIR, f"{slug}.json"),
            {
                "code": slug,
                "n": n,
                "k": k,
                "group": [int(x) for x in dims],
                "claim": claim,
                "search": {
                    "tool": "class_search.py",
                    "trials": trials_done,
                    "seconds": round(time.time() - t0, 1),
                    "seed": args.seed,
                    "cap": cap,
                    "m_target": m_target,
                    "final": final,
                },
                "certificate": {
                    "bound": bound,
                    "closed": bound >= target,
                    "class_values": {c: str(v) for c, (v, _) in vals.items()},
                    "reps": cert_reps,
                },
                "archive": [
                    {"class": c, "split": [a, b], "support": s}
                    for (c, a, b), s in sorted(supports.items())
                ],
            },
        )

    # Seed every class with the repo's C++ constrained RIS: for each nonzero
    # X-class x, the lightest Z-logical anticommuting with x (two classes at a
    # time). These lightest weights also cap what any certificate can reach.
    lightest = {}
    xs = {"x0": LX[0], "x1": LX[1], "x0+x1": (LX[0] + LX[1]) % 2}
    for label, x in xs.items():
        w, sup = gf2_fast.dem_rand_witness(
            HX,
            x[None, :].astype(np.int8),
            trials=args.seed_trials,
            seed=args.seed,
            pair_depth=24,
            threads=1,
        )
        if sup:
            v = np.zeros(n, dtype=np.uint8)
            v[list(sup)] = 1
            words = pack(v)[0]
            lightest[label] = {"weight": int(w), "class": cls(words)}
            record(words, trial=-1)
    bound, vals = certificate(per_class, G)
    save()
    print(
        f"{slug}: seeded bound {bound} (target {target}, m_target {m_target}, cap {cap}, K {Kb.shape[0]}); "
        f"lightest anticommuting with each X-class: {lightest}",
        flush=True,
    )
    while trials_done < args.trials and time.time() - t0 < args.seconds and bound < target:
        order = rng.permutation(n)
        R, piv = gf2_fast.gf2_rref(Kb[:, order])
        R = np.asarray(R[: len(piv)])
        Rorig = np.empty_like(R)
        Rorig[:, order] = R
        P = pack(Rorig)
        new = False
        cands = [P[np.bitwise_count(P).sum(axis=1) <= cap]]
        # All pairwise sums, a block of rows at a time to bound memory.
        for s in range(0, len(P), BLOCK):
            X = P[s : s + BLOCK, None, :] ^ P[None, :, :]
            ii, jj = np.nonzero(np.bitwise_count(X).sum(axis=2) <= cap)
            keep = (s + ii) < jj  # each unordered pair once
            cands.append(X[ii[keep], jj[keep]])
        C = np.concatenate(cands)
        # Classify all candidates at once and skip stabilizers (class 00), which
        # dominate the low-weight hits and can never refute a claim.
        par = np.stack(
            [np.bitwise_count(C & LXp[j]).sum(axis=1) % 2 for j in range(len(LXp))], axis=1
        )
        for row in np.nonzero(par.any(axis=1))[0]:
            new |= record(C[row], trials_done)
        trials_done += 1
        if new:
            bound, vals = certificate(per_class, G)
            save()
            print(
                f"{slug}: trial {trials_done} t={time.time() - t0:.0f}s bound {bound} "
                f"classes {{{', '.join(f'{c}: {float(v):.2f}' for c, (v, _) in sorted(vals.items()))}}}",
                flush=True,
            )
    save(final=True)
    status = "CLOSED (exact)" if bound >= target else f"open: best bound {bound} < {target}"
    print(
        f"{slug}: done after {trials_done} trials, {time.time() - t0:.0f}s: {status}; "
        f"refutations: {refuted or 'none'}",
        flush=True,
    )


if __name__ == "__main__":
    main()
