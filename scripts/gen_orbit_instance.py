"""Emit finite rank, logical-coverage, and weighted orbit certificates for Lean.

The Python class labels and reported bounds are not trusted. Classes are rebuilt
from the submitted matrices. Lean checks every emitted certificate independently.
"""

import argparse
import hashlib
import itertools
import json
from fractions import Fraction
from pathlib import Path

import common
import numpy as np
from common import gf2
from gen_lean_instance import rank_certificate


def mask(v):
    return sum(1 << int(q) for q in np.flatnonzero(v))


def solve(a, b):
    n = a.shape[1]
    reduced, pivots = gf2.rref(np.column_stack([a, b]))
    if n in pivots:
        raise ValueError("The proposed detector classes do not have dual logical witnesses.")
    x = np.zeros(n, dtype=np.int8)
    x[pivots] = reduced[: len(pivots), n]
    assert np.array_equal(a @ x % 2, b)
    return x


def build(slug):
    source = Path(common.code_file(slug))
    raw = source.read_bytes()
    d = json.loads(raw)
    n, target = d["n"], min(len(d["distance"][s]["witness"]) for s in ("X", "Z"))
    g = n // 2
    if n != 2 * g or common.group_dims(slug, n) != (g,):
        raise ValueError("This generator currently accepts cyclic two-block codes.")
    hx, hz = (common.matrix(d["checks"][s], n) for s in ("X", "Z"))
    if n - gf2.rank(hx) - gf2.rank(hz) != 2:
        raise ValueError("This instance generator requires k=2.")

    def vector(support):
        v = np.zeros(n, dtype=np.int8)
        v[support] = 1
        return v

    def dual(v):
        inv = (-np.arange(g)) % g
        return np.concatenate([v[g:][inv], v[:g][inv]])

    reps_path = Path(common.DATA) / "reps" / f"{slug}.json"
    saved = json.loads(reps_path.read_bytes()) if reps_path.exists() else None
    candidates = [
        vector(d["distance"]["Z"]["witness"]),
        dual(vector(d["distance"]["X"]["witness"])),
    ]
    if saved:
        candidates += [vector(r["support"]) for r in saved["certificate"]["reps"]]
    classes = []
    for v in candidates:
        if (hx @ v % 2).any() or gf2.in_rowspace(v, hz):
            raise ValueError("A saved representative is not a nontrivial Z logical.")
        for cls in classes:
            if gf2.in_rowspace(v ^ cls[0], hz):
                if not any(np.array_equal(v, old) for old in cls):
                    cls.append(v)
                break
        else:
            classes.append([v])
    good = []
    for cls in classes:
        best = None
        for a in cls:
            aa, ab = int(a[:g].sum()), int(a[g:].sum())
            value = Fraction(g, max(aa, ab))
            if best is None or value > best[0]:
                best = (value, [a, a], [1, 0])
        for a, b in itertools.product(cls, repeat=2):
            aa, ab, ba, bb = (int(v.sum()) for v in (a[:g], a[g:], b[:g], b[g:]))
            if aa > ab and ba < bb:
                weights = [bb - ba, aa - ab]
                cap = weights[0] * aa + weights[1] * ba
                value = Fraction(g * sum(weights), cap)
                if value > best[0]:
                    best = (value, [a, b], weights)
        if best is not None and best[0] > target - 1:
            good.append(best)
    if len(good) < 2:
        raise ValueError("Fewer than two independent classes reach the target.")
    good.sort(key=lambda item: item[0], reverse=True)
    good = good[:2]
    zbase = [item[1][0] for item in good]
    xbase = [dual(v) for v in zbase]
    xdual = [
        solve(
            np.vstack([hz, zbase]),
            np.r_[np.zeros(len(hz), dtype=np.int8), np.eye(2, dtype=np.int8)[i]],
        )
        for i in range(2)
    ]
    zdual = [
        solve(
            np.vstack([hx, xbase]),
            np.r_[np.zeros(len(hx), dtype=np.int8), np.eye(2, dtype=np.int8)[i]],
        )
        for i in range(2)
    ]
    families, caps = [], []
    for value, seeds, weights in good:
        family = []
        for seed, weight in zip(seeds, weights, strict=True):
            for shift in range(g):
                v = np.concatenate([np.roll(seed[:g], shift), np.roll(seed[g:], shift)])
                family.append((v, weight))
        coverage = sum(
            (weight * v.astype(np.int64) for v, weight in family), np.zeros(n, dtype=np.int64)
        )
        cap = int(coverage.max())
        assert Fraction(sum(w for _, w in family), cap) == value
        assert (target - 1) * cap < sum(w for _, w in family)
        for v, _ in family:
            assert not (hx @ v % 2).any()
            assert all(int(v @ x % 2) == int(seeds[0] @ x % 2) for x in xbase)
            assert not (hz @ dual(v) % 2).any()
            assert all(int(dual(v) @ z % 2) == int(dual(seeds[0]) @ z % 2) for z in zbase)
        families.append(family)
        caps.append(cap)
    return {
        "n": n,
        "g": g,
        "target": target,
        "hx": hx,
        "hz": hz,
        "zbase": zbase,
        "xbase": xbase,
        "xdual": xdual,
        "zdual": zdual,
        "zfamilies": families,
        "xfamilies": [[(dual(v), w) for v, w in f] for f in families],
        "caps": caps,
        "wx": vector(d["distance"]["X"]["witness"]),
        "wz": vector(d["distance"]["Z"]["witness"]),
        "source_sha256": hashlib.sha256(raw).hexdigest(),
        "reps_sha256": hashlib.sha256(reps_path.read_bytes()).hexdigest() if saved else None,
        "values": [str(item[0]) for item in good],
    }


def generate(slug, namespace):
    data = build(slug)
    n = data["n"]
    parts = [
        "import Mathlib.Data.Finset.Insert\n",
        f"/-! Generated by scripts/gen_orbit_instance.py from codes/{slug}.json.\n"
        f"Input SHA256: {data['source_sha256']}\nRepresentatives SHA256: {data['reps_sha256']} -/\n",
        f"namespace {namespace}\n",
        f"def nq : Nat := {n}\ndef target : Nat := {data['target']}\n",
    ]

    def emit(name, values, typ="Nat"):
        parts.append(f"def {name} : List ({typ}) := [\n  " + ",\n  ".join(map(str, values)) + "]\n")

    def supports(name, rows, size):
        emit(
            name,
            [
                "{" + ", ".join(f"⟨{int(q)}, by decide⟩" for q in np.flatnonzero(v)) + "}"
                for v in rows
            ],
            f"Finset (Fin {size})",
        )

    for side in ("x", "z"):
        h = data[f"h{side}"]
        supports(f"h{side}", h, n)
        ts, ps = rank_certificate(h)
        emit(f"t{side}", ts)
        emit(f"p{side}", [f"⟨{p}, by decide⟩" for p in ps], f"Fin {n}")
        supports(f"c{side}", h[:, ps].T, len(h))
        supports(f"{side}Base", data[f"{side}base"], n)
        emit(f"{side}BaseMasks", [mask(v) for v in data[f"{side}base"]])
        emit(f"{side}Dual", [mask(v) for v in data[f"{side}dual"]])
        for i, family in enumerate(data[f"{side}families"]):
            emit(f"{side}Family{i}", [f"({mask(v)}, {w})" for v, w in family], "Nat × Nat")
    for i, cap in enumerate(data["caps"]):
        parts.append(f"def cap{i} : Nat := {cap}\n")
    for side in ("x", "z"):
        parts.append(f"def w{side} : Nat := {mask(data['w' + side])}\n")
    parts.append(f"end {namespace}\n")
    return "\n".join(parts), data


def generate_checks(data_module, data_namespace):
    namespace = data_namespace.removesuffix("Data") + "Checks"
    lines = [
        "import QldpcVerification.Input.SparseCertificates",
        f"import {data_module}",
        "",
        f"namespace {namespace}",
        "open QldpcVerification.Input.Sparse",
        f"open {data_namespace}",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
    ]

    def check(name, proposition):
        lines.append(f"theorem {name} : {proposition} := by decide +kernel\n")

    check("comm", "commCheck hx hz = true")
    for side, opposite in [("x", "z"), ("z", "x")]:
        check(f"{side}Columns", f"columnCheck h{side} p{side} c{side} = true")
        check(f"{side}Pivots", f"pivotCheck t{side} c{side} = true")
        check(
            f"{side}BaseVectors",
            f"∀ i : Fin 2, vectorCheck ({side}BaseMasks.get i) ({side}Base.get i) = true",
        )
        check(
            f"{side}BaseKernel",
            f"∀ i : Fin 2, kernelCheck h{opposite} ({side}BaseMasks.get i) = true",
        )
        check(
            f"{side}DualKernel", f"∀ i : Fin 2, kernelCheck h{opposite} ({side}Dual.get i) = true"
        )
        check(f"{side}Pairing", f"pairingCheck {opposite}Base {side}Dual = true")
        for i in range(2):
            check(
                f"{side}Class{i}",
                f"familyCheck h{opposite} {opposite}Base ({side}BaseMasks.get ⟨{i}, by decide⟩) {side}Family{i} = true",
            )
            check(f"{side}Cap{i}", f"capCheck nq {side}Family{i} cap{i} = true")
        check(f"w{side}Kernel", f"kernelCheck h{opposite} w{side} = true")
        check(f"w{side}Weight", f"(∑ q : Fin nq, if bit w{side} q then 1 else 0) = target")
        check(f"w{side}Pair", f"∃ j : Fin 2, parity ({opposite}Base.get j) w{side} = true")
    for i in range(2):
        check(f"threshold{i}", f"(target - 1) * cap{i} < ({'z'}Family{i}.map Prod.snd).sum")
    lines += [f"end {namespace}", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("slug")
    parser.add_argument("namespace")
    parser.add_argument("output", type=Path)
    parser.add_argument("--checks", type=Path)
    args = parser.parse_args()
    text, data = generate(args.slug, args.namespace)
    args.output.write_text(text)
    if args.checks:
        module = ".".join(args.output.with_suffix("").parts[1:])
        args.checks.write_text(generate_checks(module, args.namespace))
    print(args.slug, "target", data["target"], "class ratios", data["values"], "caps", data["caps"])


if __name__ == "__main__":
    main()
