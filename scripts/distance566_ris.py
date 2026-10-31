"""Bounded random-information-set pilot, without physical symmetry assumptions.

Search both literal endpoints for low-weight logical classes spanning all
eighteen coordinates. These are numerical upper witnesses, not lower bounds.
"""

import argparse
import json
import random
import time
from pathlib import Path

import numpy as np
from distance566 import coordinates, dot, echelon, pack, reduce_vector, support
from emit_removal566 import HASHES, REVISION, read_code


def systematic_kernel(matrix):
    """Independent NumPy RREF in the supplied physical column order."""
    matrix = matrix.copy()
    m, n = matrix.shape
    pivots = []
    r = 0
    for q in range(n):
        candidates = np.flatnonzero(matrix[r:, q])
        if not len(candidates):
            continue
        j = r + int(candidates[0])
        matrix[[r, j]] = matrix[[j, r]]
        selected = matrix[:, q].astype(bool)
        selected[r] = False
        matrix[selected] ^= matrix[r]
        pivots.append(q)
        r += 1
        if r == m:
            break
    pivot_set = set(pivots)
    for q in range(n):
        if q not in pivot_set:
            yield [q, *(pivots[i] for i in np.flatnonzero(matrix[:r, q]))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--trials", type=int, default=64)
    parser.add_argument("--seconds", type=int, default=90)
    parser.add_argument("--seed", type=int, default=56621)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    tasks = {}
    for n in (566, 578):
        code = read_code(args.upstream / f"codes/{n}-18-20.json", n)
        record = coordinates(code)
        for side, opposite in (("X", "Z"), ("Z", "X")):
            matrix = np.zeros((len(code["checks"][opposite]), n), dtype=np.uint8)
            for i, row in enumerate(code["checks"][opposite]):
                matrix[i, row] = 1
            tasks[f"{n}-{side}"] = {
                "n": n,
                "side": side,
                "matrix": matrix,
                "rows": [pack(r) for r in code["checks"][opposite]],
                "detectors": [pack(r) for r in record[opposite]],
                "best": {},
                "trials": 0,
            }
    start = time.monotonic()
    for _ in range(args.trials):
        for task in tasks.values():
            if time.monotonic() >= start + args.seconds:
                break
            order = list(range(task["n"]))
            rng.shuffle(order)
            for indices in systematic_kernel(task["matrix"][:, order]):
                v = pack(int(order[q]) for q in indices)
                logical_class = pack(i for i, d in enumerate(task["detectors"]) if dot(v, d))
                if not logical_class:
                    continue
                if any(dot(v, row) for row in task["rows"]):
                    raise ValueError("Information-set candidate has nonzero syndrome")
                previous = task["best"].get(logical_class)
                if previous is None or v.bit_count() < previous.bit_count():
                    task["best"][logical_class] = v
                if v.bit_count() < 20:
                    args.out.with_suffix(".candidate.json").write_text(
                        json.dumps(
                            {
                                "n": task["n"],
                                "side": task["side"],
                                "support": support(v),
                                "class": logical_class,
                            },
                            indent=2,
                        )
                        + "\n"
                    )
                    raise ValueError("Potential refutation found; independently check candidate")
            task["trials"] += 1
    result = {
        "revision": REVISION,
        "input_sha256": HASHES,
        "seed": args.seed,
        "elapsed_seconds": time.monotonic() - start,
        "results": {},
    }
    for name, task in tasks.items():
        basis = {}
        selected = []
        for c, v in sorted(task["best"].items(), key=lambda cv: (cv[1].bit_count(), cv[0])):
            r = reduce_vector(c, basis)
            if r:
                basis[r.bit_length() - 1] = r
                selected.append({"class": c, "support": support(v), "weight": v.bit_count()})
        result["results"][name] = {
            "trials": task["trials"],
            "classes_found": len(task["best"]),
            "class_span_rank": len(echelon(task["best"])),
            "selected_class_basis": selected,
            "minimum_sampled_weight": min(
                (v.bit_count() for v in task["best"].values()), default=None
            ),
        }
    result["scope"] = (
        "Numerical upper witnesses and detector candidates only; no lower distance bound"
    )
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                name: {k: v for k, v in r.items() if k != "selected_class_basis"}
                for name, r in result["results"].items()
            }
        )
    )


if __name__ == "__main__":
    main()
