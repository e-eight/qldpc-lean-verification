"""Independent exact sparse validation of weighted 566/578 packing certificates.

No NumPy, LP solver, search arithmetic, or search rank routine is imported.
This verifies finite mathematical certificates and does not supply a Lean proof.
"""

import argparse
import gzip
import hashlib
import json
from pathlib import Path

EXPECTED = {
    566: "061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be",
    578: "440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514",
}


def natural(value, name, positive=False):
    if type(value) is not int or value < (1 if positive else 0):
        raise ValueError(f"Invalid natural {name}")
    return value


def sparse(values, size):
    if len(set(values)) != len(values):
        raise ValueError("Duplicate index")
    if any(type(q) is not int or not 0 <= q < size for q in values):
        raise ValueError("Index out of range")
    return set(values)


def rank_sets(rows):
    pivots = {}
    for source in rows:
        v = set(source)
        while v:
            p = max(v)
            if p not in pivots:
                pivots[p] = v
                break
            v.symmetric_difference_update(pivots[p])
    return len(pivots)


def label_support(label, k=18):
    natural(label, "class", positive=True)
    if label >= 2**k:
        raise ValueError("Logical class index out of range")
    return {i for i in range(k) if label // 2**i % 2}


def class_of(vector, opposite_basis):
    return sum(2**i for i, d in enumerate(opposite_basis) if len(vector & d) % 2)


def check_cycle(vector, checks):
    if any(len(vector & row) % 2 for row in checks):
        raise ValueError("Nonzero syndrome")


def verify_witness(code, coordinates, record):
    side = record["detector_side"]
    if side not in ("X", "Z") or record["n"] != code["n"]:
        raise ValueError("Wrong witness sector")
    opposite = "Z" if side == "X" else "X"
    vector = sparse(record["support"], code["n"])
    checks = [sparse(row, code["n"]) for row in code["checks"][opposite]]
    basis = [sparse(row, code["n"]) for row in coordinates[opposite]]
    own_rows = [sparse(row, code["n"]) for row in code["checks"][side]]
    for detector in basis:
        check_cycle(detector, own_rows)
    check_cycle(vector, checks)
    label = class_of(vector, basis)
    if label == 0 or label != record["class"]:
        raise ValueError("Wrong or trivial witness class")
    return {
        "weight": len(vector),
        "class": label,
        "scope": "Upper witness only; no lower bound or refutation of d<=20",
    }


def validate_problem(code, coordinates, record):
    n, side = code["n"], record["detector_side"]
    if side not in ("X", "Z") or record["n"] != n:
        raise ValueError("Wrong detector sector")
    opposite = "Z" if side == "X" else "X"
    if record["bounded_side"] != opposite:
        raise ValueError("Detector and bounded sectors are swapped")
    rows = {s: [sparse(r, n) for r in code["checks"][s]] for s in ("X", "Z")}
    if any(len(x & z) % 2 for x in rows["X"] for z in rows["Z"]):
        raise ValueError("Noncommuting CSS matrices")
    old = {s: [sparse(v, n) for v in coordinates[s]] for s in ("X", "Z")}
    if len(old["X"]) != 18 or len(old["Z"]) != 18:
        raise ValueError("Wrong baseline dimension")
    if any(
        len(x & z) % 2 != (i == j) for i, x in enumerate(old["X"]) for j, z in enumerate(old["Z"])
    ):
        raise ValueError("Baseline bases are not paired")
    ranks = {s: rank_sets(rs) for s, rs in rows.items()}
    if n - sum(ranks.values()) != 18:
        raise ValueError("Wrong dimension bound")
    for s in ("X", "Z"):
        for vector in old[s]:
            check_cycle(vector, rows["Z" if s == "X" else "X"])
    families = {}
    for family in record["families"]:
        if (
            family["n"] != n
            or family["detector_side"] != side
            or family["bounded_side"] != opposite
        ):
            raise ValueError("Family sector mismatch")
        label = family["class"]
        label_support(label)
        if label in families:
            raise ValueError("Duplicate logical class")
        base = sparse(family["base_support"], n)
        check_cycle(base, rows[opposite])
        if class_of(base, old[opposite]) != label:
            raise ValueError("Incorrect base logical coordinates")
        loads = [0] * n
        total = 0
        representatives = family["representatives"]
        if not representatives:
            raise ValueError("Empty family")
        for representative in representatives:
            vector = sparse(representative["support"], n)
            indices = sparse(representative["rows"], len(rows[side]))
            rebuilt = base.copy()
            for i in indices:
                rebuilt.symmetric_difference_update(rows[side][i])
            if rebuilt != vector:
                raise ValueError("Incorrect stabilizer row-combination witness")
            check_cycle(vector, rows[opposite])
            if class_of(vector, old[opposite]) != label:
                raise ValueError("Representative class changed")
            weight = natural(representative["weight"], "weight")
            total += weight
            for q in vector:
                loads[q] += weight
        cap = max(loads)
        if total <= 0 or cap <= 0:
            raise ValueError("Empty positive weighted family")
        arithmetic = {"totalWeight": total, "cap": cap, "bound": (total + cap - 1) // cap}
        for value in family["arithmetic"].values():
            natural(value, "packing arithmetic", positive=True)
        if family["arithmetic"] != arithmetic:
            raise ValueError("Incorrect exact integer threshold or capacity")
        dual = family["restricted_dual"]
        denominator = natural(dual["denominator"], "dual denominator", positive=True)
        prices = [natural(w, "dual price") for w in dual["qubit_weights"]]
        if len(prices) != n or sum(prices) != natural(dual["upper_numerator"], "dual numerator"):
            raise ValueError("Incorrect restricted dual dimensions")
        if any(
            sum(prices[q] for q in sparse(r["support"], n)) < denominator for r in representatives
        ):
            raise ValueError("Infeasible restricted-list dual")
        if total * denominator > cap * sum(prices):
            raise ValueError("Restricted-list weak duality violated")
        families[label] = family
    curve = []
    for d in range(1, max([20, *(f["arithmetic"]["bound"] for f in families.values())]) + 1):
        eligible = [
            f
            for f in families.values()
            if (d - 1) * f["arithmetic"]["cap"] < f["arithmetic"]["totalWeight"]
        ]
        curve.append(
            {
                "bound": d,
                "rank": rank_sets([label_support(f["class"]) for f in eligible]),
                "eligible_classes": len(eligible),
            }
        )
    if record["rank_vs_bound"] != curve:
        raise ValueError("Incorrect rank-versus-bound curve")
    coverage = record["coverage"]
    if coverage["detector_side"] != side or coverage["bounded_side"] != opposite:
        raise ValueError("Incorrect coverage sector")
    classes = coverage["classes"]
    if (
        len(classes) != 18
        or len(set(classes)) != 18
        or rank_sets([label_support(c) for c in classes]) != 18
    ):
        raise ValueError("Incomplete or dependent detector coverage")
    detectors = [sparse(v, n) for v in coverage["detectors"]]
    if len(detectors) != 18 or any(
        detector != set(families[c]["base_support"])
        for detector, c in zip(detectors, classes, strict=True)
    ):
        raise ValueError("Coverage detector mismatch")
    witnesses = []
    for entry in coverage["paired_witnesses"]:
        vector = sparse(entry["support"], n)
        rebuilt = set()
        for i in sparse(entry["old_basis_rows"], 18):
            rebuilt.symmetric_difference_update(old[opposite][i])
        if rebuilt != vector:
            raise ValueError("Wrong paired-witness basis change")
        check_cycle(vector, rows[side])
        witnesses.append(vector)
    if len(witnesses) != 18 or any(
        len(w & d) % 2 != (i == j) for i, w in enumerate(witnesses) for j, d in enumerate(detectors)
    ):
        raise ValueError("Paired coverage matrix is not identity")
    bound = natural(coverage["bound"], "coverage bound", positive=True)
    best = max((r["bound"] for r in curve if r["rank"] == 18), default=0)
    if bound != best or any(
        (bound - 1) * families[c]["arithmetic"]["cap"] >= families[c]["arithmetic"]["totalWeight"]
        for c in classes
    ):
        raise ValueError("Incorrect complete-basis bound")
    return {
        "n": n,
        "detector_side": side,
        "bounded_side": opposite,
        "exact_finite_complete_bound": bound,
        "rank_vs_bound": curve,
        "families_checked": len(families),
        "representatives_checked": sum(len(f["representatives"]) for f in families.values()),
        "detector_weights": [len(d) for d in detectors],
        "paired_witness_weights": [len(w) for w in witnesses],
        "coverage_pairing": "identity",
        "matrix_ranks": ranks,
        "scope": "Independent exact finite validation only; not a Lean proof",
    }


def verify_diagnostic(code, coordinates, family, record):
    side = family["detector_side"]
    opposite = family["bounded_side"]
    vector = sparse(record["support"], code["n"])
    base = sparse(family["base_support"], code["n"])
    prices = family["restricted_dual"]["qubit_weights"]
    if record["kind"] == "zero_price_representative":
        rows = [sparse(r, code["n"]) for r in code["checks"][side]]
        rebuilt = base.copy()
        for i in sparse(record["rows"], len(rows)):
            rebuilt.symmetric_difference_update(rows[i])
        if rebuilt != vector or sum(prices[q] for q in vector) != 0:
            raise ValueError("Incorrect zero-price row-combination diagnostic")
        check_cycle(vector, [sparse(r, code["n"]) for r in code["checks"][opposite]])
        if (
            class_of(vector, [sparse(r, code["n"]) for r in coordinates[opposite]])
            != family["class"]
        ):
            raise ValueError("Zero-price representative changed class")
    elif record["kind"] == "opposite_cycle_obstruction":
        if record["detector_side"] != opposite or len(vector & base) % 2 != 1:
            raise ValueError("Incorrect erasure obstruction pairing")
        if any(prices[q] == 0 for q in vector):
            raise ValueError("Erasure obstruction leaves the priced support")
        verify_witness(code, coordinates, record)
    else:
        raise ValueError("Unknown pricing diagnostic")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--coordinates", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    with gzip.open(args.certificate, "rt") as stream:
        record = json.load(stream)
    if (
        record["baseline_commit"] != "4461ec5e8d711cbb1cf29da5d35d0aebe987f038"
        or record["challenge_revision"] != "8c87413d16b78cdd934b7b7a8592cddc81ae6eed"
    ):
        raise ValueError("Wrong baseline or challenge revision")
    if record["input_sha256"] != {str(n): h for n, h in EXPECTED.items()}:
        raise ValueError("Wrong certificate input hashes")
    coordinates = json.loads(args.coordinates.read_text())["coordinates"]
    codes = {}
    for n, digest in EXPECTED.items():
        raw = (args.upstream / f"codes/{n}-18-20.json").read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("Wrong literal input hash")
        codes[n] = json.loads(raw)
    results = [
        validate_problem(codes[r["n"]], coordinates[str(r["n"])], r) for r in record["results"]
    ]
    witnesses = []
    for path in sorted((args.certificate.parent / "lighter-witnesses").glob("*.json")):
        entry = json.loads(path.read_text())
        witnesses.append(verify_witness(codes[entry["n"]], coordinates[str(entry["n"])], entry))
    output = {
        "status": "passed",
        "certificate_sha256": hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
        "coordinate_record_sha256": hashlib.sha256(args.coordinates.read_bytes()).hexdigest(),
        "results": results,
        "lighter_witnesses": witnesses,
        "scope": "Exact mathematical certificate validation; no new kernel result",
    }
    args.out.write_text(json.dumps(output, indent=2) + "\n")
    print(
        json.dumps(
            {
                "status": "passed",
                "bounds": [
                    {
                        k: r[k]
                        for k in (
                            "n",
                            "detector_side",
                            "bounded_side",
                            "exact_finite_complete_bound",
                        )
                    }
                    for r in results
                ],
                "lighter_witnesses": len(witnesses),
            }
        )
    )


if __name__ == "__main__":
    main()
