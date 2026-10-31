"""Independently check the finite packing output using sparse sets and counters.

This numerical validator supplies no theorem. Run it in a bounded allocation.
It does not use the generator's integer-mask or row-combination implementation.
"""

import argparse
import gzip
import json
from collections import Counter
from pathlib import Path

from emit_removal566 import HASHES, REVISION, read_code


def validate(codes, coordinates, record):
    result = {}
    for entry in record["families"]:
        n, side, index = entry["n"], entry["side"], entry["coordinate"]
        if n not in codes or side not in ("X", "Z") or not 0 <= index < 18:
            raise ValueError("Invalid coordinate label")
        code = codes[n]
        opposite = "Z" if side == "X" else "X"
        base = set(coordinates[str(n)][side][index])
        rows = [set(r) for r in code["checks"][side]]
        checks = [set(r) for r in code["checks"][opposite]]
        detectors = [set(r) for r in coordinates[str(n)][opposite]]
        loads = Counter()
        total = 0
        family = entry["family"]
        if not family:
            raise ValueError("Empty representative family")
        for representative in family:
            sparse = representative["support"]
            v = set(sparse)
            if len(v) != len(sparse) or any(type(q) is not int or not 0 <= q < n for q in v):
                raise ValueError("Malformed physical support")
            indices = representative["rows"]
            if len(set(indices)) != len(indices):
                raise ValueError("Duplicate row index")
            rebuilt = base.copy()
            for i in indices:
                if type(i) is not int or not 0 <= i < len(rows):
                    raise ValueError("Invalid row index")
                rebuilt.symmetric_difference_update(rows[i])
            if rebuilt != v:
                raise ValueError("Incorrect row-combination witness")
            if any(len(v & check) % 2 for check in checks):
                raise ValueError("Nonzero syndrome")
            if any(len(v & d) % 2 != len(base & d) % 2 for d in detectors):
                raise ValueError("Wrong logical coordinates")
            weight = representative["weight"]
            if type(weight) is not int or weight <= 0:
                raise ValueError("Invalid natural weight")
            total += weight
            loads.update({q: weight for q in v})
        cap = max(loads.values(), default=0)
        if cap == 0:
            raise ValueError("Zero-capacity logical family")
        arithmetic = {"totalWeight": total, "cap": cap, "bound": (total + cap - 1) // cap}
        if arithmetic != entry["arithmetic"]:
            raise ValueError("Incorrect packing arithmetic")
        label = f"{n}-{side}"
        if index in result.setdefault(label, {}):
            raise ValueError("Repeated coordinate family")
        result[label][index] = arithmetic
    return {
        label: {
            "coordinates_checked": sorted(values),
            "complete_basis": len(values) == 18,
            "minimum_family_bound": min(v["bound"] for v in values.values()),
            "families_above_twenty_threshold": sum(
                19 * v["cap"] < v["totalWeight"] for v in values.values()
            ),
        }
        for label, values in result.items()
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--coordinates", type=Path, required=True)
    parser.add_argument("--packing", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    codes = {n: read_code(args.upstream / f"codes/{n}-18-20.json", n) for n in (566, 578)}
    coordinate_record = json.loads(args.coordinates.read_text())
    opener = gzip.open if args.packing.suffix == ".gz" else open
    with opener(args.packing, "rt") as stream:
        record = json.load(stream)
    if coordinate_record["revision"] != REVISION or record["revision"] != REVISION:
        raise ValueError("Unexpected challenge revision")
    if coordinate_record["input_sha256"] != {str(n): h for n, h in HASHES.items()}:
        raise ValueError("Unexpected coordinate input hashes")
    result = {
        "validation": validate(codes, coordinate_record["coordinates"], record),
        "scope": "Independent exact arithmetic and class checks only; no kernel proof",
    }
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
