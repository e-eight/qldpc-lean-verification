"""Bounded disjoint-unit diagnostic on the frozen X32 sector pool.

No new representatives, LP calls, or complete X coverage are attempted. Greedy
failure says nothing about existence of a disjoint family or the code distance.
"""

import argparse
import copy
import gzip
import hashlib
import json
import random
import time
from pathlib import Path

from distance566_sector_verify import (
    BASELINE,
    INPUT_HASHES,
    check_case,
    load,
    source_inputs,
    validate_record,
)
from emit_removal566 import HASHES, REVISION

ROOT = Path(__file__).resolve().parents[1]
X_CERTIFICATE_SHA256 = "e5e8f386598416454e563307c55024cf6a7fff36ff1263daad5fbfd00489ccfd"
FROZEN = ROOT / "data/sector-packing-evaluation/2026-10-31/numerical"
WEIGHTED = ROOT / "data/distance566-packing/2026-10-30-weighted"
COORDINATES = ROOT / "data/distance566-evaluation/2026-10-30/coordinates.json"


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def certificate_bytes(record):
    return gzip.compress((json.dumps(record, sort_keys=True, indent=2) + "\n").encode(), mtime=0)


def check_provenance(record):
    if (
        record["baseline_commit"] != BASELINE
        or record["challenge_revision"] != REVISION
        or record["literal_sha256"] != HASHES[566]
        or record["input_sha256"] != INPUT_HASHES
        or record["bounded_side"] != "X"
        or record["detector_side"] != "Z"
        or record["good_rank"] != 7
        or record["residue_scope"] != {"mode": "pilot", "total_nonzero": 2047}
        or len(record["residues"]) != 32
        or len(record["pool"]) != 8306
    ):
        raise ValueError("Wrong frozen X32 input contract")


def greedy_disjoint(pool, case, restarts=8, deadline=None):
    """Shortest-first, then at most eight seeded within-length tie orders."""
    if type(restarts) is not int or not 0 <= restarts <= 8:
        raise ValueError("At most eight tie-order restarts are permitted")
    started = time.monotonic()
    pattern = case["suffix_pattern"]
    reference = sum(1 << q for q in case["reference_support"])
    eligible = []
    for i, entry in enumerate(pool):
        if (entry["quotient_class"] & pattern).bit_count() % 2:
            if (entry["mask"] & reference).bit_count() % 2 != 1:
                raise ValueError("Eligible detector has wrong physical pairing")
            eligible.append(i)
    sizes = {i: pool[i]["mask"].bit_count() for i in eligible}
    best, attempts = [], []
    for seed in [None, *range(restarts)]:
        if deadline is not None and time.monotonic() >= deadline:
            break
        order = eligible.copy()
        if seed is not None:
            random.Random(seed).shuffle(order)
        order.sort(key=sizes.__getitem__)
        occupied, selected = 0, []
        for index in order:
            if not (occupied & pool[index]["mask"]):
                selected.append(index)
                occupied |= pool[index]["mask"]
                if len(selected) == 7:
                    break
        attempts.append({"seed": seed, "selected_count": len(selected)})
        if len(selected) > len(best):
            best = selected
        if len(best) == 7:
            break
    return {
        "suffix_pattern": pattern,
        "eligible_count": len(eligible),
        "success": len(best) == 7,
        "selected_indices": best,
        "attempts": attempts,
        "wall_seconds": time.monotonic() - started,
    }


def unit_case(record, case, indices):
    """Separate set-based disjointness and pairing check before frozen validation."""
    if len(indices) != 7 or len(set(indices)) != 7:
        raise ValueError("Exactly seven different pool indices are required")
    reference = set(case["reference_support"])
    occupied, loads = set(), [0] * record["n"]
    for index in indices:
        if type(index) is not int or not 0 <= index < len(record["pool"]):
            raise ValueError("Invalid selected pool index")
        entry = record["pool"][index]
        vector = set(entry["support"])
        if not vector or any(type(q) is not int or not 0 <= q < record["n"] for q in vector):
            raise ValueError("Invalid physical support")
        if occupied & vector:
            raise ValueError("Selected detectors overlap physically")
        if (entry["quotient_class"] & case["suffix_pattern"]).bit_count() % 2 != 1:
            raise ValueError("Selected quotient does not pair one")
        if len(vector & reference) % 2 != 1:
            raise ValueError("Selected physical support does not pair one")
        occupied.update(vector)
        for q in vector:
            loads[q] += 1
    result = copy.deepcopy(case)
    result["weights"] = [[index, 1] for index in indices]
    result["arithmetic"] = {
        "loads": loads,
        "totalWeight": 7,
        "cap": 1,
        "bound": 7,
        "strict_seven": True,
    }
    result["restricted_dual"] = None
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, default=FROZEN / "x-v1/certificates.json.gz")
    parser.add_argument(
        "--focused", type=Path, default=WEIGHTED / "focused-v1/certificates.json.gz"
    )
    parser.add_argument(
        "--analysis", type=Path, default=WEIGHTED / "analysis-v1/lean-ready.json.gz"
    )
    parser.add_argument("--coordinates", type=Path, default=COORDINATES)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=90)
    parser.add_argument("--restarts", type=int, default=8)
    args = parser.parse_args()
    if not 0 < args.seconds <= 120 or not 0 <= args.restarts <= 8:
        raise ValueError("Diagnostic budgets exceed the authorized bounds")
    if args.out.exists():
        raise ValueError("Use a fresh diagnostic output directory")
    original = load(args.certificate, X_CERTIFICATE_SHA256)
    check_provenance(original)
    code, coordinates, sources, input_reports = source_inputs(
        args.upstream, args.focused, args.analysis, args.coordinates
    )
    original_report = validate_record(code, coordinates, original, sources["X"])
    if not original_report["all_requested_passed"]:
        raise ValueError("Original X32 numerical gate is not satisfied")
    args.out.mkdir(parents=True)
    write_json(args.out / "input-validation.json", input_reports)
    write_json(args.out / "original-validation.json", original_report)
    candidate = copy.deepcopy(original)
    candidate["parent_certificate_sha256"] = X_CERTIFICATE_SHA256
    candidate["parent_source_sha256"] = original["source_sha256"]
    candidate["source_sha256"] = {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [Path(__file__), ROOT / "tests/test_distance566_sector_disjoint.py"]
    }
    candidate["generation_scope"] = "Bounded greedy disjoint X32 diagnostic; LP fallback unchanged"
    started = time.monotonic()
    diagnostics = []
    selected_union = set()
    for i, case in enumerate(original["residues"]):
        result = greedy_disjoint(original["pool"], case, args.restarts, started + args.seconds)
        if result["success"]:
            replacement = unit_case(original, case, result["selected_indices"])
            check_case(code, coordinates, original, replacement, require_seven=True)
            candidate["residues"][i] = replacement
            selected_union.update(result["selected_indices"])
        result["retained_original_LP_weights"] = not result["success"]
        diagnostics.append(result)
        write_json(
            args.out / "progress.json", {"cases_finished": i + 1, "diagnostics": diagnostics}
        )
    search_seconds = time.monotonic() - started
    report = validate_record(code, coordinates, candidate, sources["X"])
    candidate_path = args.out / "candidate-v1.json.gz"
    candidate_path.write_bytes(certificate_bytes(candidate))
    report["certificate_sha256"] = hashlib.sha256(candidate_path.read_bytes()).hexdigest()
    write_json(args.out / "independent-validation.json", report)
    lengths = [len(original["pool"][i]["support"]) for i in sorted(selected_union)]
    chosen = [i for result in diagnostics if result["success"] for i in result["selected_indices"]]
    occurrences = [len(original["pool"][i]["support"]) for i in chosen]
    summary = {
        "schema": "qldpc-disjoint-x32-diagnostic-v1",
        "parent_certificate_sha256": X_CERTIFICATE_SHA256,
        "candidate_sha256": report["certificate_sha256"],
        "bounded_side": "X",
        "detector_side": "Z",
        "cases": 32,
        "total_nonzero_residues": 2047,
        "complete_residue_coverage": False,
        "seven_disjoint_successes": sum(r["success"] for r in diagnostics),
        "successful_patterns": [r["suffix_pattern"] for r in diagnostics if r["success"]],
        "failed_patterns": [r["suffix_pattern"] for r in diagnostics if not r["success"]],
        "search_wall_seconds": search_seconds,
        "soft_search_limit_seconds": args.seconds,
        "maximum_seeded_tie_restarts": args.restarts,
        "seeds": list(range(args.restarts)),
        "shortest_first_initial_attempt": True,
        "selected_pool_union": sorted(selected_union),
        "selected_pool_union_size": len(selected_union),
        "union_max_physical_weight": max(lengths, default=0),
        "union_average_physical_weight": sum(lengths) / len(lengths) if lengths else None,
        "occurrence_average_physical_weight": sum(occurrences) / len(occurrences)
        if occurrences
        else None,
        "all_requested_exact_thresholds_passed": report["all_requested_passed"],
        "diagnostics": diagnostics,
        "scope": "Numerical X32 diagnostic only; greedy failure is not infeasibility; no complete X or new Lean claim",
    }
    write_json(args.out / "summary.json", summary)
    print(
        json.dumps(
            {k: v for k, v in summary.items() if k not in ("diagnostics", "selected_pool_union")}
        )
    )


if __name__ == "__main__":
    main()
