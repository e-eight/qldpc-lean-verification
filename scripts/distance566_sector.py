"""Bounded numerical packing across detector classes for logical sectors.

The Z pilot covers seven residuals; the X pilot is capped at 32 of 2047.
Floating-point optimization only proposes natural weights. Exact sparse
validation decides whether the exported finite certificate meets the threshold.
"""

import argparse
import copy
import gzip
import hashlib
import json
import math
import time
import warnings
from fractions import Fraction
from pathlib import Path

from distance566_sector_verify import BASELINE, INPUT_HASHES, SCHEMA, source_inputs
from emit_removal566 import HASHES, REVISION

ROOT = Path(__file__).resolve().parents[1]
WEIGHTED = ROOT / "data/distance566-packing/2026-10-30-weighted"
COORDINATES = ROOT / "data/distance566-evaluation/2026-10-30/coordinates.json"


def mask(values):
    return sum(1 << i for i in values)


def support(value):
    return [i for i in range(value.bit_length()) if value >> i & 1]


def dot(a, b):
    return (a & b).bit_count() % 2


def xor_values(values):
    value = 0
    for item in values:
        value ^= item
    return value


def rank(values):
    pivots = {}
    for value in values:
        while value:
            p = value.bit_length() - 1
            if p not in pivots:
                pivots[p] = value
                break
            value ^= pivots[p]
    return len(pivots)


def exact_arithmetic(vectors, weights, n):
    loads = [0] * n
    if len(vectors) != len(weights):
        raise ValueError("Weight vector dimension mismatch")
    for vector, weight in zip(vectors, weights, strict=True):
        if type(weight) is not int or weight < 0:
            raise ValueError("Invalid natural proposal weight")
        for q in support(vector):
            loads[q] += weight
    total, cap = sum(weights), max(loads, default=0)
    if total <= 0 or cap <= 0:
        raise ValueError("Empty proposal")
    return {
        "loads": loads,
        "totalWeight": total,
        "cap": cap,
        "bound": (total + cap - 1) // cap,
        "strict_seven": 6 * cap < total,
    }


def gzip_bytes(record):
    return gzip.compress((json.dumps(record, sort_keys=True, indent=2) + "\n").encode(), mtime=0)


def representative(rep, index):
    return {
        "support": rep["support"],
        "mask": mask(rep["support"]),
        "rows": rep["rows"],
        "row_mask": mask(rep["rows"]),
        "weight": rep["weight"],
        "source_rep_index": index,
    }


def build_problem(code, coordinates, source, bounded_side, limit=None):
    side = "X" if bounded_side == "Z" else "Z"
    if source["detector_side"] != side or source["bounded_side"] != bounded_side:
        raise ValueError("Source orientation mismatch")
    basis = copy.deepcopy(source["coverage"])
    classes = basis["classes"]
    good = [
        f for f in source["families"] if 6 * f["arithmetic"]["cap"] < f["arithmetic"]["totalWeight"]
    ]
    g = rank([f["class"] for f in good])
    if g != (15 if bounded_side == "Z" else 7):
        raise ValueError("Unexpected saved good-class rank")
    good_classes = {f["class"] for f in good}
    if any(c not in good_classes for c in classes[:g]) or any(
        c in good_classes for c in classes[g:]
    ):
        raise ValueError("Saved strongest-first basis does not split at good rank")
    paired = [mask(w["support"]) for w in basis["paired_witnesses"]]
    opposite_old = [mask(v) for v in coordinates[bounded_side]]
    own_old = [mask(v) for v in coordinates[side]]
    rows = {s: [mask(row) for row in code["checks"][s]] for s in ("X", "Z")}
    problem = {
        "schema": SCHEMA,
        "baseline_commit": BASELINE,
        "challenge_revision": REVISION,
        "literal_sha256": HASHES[566],
        "input_sha256": INPUT_HASHES,
        "n": code["n"],
        "logical_dimension": 18,
        "target_bound": 7,
        "detector_side": side,
        "bounded_side": bounded_side,
        "good_rank": g,
        "matrix_ranks": {s: rank(rs) for s, rs in rows.items()},
        "selected_basis": basis,
        "families": [],
        "source_family_count": len(source["families"]),
        "good_families": [],
        "pool": [],
        "annihilator": {
            "dimension": 18 - g,
            "canonical_basis": [
                mask(i for i, w in enumerate(own_old) if dot(v, w)) for v in paired[g:]
            ],
            "selected_pairing_basis": [1 << i for i in range(g, 18)],
        },
        "scope": "Numerical finite sector certificates only; kernel bound remains 6 <= d <= 20",
    }
    seen = {}
    sources = {f["class"]: f for f in source["families"]}
    for i, family in enumerate(source["families"]):
        base = mask(family["base_support"])
        coefficient = mask(j for j, w in enumerate(paired) if dot(base, w))
        quotient = coefficient >> g
        problem["families"].append(
            {
                "class": family["class"],
                "base_support": family["base_support"],
                "base_mask": base,
                "selected_class_coordinates": coefficient,
                "quotient_class": quotient,
                "source_family_index": i,
            }
        )
        if not quotient:
            continue
        for j, rep in enumerate(family["representatives"]):
            value = mask(rep["support"])
            if value not in seen:
                seen[value] = len(problem["pool"])
                problem["pool"].append(
                    {
                        "support": rep["support"],
                        "mask": value,
                        "class": family["class"],
                        "selected_class_coordinates": coefficient,
                        "quotient_class": quotient,
                        "provenances": [],
                    }
                )
            problem["pool"][seen[value]]["provenances"].append(
                {
                    "family_class": family["class"],
                    "source_rep_index": j,
                    "rows": rep["rows"],
                    "row_mask": mask(rep["rows"]),
                }
            )
    for i, c in enumerate(classes[:g]):
        family = sources[c]
        reps = [
            representative(r, j) for j, r in enumerate(family["representatives"]) if r["weight"]
        ]
        problem["good_families"].append(
            {
                "class": c,
                "selected_index": i,
                "representatives": reps,
                "arithmetic": exact_arithmetic(
                    [r["mask"] for r in reps], [r["weight"] for r in reps], code["n"]
                ),
            }
        )
    d = 18 - g
    if bounded_side == "Z":
        if limit not in (None, 7):
            raise ValueError("Z pilot must cover all seven residues")
        patterns = list(range(1, 8))
        mode = "complete"
    else:
        limit = 32 if limit is None else limit
        if not 0 < limit <= 32:
            raise ValueError("Full X exploration is not authorized; limit is 32")
        patterns = sorted(range(1, 2**d), key=lambda p: (p.bit_count(), p))[:limit]
        mode = "pilot"
    problem["residue_scope"] = {"mode": mode, "total_nonzero": 2**d - 1}
    problem["residues"] = []
    for p in patterns:
        reference = xor_values(paired[g + i] for i in support(p))
        canonical = mask(i for i, w in enumerate(own_old) if dot(reference, w))
        if mask(i for i, c in enumerate(classes) if dot(c, canonical)) != p << g:
            raise ValueError("Canonical/selected reference transform failed")
        problem["residues"].append(
            {
                "suffix_pattern": p,
                "canonical_class": canonical,
                "selected_pairing_coordinates": p << g,
                "reference_support": support(reference),
            }
        )
    # Sanity check the original selected detector classes separately from logical coordinates.
    if any(
        mask(j for j, w in enumerate(opposite_old) if dot(mask(v), w)) != c
        for v, c in zip(basis["detectors"], classes, strict=True)
    ):
        raise ValueError("Canonical detector coordinates changed")
    return problem


def choose_weights(vectors, n, proposals, lp_seconds=0):
    """Compare cheap proposals and rounded LP proposals by exact W/cap."""
    candidates = [(name, values) for name, values in proposals if sum(values) > 0]
    status = {"ran": False, "time_limit_seconds": lp_seconds}
    dual = None
    if lp_seconds > 0:
        import numpy as np
        from scipy.optimize import OptimizeWarning, linprog
        from scipy.sparse import csc_matrix

        starts = [0]
        positions = []
        for value in vectors:
            positions.extend(support(value))
            starts.append(len(positions))
        matrix = csc_matrix((np.ones(len(positions)), positions, starts), shape=(n, len(vectors)))
        started = time.monotonic()
        with warnings.catch_warnings():
            warnings.filterwarnings(
                "ignore", message="Unrecognized options detected.*", category=OptimizeWarning
            )
            result = linprog(
                -np.ones(len(vectors)),
                A_ub=matrix,
                b_ub=np.ones(n),
                bounds=(0, None),
                method="highs",
                options={"threads": 1, "parallel": False, "time_limit": lp_seconds},
            )
        status = {
            "ran": True,
            "status": int(result.status),
            "success": bool(result.success),
            "time_limit_seconds": lp_seconds,
            "elapsed_seconds": time.monotonic() - started,
            "columns": len(vectors),
            "rows": n,
        }
        if result.x is not None and np.isfinite(result.x).all():
            for scale in (1000, 1_000_000):
                values = [max(0, int(round(float(x) * scale))) for x in result.x]
                divisor = math.gcd(*values)
                if divisor:
                    candidates.append((f"LP rounded at {scale}", [v // divisor for v in values]))
        prices = np.ones(n)
        if result.success and result.ineqlin.marginals is not None:
            prices = np.maximum(0, -result.ineqlin.marginals)
        denominator = 1_000_000
        prices = [max(0, math.ceil(float(p) * denominator)) for p in prices]
        for vector in vectors:
            qs = support(vector)
            deficit = denominator - sum(prices[q] for q in qs)
            if deficit > 0:
                prices[qs[0]] += deficit
        dual = {
            "qubit_weights": prices,
            "denominator": denominator,
            "upper_numerator": sum(prices),
            "scope": "Only this residue's eligible stored physical pool; no global pricing claim",
        }
    evaluated = [
        (name, values, exact_arithmetic(vectors, values, n)) for name, values in candidates
    ]
    name, weights, arithmetic = max(
        evaluated, key=lambda item: Fraction(item[2]["totalWeight"], item[2]["cap"])
    )
    return (
        weights,
        arithmetic,
        dual,
        {
            "solver": status,
            "chosen_proposal": name,
            "proposals": [
                {"name": name, "ratio": str(Fraction(a["totalWeight"], a["cap"]))}
                for name, _, a in evaluated
            ],
        },
    )


def pack_residue(problem, case, source, lp_seconds):
    pattern = case["suffix_pattern"]
    indices = [i for i, r in enumerate(problem["pool"]) if dot(r["quotient_class"], pattern)]
    vectors = [problem["pool"][i]["mask"] for i in indices]
    reference = mask(case["reference_support"])
    if any(dot(vector, reference) != 1 for vector in vectors):
        raise ValueError("Compatible class has wrong direct physical pairing")
    sources = {f["class"]: f for f in source["families"]}
    inherited = []
    for i in indices:
        entry = problem["pool"][i]
        weight = 0
        for provenance in entry["provenances"]:
            family = sources[provenance["family_class"]]
            weight += (
                family["representatives"][provenance["source_rep_index"]]["weight"]
                * 1_000_000
                // family["arithmetic"]["cap"]
            )
        inherited.append(weight)
    proposals = [
        ("uniform eligible pool", [1] * len(indices)),
        ("inherited normalized class weights", inherited),
        ("inverse physical weight", [max(1, 10000 // v.bit_count()) for v in vectors]),
    ]
    weights, arithmetic, dual, details = choose_weights(
        vectors, problem["n"], proposals, lp_seconds
    )
    result = case | {
        "eligible_count": len(indices),
        "weights": [[i, w] for i, w in zip(indices, weights, strict=True) if w],
        "arithmetic": arithmetic,
        "restricted_dual": dual,
    }
    return result, details


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument(
        "--focused", type=Path, default=WEIGHTED / "focused-v1/certificates.json.gz"
    )
    parser.add_argument(
        "--analysis", type=Path, default=WEIGHTED / "analysis-v1/lean-ready.json.gz"
    )
    parser.add_argument("--coordinates", type=Path, default=COORDINATES)
    parser.add_argument("--bounded-side", choices=("X", "Z"), default="Z")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=float, default=180)
    parser.add_argument("--lp-seconds", type=float, default=4)
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError("Use a fresh output directory")
    if args.seconds <= 0 or not 0 <= args.lp_seconds <= 10:
        raise ValueError("Invalid bounded search budget")
    args.out.mkdir(parents=True)
    began = time.monotonic()
    code, coordinates, sources, reports = source_inputs(
        args.upstream, args.focused, args.analysis, args.coordinates
    )
    (args.out / "input-validation.json").write_text(json.dumps(reports, indent=2) + "\n")
    problem = build_problem(
        code, coordinates, sources[args.bounded_side], args.bounded_side, args.limit
    )
    problem["source_sha256"] = {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [
            Path(__file__),
            ROOT / "scripts/distance566_sector_verify.py",
            ROOT / "tests/test_distance566_sector.py",
        ]
    }
    setup_seconds = time.monotonic() - began
    started = time.monotonic()
    details = []
    for i, case in enumerate(problem["residues"]):
        remaining = max(0, args.seconds - (time.monotonic() - started))
        seconds = min(args.lp_seconds, remaining)
        if seconds < 0.05:
            seconds = 0
        packed, detail = pack_residue(problem, case, sources[args.bounded_side], seconds)
        problem["residues"][i] = packed
        details.append({"suffix_pattern": case["suffix_pattern"], **detail})
        (args.out / "progress.json").write_text(
            json.dumps(
                {
                    "bounded_side": args.bounded_side,
                    "cases_finished": i + 1,
                    "strict_passes": sum(
                        r.get("arithmetic", {}).get("strict_seven", False)
                        for r in problem["residues"]
                    ),
                    "last_bound": packed["arithmetic"]["bound"],
                },
                indent=2,
            )
            + "\n"
        )
    problem["all_requested_passed"] = all(
        r["arithmetic"]["strict_seven"] for r in problem["residues"]
    )
    certificate = args.out / "certificates.json.gz"
    certificate.write_bytes(gzip_bytes(problem))
    summary = {
        "bounded_side": args.bounded_side,
        "detector_side": problem["detector_side"],
        "good_rank": problem["good_rank"],
        "annihilator_dimension": problem["annihilator"]["dimension"],
        "cases": len(problem["residues"]),
        "total_nonzero_residues": problem["residue_scope"]["total_nonzero"],
        "pool_supports": len(problem["pool"]),
        "source_classes": problem["source_family_count"],
        "all_requested_passed": problem["all_requested_passed"],
        "setup_seconds": setup_seconds,
        "packing_wall_seconds": time.monotonic() - started,
        "soft_budget_seconds": args.seconds,
        "LP_seconds_per_case": args.lp_seconds,
        "seed": None,
        "random_search": False,
        "certificate_sha256": hashlib.sha256(certificate.read_bytes()).hexdigest(),
        "results": [
            {k: r[k] for k in ("suffix_pattern", "canonical_class", "selected_pairing_coordinates")}
            | {k: r["arithmetic"][k] for k in ("totalWeight", "cap", "bound", "strict_seven")}
            for r in problem["residues"]
        ],
        "details": details,
        "scope": "Finite numerical certificates only; full X exploration and new Lean claims excluded",
    }
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k not in ("details", "results")}))


if __name__ == "__main__":
    main()
