"""Finite packing report, positive-weight exports, and exact pricing diagnostics.

All numerical analysis runs in a bounded allocation. Diagnostics concern the
stored price vector and class, not a proof of global pricing optimality.
"""

import argparse
import copy
import gzip
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from distance566 import combination, dot, kernel, pack, support
from distance566_weighted import load_json, rank_curve, row_solver, solve_rows
from distance566_weighted_verify import verify_diagnostic, verify_witness
from emit_removal566 import read_code


def positive_problem(record):
    result = copy.deepcopy(record)
    families = {f["class"]: f for f in result["families"]}
    result["families"] = [families[c] for c in result["coverage"]["classes"]]
    for family in result["families"]:
        family["representatives"] = [r for r in family["representatives"] if r["weight"] > 0]
        family["restricted_dual"]["scope"] = "Only the selected positive-weight representative list"
    result["rank_vs_bound"] = rank_curve(result["families"])
    result["classes_evaluated"] = 18
    result.pop("progress", None)
    result["artifact_role"] = "Lean-ready finite input; no new Lean proof"
    return result


def pricing_diagnostic(code, coordinates, family, witness_directory=None):
    side = family["detector_side"]
    opposite = family["bounded_side"]
    rows = [pack(r) for r in code["checks"][side]]
    base = pack(family["base_support"])
    qs = [q for q, w in enumerate(family["restricted_dual"]["qubit_weights"]) if w]
    qmask = pack(qs)
    try:
        coefficient = solve_rows(base & qmask, row_solver([r & qmask for r in rows]))
    except ValueError:
        compressed = [pack(i for i, q in enumerate(qs) if (r >> q) & 1) for r in rows]
        compressed_base = pack(i for i, q in enumerate(qs) if (base >> q) & 1)
        dual_vector = next(v for v in kernel(compressed, len(qs)) if dot(v, compressed_base))
        vector = pack(qs[i] for i in support(dual_vector))
        label = pack(i for i, w in enumerate(coordinates[side]) if dot(vector, pack(w)))
        result = {
            "kind": "opposite_cycle_obstruction",
            "n": code["n"],
            "detector_side": opposite,
            "family_detector_side": side,
            "family_class": family["class"],
            "class": label,
            "support": support(vector),
            "scope": "Excludes cost zero for these prices only; does not exclude other improving columns",
        }
    else:
        vector = base ^ combination(rows, coefficient)
        result = {
            "kind": "zero_price_representative",
            "n": code["n"],
            "detector_side": side,
            "family_class": family["class"],
            "class": family["class"],
            "support": support(vector),
            "rows": support(coefficient),
            "scope": "Explicit counterexample to globally extending this restricted-list dual",
        }
    witness_path = None
    if witness_directory is not None and len(result["support"]) < 20:
        witness_path = (
            witness_directory
            / f"pricing-{code['n']}-{result['detector_side']}-{family['class']}.json"
        )
        witness_path.write_text(json.dumps(result, indent=2) + "\n")
    verify_diagnostic(code, coordinates, family, result)
    result["independent_sparse_validation"] = "passed"
    if witness_path is not None:
        verify_witness(code, coordinates, result)
        witness_path.write_text(json.dumps(result, indent=2) + "\n")
    return result


def analyze_problem(record):
    families = record["families"]
    selected = {f["class"]: f for f in families}
    chosen = [selected[c] for c in record["coverage"]["classes"]]
    canonical = [f for f in families if f["class"] & (f["class"] - 1) == 0]
    bounds = [r["bound"] for r in record["rank_vs_bound"] if r["rank"] == 18]
    details = []
    for f in chosen:
        arithmetic = f["arithmetic"]
        weighted_size = sum(r["weight"] * len(r["support"]) for r in f["representatives"])
        value = Fraction(arithmetic["totalWeight"], arithmetic["cap"])
        dual = Fraction(
            f["restricted_dual"]["upper_numerator"], f["restricted_dual"]["denominator"]
        )
        details.append(
            {
                "class": f["class"],
                "bound": arithmetic["bound"],
                "value": str(value),
                "restricted_dual_upper": str(dual),
                "exact_restricted_duality_gap": str(dual - value),
                "positive_representatives": sum(r["weight"] > 0 for r in f["representatives"]),
                "weighted_mean_physical_weight": str(
                    Fraction(weighted_size, arithmetic["totalWeight"])
                ),
                "capacity_imbalance_over_mean_load": str(
                    Fraction(record["n"] * arithmetic["cap"], weighted_size)
                ),
                "dual_positive_positions": sum(
                    w > 0 for w in f["restricted_dual"]["qubit_weights"]
                ),
            }
        )
    # A dual upper <=19 excludes a threshold >19 only for its selected list.
    not_excluded = [
        f
        for f in families
        if f["restricted_dual"]["upper_numerator"] > 19 * f["restricted_dual"]["denominator"]
    ]
    from distance566 import echelon

    return {
        "n": record["n"],
        "detector_side": record["detector_side"],
        "bounded_side": record["bounded_side"],
        "complete_bound": max(bounds, default=0),
        "canonical_basis_only_bound": min((f["arithmetic"]["bound"] for f in canonical), default=0),
        "initial_reweighted_complete_bound": max(
            (r["bound"] for r in record["progress"][0]["rank_vs_bound"] if r["rank"] == 18),
            default=0,
        ),
        "rank_vs_bound": record["rank_vs_bound"],
        "rank_not_excluded_at_twenty_by_restricted_duals": len(
            echelon([f["class"] for f in not_excluded])
        ),
        "detector_weights": [len(d) for d in record["coverage"]["detectors"]],
        "paired_witness_weights": [
            len(w["support"]) for w in record["coverage"]["paired_witnesses"]
        ],
        "selected_families": details,
        "duality_scope": "Exact primal/dual interval for each stored list only; no global impossibility result",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, action="append", required=True)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--coordinates", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError("Use a fresh report directory")
    args.out.mkdir(parents=True)
    (args.out / "lighter-witnesses").mkdir()
    reports, candidates = [], {}
    header = None
    for directory in args.run:
        path = directory / "certificates.json.gz"
        record = load_json(path)
        header = {k: v for k, v in record.items() if k not in ("results", "parameters")}
        for entry in record["results"]:
            report = analyze_problem(entry)
            report["run_label"] = directory.name
            reports.append(report)
            key = (entry["n"], entry["detector_side"])
            old = candidates.get(key)
            if old is None or entry["coverage"]["bound"] > old[0]["coverage"]["bound"]:
                candidates[key] = (
                    entry,
                    directory.name,
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                )
    coordinates = load_json(args.coordinates)["coordinates"]
    codes = {n: read_code(args.upstream / f"codes/{n}-18-20.json", n) for n in (566, 578)}
    exported, diagnostics = [], []
    for key, (entry, label, digest) in sorted(candidates.items()):
        positive = positive_problem(entry)
        positive["source_run"] = label
        positive["source_certificate_sha256"] = digest
        exported.append(positive)
        if key[0] == 566:
            families = {f["class"]: f for f in entry["families"]}
            for c in entry["coverage"]["classes"]:
                diagnostic = pricing_diagnostic(
                    codes[key[0]],
                    coordinates[str(key[0])],
                    families[c],
                    args.out / "lighter-witnesses",
                )
                diagnostics.append(diagnostic)
                if len(diagnostic["support"]) < 20:
                    witness = dict(diagnostic)
                    verify_witness(codes[key[0]], coordinates[str(key[0])], witness)
    ready = header | {
        "results": exported,
        "scope": "Selected positive-weight bases for existing Lean interfaces; no new kernel bound",
    }
    with gzip.open(args.out / "lean-ready.json.gz", "wt") as stream:
        json.dump(ready, stream, indent=2)
    (args.out / "analysis.json").write_text(
        json.dumps(
            {
                "runs": reports,
                "diagnostics": diagnostics,
                "kernel_bound_unchanged": "3 <= d <= 20",
                "scope": "Finite certificates and algebraic diagnostics outside Lean; no novelty claim",
            },
            indent=2,
        )
        + "\n"
    )
    print(
        json.dumps(
            {
                "best_complete_bounds": [
                    {
                        "n": r["n"],
                        "detector_side": r["detector_side"],
                        "bounded_side": r["bounded_side"],
                        "bound": r["coverage"]["bound"],
                    }
                    for r in exported
                ],
                "zero_price_counterexamples": sum(
                    d["kind"] == "zero_price_representative" for d in diagnostics
                ),
                "opposite_cycle_obstructions": sum(
                    d["kind"] == "opposite_cycle_obstruction" for d in diagnostics
                ),
            }
        )
    )


if __name__ == "__main__":
    main()
