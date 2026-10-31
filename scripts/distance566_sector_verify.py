"""Independent sparse, exact validation of numerical sector-packing certificates.

This module imports neither the search nor NumPy/SciPy. Its successful checks
remain finite mathematical validation, not a new Lean distance theorem.
"""

import argparse
import gzip
import hashlib
import json
from pathlib import Path

from distance566_weighted_verify import (
    check_cycle,
    class_of,
    natural,
    rank_sets,
    sparse,
    validate_problem,
)
from emit_removal566 import HASHES, REVISION, read_code

SCHEMA = "qldpc-sector-packing-v1"
BASELINE = "e9e33f21946bc781e6ae3c3c04adaac86abb36dd"
INPUT_HASHES = {
    "focused": "c097a4a92565609f73fff4520a494471b4d1204292846e5614877eea2da487e2",
    "analysis": "fa54c2e0c13097f3e2433c9a4ca2e36a82763bff02eb0cddfec76a1b0b84fe78",
    "coordinates": "171d2327eeda9aedb7a2585332fa2f495ac61aef5859e9cf6f9d8297415f34a6",
}


def load(path, expected=None):
    raw = path.read_bytes()
    if expected and hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError("Wrong immutable input hash")
    return json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)


def bits(value, width, zero=False):
    natural(value, "binary coordinate", positive=not zero)
    if value >= 2**width:
        raise ValueError("Binary coordinate out of range")
    return {i for i in range(width) if value // 2**i % 2}


def parity(a, b):
    return len(a & b) % 2


def xor_supports(supports):
    result = set()
    for support in supports:
        result.symmetric_difference_update(support)
    return result


def checked_support(entry, n):
    support = sparse(entry["support"], n)
    mask = natural(entry["mask"], "physical mask", positive=True)
    if mask >= 2**n or mask != sum(2**q for q in support):
        raise ValueError("Physical support/mask mismatch")
    return support


def row_witness(rows, base, vector, entry):
    indices = sparse(entry["rows"], len(rows))
    mask = natural(entry["row_mask"], "row mask")
    if mask >= 2 ** len(rows) or mask != sum(2**i for i in indices):
        raise ValueError("Row index/mask mismatch")
    rebuilt = base.copy()
    for i in indices:
        rebuilt.symmetric_difference_update(rows[i])
    if rebuilt != vector:
        raise ValueError("Incorrect original-row witness against own base")


def arithmetic(supports, weights, n):
    loads = [0] * n
    total = 0
    for vector, weight in zip(supports, weights, strict=True):
        weight = natural(weight, "packing weight", positive=True)
        total += weight
        for q in vector:
            loads[q] += weight
    cap = max(loads, default=0)
    if cap <= 0 or total <= 0:
        raise ValueError("Empty positive packing")
    return {
        "loads": loads,
        "totalWeight": total,
        "cap": cap,
        "bound": (total + cap - 1) // cap,
        "strict_seven": 6 * cap < total,
    }


def check_arithmetic(expected, observed):
    for name in ("totalWeight", "cap", "bound"):
        natural(observed[name], name, positive=True)
    if any(type(value) is not int or value < 0 for value in observed["loads"]):
        raise ValueError("Invalid natural load")
    if type(observed["strict_seven"]) is not bool or expected != observed:
        raise ValueError("Incorrect exact loads/cap/strict threshold")


def source_inputs(upstream, focused_path, analysis_path, coordinate_path):
    code = read_code(upstream / "codes/566-18-20.json", 566)
    full = load(focused_path, INPUT_HASHES["focused"])
    analysis = load(analysis_path, INPUT_HASHES["analysis"])
    coordinates = load(coordinate_path, INPUT_HASHES["coordinates"])["coordinates"]["566"]
    selected = {}
    reports = []
    for record, label in ((full, "original_unpruned"), (analysis, "analysis_export")):
        if record["challenge_revision"] != REVISION:
            raise ValueError("Wrong challenge revision")
        targets = [r for r in record["results"] if r["n"] == 566]
        if len(targets) != 2 or {r["detector_side"] for r in targets} != {"X", "Z"}:
            raise ValueError("Incomplete target source sectors")
        for entry in targets:
            result = validate_problem(code, coordinates, entry)
            reports.append({"input": label, **result})
            if label == "original_unpruned":
                if len(entry["families"]) != 64:
                    raise ValueError("Expected original 64-class source")
                selected[entry["bounded_side"]] = entry
            elif selected[entry["bounded_side"]]["coverage"] != entry["coverage"]:
                raise ValueError("Selected basis changed in analysis export")
    return code, coordinates, selected, reports


def check_case(code, coordinates, record, case, require_seven=False):
    """Check physical pairings independently of any stored class tag."""
    n, k = code["n"], record["logical_dimension"]
    side, bounded = record["detector_side"], record["bounded_side"]
    g, d = record["good_rank"], k - record["good_rank"]
    pattern = natural(case["suffix_pattern"], "suffix pattern", positive=True)
    chosen = bits(pattern, d)
    expected_pairing = pattern * 2**g
    if case["selected_pairing_coordinates"] != expected_pairing:
        raise ValueError("Wrong selected pairing coordinates")
    bits(case["selected_pairing_coordinates"], k)
    reference = sparse(case["reference_support"], n)
    paired = [sparse(w["support"], n) for w in record["selected_basis"]["paired_witnesses"]]
    if reference != xor_supports(paired[g + i] for i in chosen):
        raise ValueError("Wrong physical reference support")
    check_cycle(reference, [sparse(r, n) for r in code["checks"][side]])
    canonical = class_of(reference, [sparse(r, n) for r in coordinates[side]])
    bits(case["canonical_class"], k)
    if canonical != case["canonical_class"]:
        raise ValueError("Wrong canonical logical class")
    detectors = [sparse(v, n) for v in record["selected_basis"]["detectors"]]
    if class_of(reference, detectors) != expected_pairing:
        raise ValueError("Selected physical reference pairing mismatch")
    indices, vectors, weights = set(), [], []
    for index, weight in case["weights"]:
        natural(index, "pool index")
        if index >= len(record["pool"]) or index in indices:
            raise ValueError("Invalid or repeated pool index")
        indices.add(index)
        entry = record["pool"][index]
        if parity(bits(entry["quotient_class"], d), chosen) != 1:
            raise ValueError("Incompatible quotient class")
        if parity(bits(entry["class"], k), bits(canonical, k)) != 1:
            raise ValueError("Incompatible canonical class")
        vector = sparse(entry["support"], n)
        if parity(vector, reference) != 1:
            raise ValueError("Direct physical pairing is not one")
        vectors.append(vector)
        weights.append(weight)
    observed = arithmetic(vectors, weights, n)
    check_arithmetic(observed, case["arithmetic"])
    if require_seven and not observed["strict_seven"]:
        raise ValueError("Strict inequality for seven failed")
    eligible = [
        entry for entry in record["pool"] if parity(bits(entry["quotient_class"], d), chosen)
    ]
    if case["eligible_count"] != len(eligible):
        raise ValueError("Incorrect eligible pool size")
    dual = case.get("restricted_dual")
    if dual is not None:
        prices = [natural(p, "restricted price") for p in dual["qubit_weights"]]
        denominator = natural(dual["denominator"], "dual denominator", positive=True)
        numerator = natural(dual["upper_numerator"], "dual numerator", positive=True)
        if len(prices) != n or sum(prices) != numerator:
            raise ValueError("Wrong restricted dual dimensions")
        if any(sum(prices[q] for q in e["support"]) < denominator for e in eligible):
            raise ValueError("Infeasible restricted-pool dual")
        if observed["totalWeight"] * denominator > observed["cap"] * numerator:
            raise ValueError("Exact weak duality failed")
    return {
        "suffix_pattern": pattern,
        "canonical_class": canonical,
        "bounded_side": bounded,
        **{key: observed[key] for key in ("totalWeight", "cap", "bound", "strict_seven")},
    }


def validate_record(code, coordinates, record, source=None):
    if record["schema"] != SCHEMA or record["n"] != code["n"]:
        raise ValueError("Wrong sector schema or physical size")
    n, k = code["n"], natural(record["logical_dimension"], "logical dimension", positive=True)
    side, bounded = record["detector_side"], record["bounded_side"]
    if side not in ("X", "Z") or bounded != ("Z" if side == "X" else "X"):
        raise ValueError("Swapped detector/bounded sectors")
    if k != 18 or record["target_bound"] != 7:
        raise ValueError("Wrong logical dimension or target threshold")
    rows = {s: [sparse(r, n) for r in code["checks"][s]] for s in ("X", "Z")}
    old = {s: [sparse(r, n) for r in coordinates[s]] for s in ("X", "Z")}
    if any(len(old[s]) != k for s in old):
        raise ValueError("Incomplete canonical paired bases")
    if any(parity(x, z) for x in rows["X"] for z in rows["Z"]):
        raise ValueError("Noncommuting literals")
    ranks = {s: rank_sets(rows[s]) for s in rows}
    if n - sum(ranks.values()) != k or record["matrix_ranks"] != ranks:
        raise ValueError("Literal rank/dimension mismatch")
    for value in record["matrix_ranks"].values():
        natural(value, "matrix rank")
    for s in old:
        for vector in old[s]:
            check_cycle(vector, rows["Z" if s == "X" else "X"])
    if any(
        parity(x, z) != (i == j) for i, x in enumerate(old["X"]) for j, z in enumerate(old["Z"])
    ):
        raise ValueError("Canonical pairing is not identity")
    basis = record["selected_basis"]
    if basis["detector_side"] != side or basis["bounded_side"] != bounded:
        raise ValueError("Selected basis sector mismatch")
    labels = basis["classes"]
    if len(labels) != k or rank_sets([bits(c, k) for c in labels]) != k:
        raise ValueError("Dependent selected detector basis")
    detectors = [sparse(v, n) for v in basis["detectors"]]
    paired = []
    if len(detectors) != k or len(basis["paired_witnesses"]) != k:
        raise ValueError("Incomplete selected pairing")
    for i, vector in enumerate(detectors):
        check_cycle(vector, rows[bounded])
        if class_of(vector, old[bounded]) != labels[i]:
            raise ValueError("Selected detector canonical class mismatch")
    for witness in basis["paired_witnesses"]:
        vector = sparse(witness["support"], n)
        indices = sparse(witness["old_basis_rows"], k)
        if vector != xor_supports(old[bounded][i] for i in indices):
            raise ValueError("Selected witness basis change mismatch")
        check_cycle(vector, rows[side])
        paired.append(vector)
    if any(parity(w, v) != (i == j) for i, w in enumerate(paired) for j, v in enumerate(detectors)):
        raise ValueError("Selected pairing is not identity")
    g = natural(record["good_rank"], "good rank")
    if not 0 < g < k or len(record["good_families"]) != g:
        raise ValueError("Wrong good-span dimension")
    if rank_sets([bits(c, k) for c in labels[:g]]) != g:
        raise ValueError("Dependent good span")
    families = {}
    natural(record["source_family_count"], "source family count", positive=True)
    for entry in record["families"]:
        c = entry["class"]
        bits(c, k)
        if c in families:
            raise ValueError("Duplicate source family")
        base = checked_support({"support": entry["base_support"], "mask": entry["base_mask"]}, n)
        check_cycle(base, rows[bounded])
        if class_of(base, old[bounded]) != c:
            raise ValueError("Source base class mismatch")
        coefficient = class_of(base, paired)
        bits(entry["selected_class_coordinates"], k)
        bits(entry["quotient_class"], k - g, zero=True)
        natural(entry["source_family_index"], "source family index")
        if (
            entry["selected_class_coordinates"] != coefficient
            or entry["quotient_class"] != coefficient // 2**g
        ):
            raise ValueError("Wrong selected or quotient detector class")
        families[c] = (entry, base)
    if len(families) != record["source_family_count"]:
        raise ValueError("Wrong source-family count")
    for i, certificate in enumerate(record["good_families"]):
        natural(certificate["selected_index"], "selected index")
        c = certificate["class"]
        if c != labels[i] or certificate["selected_index"] != i:
            raise ValueError("Wrong good-family prefix/span")
        entry, base = families[c]
        if base != detectors[i] or entry["quotient_class"] != 0:
            raise ValueError("Good-family base or annihilator mismatch")
        vectors, weights = [], []
        for rep in certificate["representatives"]:
            natural(rep["source_rep_index"], "source representative index")
            vector = checked_support(rep, n)
            row_witness(rows[side], base, vector, rep)
            check_cycle(vector, rows[bounded])
            if class_of(vector, old[bounded]) != c:
                raise ValueError("Good-family representative changed class")
            vectors.append(vector)
            weights.append(rep["weight"])
        measured = arithmetic(vectors, weights, n)
        check_arithmetic(measured, certificate["arithmetic"])
        if not measured["strict_seven"]:
            raise ValueError("Good-family strict threshold failed")
    d = k - g
    annihilator = record["annihilator"]
    expected = [class_of(paired[i], old[side]) for i in range(g, k)]
    if annihilator != {
        "dimension": d,
        "canonical_basis": expected,
        "selected_pairing_basis": [2**i for i in range(g, k)],
    }:
        raise ValueError("Wrong annihilator basis/dimension")
    if rank_sets([bits(c, k) for c in expected]) != d or any(
        parity(bits(c, k), bits(r, k)) for c in labels[:g] for r in expected
    ):
        raise ValueError("Incomplete annihilator")
    seen = set()
    for rep in record["pool"]:
        vector = checked_support(rep, n)
        if rep["mask"] in seen:
            raise ValueError("Duplicate physical pool support")
        seen.add(rep["mask"])
        c = class_of(vector, old[bounded])
        coefficient = class_of(vector, paired)
        bits(rep["class"], k)
        bits(rep["selected_class_coordinates"], k)
        bits(rep["quotient_class"], d)
        if rep["class"] != c or rep["selected_class_coordinates"] != coefficient:
            raise ValueError("Pool canonical/selected class mismatch")
        if rep["quotient_class"] != coefficient // 2**g or rep["quotient_class"] == 0:
            raise ValueError("Zero or wrong quotient class retained")
        check_cycle(vector, rows[bounded])
        if not rep["provenances"]:
            raise ValueError("Missing own-base provenance")
        for provenance in rep["provenances"]:
            bits(provenance["family_class"], k)
            natural(provenance["source_rep_index"], "source representative index")
            if provenance["family_class"] != c:
                raise ValueError("Wrong own-base family class")
            row_witness(rows[side], families[c][1], vector, provenance)
    scope = record["residue_scope"]
    if scope["total_nonzero"] != 2**d - 1:
        raise ValueError("Wrong total residue count")
    patterns = [r["suffix_pattern"] for r in record["residues"]]
    if scope["mode"] == "complete":
        if d != 3 or patterns != list(range(1, 2**d)):
            raise ValueError("Missing or duplicate nonzero sum residue")
    elif scope["mode"] == "pilot":
        if (
            not 0 < len(patterns) <= 32
            or patterns != sorted(range(1, 2**d), key=lambda x: (x.bit_count(), x))[: len(patterns)]
        ):
            raise ValueError("Wrong deterministic pilot residues")
    else:
        raise ValueError("Unknown residue coverage scope")
    if source is not None:
        check_source_alignment(record, source)
    results = [check_case(code, coordinates, record, case) for case in record["residues"]]
    all_passed = all(r["strict_seven"] for r in results)
    if record["all_requested_passed"] is not all_passed:
        raise ValueError("Wrong aggregate threshold claim")
    return {
        "status": "exactly_validated",
        "detector_side": side,
        "bounded_side": bounded,
        "good_rank": g,
        "annihilator_dimension": d,
        "cases_checked": len(results),
        "complete_residue_coverage": scope["mode"] == "complete",
        "all_requested_passed": all_passed,
        "pool_supports": len(seen),
        "results": results,
        "scope": "Numerical finite certificate; no new kernel distance result",
    }


def check_source_alignment(record, source):
    if record["selected_basis"] != source["coverage"]:
        raise ValueError("Original selected coverage changed")
    original = {f["class"]: (i, f) for i, f in enumerate(source["families"])}
    if set(original) != {f["class"] for f in record["families"]}:
        raise ValueError("Original source classes omitted")
    by_class = {f["class"]: f for f in record["families"]}
    expected_pool = {}
    good = [
        f for f in source["families"] if 6 * f["arithmetic"]["cap"] < f["arithmetic"]["totalWeight"]
    ]
    if rank_sets([bits(f["class"], 18) for f in good]) != record["good_rank"]:
        raise ValueError("Wrong original good-span rank")
    for c, (i, family) in original.items():
        entry = by_class[c]
        if entry["source_family_index"] != i or entry["base_support"] != family["base_support"]:
            raise ValueError("Wrong source-family reference")
        if entry["quotient_class"]:
            for j, rep in enumerate(family["representatives"]):
                key = tuple(rep["support"])
                expected_pool.setdefault(key, []).append((c, j, tuple(rep["rows"])))
    actual = {}
    for rep in record["pool"]:
        actual[tuple(rep["support"])] = [
            (p["family_class"], p["source_rep_index"], tuple(p["rows"])) for p in rep["provenances"]
        ]
    if actual != expected_pool:
        raise ValueError("Global pool lost original supports or provenances")
    for certificate in record["good_families"]:
        _, family = original[certificate["class"]]
        expected = [(j, r) for j, r in enumerate(family["representatives"]) if r["weight"]]
        actual = certificate["representatives"]
        if len(expected) != len(actual) or any(
            r["source_rep_index"] != j
            or r["support"] != old["support"]
            or r["rows"] != old["rows"]
            or r["weight"] != old["weight"]
            for r, (j, old) in zip(actual, expected, strict=True)
        ):
            raise ValueError("Good-family source representatives changed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--focused", type=Path, required=True)
    parser.add_argument("--analysis", type=Path, required=True)
    parser.add_argument("--coordinates", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    code, coordinates, sources, _ = source_inputs(
        args.upstream, args.focused, args.analysis, args.coordinates
    )
    record = load(args.certificate)
    if (
        record["baseline_commit"] != BASELINE
        or record["challenge_revision"] != REVISION
        or record["literal_sha256"] != HASHES[566]
        or record["input_sha256"] != INPUT_HASHES
    ):
        raise ValueError("Wrong certificate provenance")
    report = validate_record(code, coordinates, record, sources[record["bounded_side"]])
    report["certificate_sha256"] = hashlib.sha256(args.certificate.read_bytes()).hexdigest()
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}))


if __name__ == "__main__":
    main()
