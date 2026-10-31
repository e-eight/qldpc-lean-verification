"""Exact certificate rejection, basis-change, and weighted-pricing controls."""

import copy
from fractions import Fraction

import numpy as np
import pytest
from distance566 import combination, dot, pack
from distance566_weighted import (
    Problem,
    exact_dual,
    exported_candidate,
    independent_pairing,
    integer_packing,
    optimize_weights,
    rank_curve,
    row_solver,
    select_basis,
    solve_rows,
)
from distance566_weighted_report import positive_problem, pricing_diagnostic
from distance566_weighted_verify import validate_problem


def fixture():
    # Nine independent [[4,2,2]] blocks give eighteen logical coordinates.
    rows = [list(range(4 * i, 4 * i + 4)) for i in range(9)]
    xs, zs = [], []
    for i in range(9):
        a = [4 * i, 4 * i + 1]
        b = [4 * i, 4 * i + 2]
        xs.extend([a, b])
        zs.extend([b, a])
    code = {"n": 36, "k": 18, "checks": {"X": rows, "Z": rows}}
    coordinates = {"X": xs, "Z": zs}
    labels = [1, 3, *(1 << i for i in range(2, 18))]
    families = []
    for label in labels:
        indices = [i for i in range(18) if label >> i & 1]
        base = set()
        for i in indices:
            base.symmetric_difference_update(zs[i])
        block = indices[0] // 2
        other = base ^ set(rows[block])
        prices = [0] * 36
        prices[min(base)] = prices[min(other)] = 1
        families.append(
            {
                "n": 36,
                "detector_side": "Z",
                "bounded_side": "X",
                "class": label,
                "base_support": sorted(base),
                "representatives": [
                    {"support": sorted(base), "rows": [], "weight": 2},
                    {"support": sorted(other), "rows": [block], "weight": 1},
                ],
                "arithmetic": {"totalWeight": 3, "cap": 2, "bound": 2},
                "restricted_dual": {
                    "qubit_weights": prices,
                    "denominator": 1,
                    "upper_numerator": 2,
                },
            }
        )
    record = {
        "n": 36,
        "detector_side": "Z",
        "bounded_side": "X",
        "families": families,
        "rank_vs_bound": rank_curve(families),
        "coverage": {
            "detector_side": "Z",
            "bounded_side": "X",
            "classes": labels,
            "detectors": [f["base_support"] for f in families],
            "bound": 2,
            "paired_witnesses": independent_pairing(labels, [pack(x) for x in xs]),
        },
    }
    return code, coordinates, record


def test_weighted_lp_improves_restricted_uniform_value_exactly():
    pytest.importorskip("scipy")
    vectors = [1, 1, 1, 2, 4]
    uniform = integer_packing(vectors, [1] * 5, 3)
    weights, arithmetic, dual, status = optimize_weights(vectors, 3)
    assert uniform["bound"] == 2
    assert status["success"]
    assert Fraction(arithmetic["totalWeight"], arithmetic["cap"]) == 3
    assert arithmetic["bound"] == 3
    assert arithmetic == integer_packing(vectors, weights, 3)
    assert (
        arithmetic["totalWeight"] * dual["denominator"]
        <= arithmetic["cap"] * dual["upper_numerator"]
    )


def test_strict_threshold_retains_a_tiny_exact_surplus():
    assert integer_packing([1, 2], [999999, 1], 2)["bound"] == 2


def test_exact_dual_repairs_float_infeasibility():
    certificate = exact_dual([1, 2, 3], [0.0, 0.0], 2)
    assert certificate["qubit_weights"] == [1000000, 1000000]


def test_row_coefficient_recovery():
    rows = [0b011, 0b110]
    coefficients = solve_rows(0b101, row_solver(rows))
    assert combination(rows, coefficients) == 0b101
    with pytest.raises(ValueError, match="outside"):
        solve_rows(0b001, row_solver(rows))


def test_basis_selection_avoids_a_weak_forced_coordinate():
    families = [
        {"class": 1, "base_support": [0], "arithmetic": {"bound": 1, "totalWeight": 1, "cap": 1}}
    ]
    families += [
        {"class": c, "base_support": [0], "arithmetic": {"bound": 5, "totalWeight": 5, "cap": 1}}
        for c in [3, *(1 << i for i in range(1, 18))]
    ]
    selected = select_basis(families)
    assert len(selected) == 18
    assert 1 not in {f["class"] for f in selected}
    assert rank_curve(families)[4]["rank"] == 18


def test_independent_detector_basis_keeps_separate_paired_witnesses():
    code, coordinates, record = fixture()
    # The existing good X basis and the selected Z detectors are not mutually dual.
    assert dot(pack(coordinates["X"][0]), pack(record["coverage"]["detectors"][1])) == 1
    validated = validate_problem(code, coordinates, record)
    assert validated["exact_finite_complete_bound"] == 2
    assert validated["coverage_pairing"] == "identity"


@pytest.mark.parametrize(
    "fault", ["row", "capacity", "class", "dual", "basis", "sector", "bool_weight"]
)
def test_independent_validator_rejects_malformed_certificates(fault):
    code, coordinates, source = fixture()
    record = copy.deepcopy(source)
    if fault == "row":
        record["families"][0]["representatives"][1]["rows"] = []
    if fault == "capacity":
        record["families"][0]["arithmetic"]["cap"] = 1
    if fault == "class":
        record["families"][0]["class"] = 2
    if fault == "dual":
        record["families"][0]["restricted_dual"]["qubit_weights"] = [0] * 36
    if fault == "basis":
        record["coverage"]["paired_witnesses"][0]["old_basis_rows"] = []
    if fault == "sector":
        record["bounded_side"] = "Z"
    if fault == "bool_weight":
        record["families"][0]["representatives"][0]["weight"] = True
    with pytest.raises(ValueError):
        validate_problem(code, coordinates, record)


def test_price_biased_information_set_recovers_actual_rows():
    code, coordinates, _ = fixture()
    problem = Problem(code, "Z", coordinates, 17, 32)
    base = pack(coordinates["Z"][0])
    vector, coefficients = problem.information_set(base, np.arange(36, dtype=float) + 1)
    assert base ^ vector == combination(problem.rows, coefficients)


def test_derived_moves_preserve_class_and_improve_exact_price_cost():
    code, coordinates, _ = fixture()
    problem = Problem(code, "Z", coordinates, 19, 32)
    base = pack(coordinates["Z"][0])
    prices = np.arange(36, dtype=float) + 1
    _, _, moves = problem.information_set(base, prices, with_moves=True)
    assert all(mask == combination(problem.rows, coefficients) for mask, coefficients in moves)
    vector, coefficients = problem.descend_derived(base, 0, prices, moves)
    assert base ^ vector == combination(problem.rows, coefficients)
    assert sum(prices[q] for q in range(36) if vector >> q & 1) <= sum(
        prices[q] for q in range(36) if base >> q & 1
    )


def test_reanchoring_to_a_light_detector_updates_every_row_witness():
    code, coordinates, _ = fixture()
    problem = Problem(code, "Z", coordinates, 21, 32)
    light = pack(coordinates["Z"][0])
    heavy = light ^ problem.rows[1]
    candidate = {
        "class": 1,
        "base": heavy,
        "reps": {heavy: 0, light: 2},
        "rounds": 0,
        "weights": [0, 1],
        "arithmetic": {"totalWeight": 1, "cap": 1, "bound": 1},
        "dual": {},
        "solver": {},
    }
    exported = exported_candidate(problem, candidate)
    assert pack(exported["base_support"]) == light
    for entry in exported["representatives"]:
        assert pack(entry["support"]) == light ^ combination(problem.rows, pack(entry["rows"]))


def test_positive_weight_export_preserves_complete_coverage():
    code, coordinates, source = fixture()
    source["families"][0]["representatives"].append(
        {"support": source["families"][0]["base_support"], "rows": [], "weight": 0}
    )
    result = positive_problem(source)
    assert len(source["families"][0]["representatives"]) == 3
    assert len(result["families"][0]["representatives"]) == 2
    assert validate_problem(code, coordinates, result)["exact_finite_complete_bound"] == 2


def test_exact_erasure_diagnostic_finds_an_unseen_zero_price_column():
    code, coordinates, source = fixture()
    family = source["families"][0]
    family["representatives"] = family["representatives"][:1]
    family["restricted_dual"]["qubit_weights"] = [1] + [0] * 35
    family["restricted_dual"]["upper_numerator"] = 1
    result = pricing_diagnostic(code, coordinates, family)
    assert result["kind"] == "zero_price_representative"
    assert result["support"] == [1, 3]


def test_erasure_obstruction_is_an_actual_opposite_logical_cycle():
    code, coordinates, source = fixture()
    result = pricing_diagnostic(code, coordinates, source["families"][0])
    assert result["kind"] == "opposite_cycle_obstruction"
    assert len(result["support"]) == 2
    assert result["independent_sparse_validation"] == "passed"


@pytest.mark.parametrize("weights", [[-1], [True], [0]])
def test_reject_invalid_or_empty_integer_weights(weights):
    with pytest.raises(ValueError):
        integer_packing([1], weights, 1)
