"""Small independent controls for the untrusted distance-certificate generator."""

import numpy as np
import pytest
from distance566 import combination, coordinates, dot, kernel, pack, structural_pilot, verify_family
from distance566_packproof import prune
from distance566_ris import systematic_kernel
from distance566_verify import validate


def test_kernel():
    basis = kernel([0b011, 0b110], 3)
    assert basis == [0b111]
    assert all(dot(v, r) == 0 for v in basis for r in [0b011, 0b110])


def test_paired_coordinates_with_stored_x_first():
    code = {
        "n": 4,
        "k": 2,
        "checks": {"X": [[0, 1, 2, 3]], "Z": [[0, 1, 2, 3]]},
        "distance": {"X": {"witness": [0, 1], "value": 2}, "Z": {"witness": [0, 2], "value": 2}},
    }
    result = coordinates(code)
    assert result["X"][0] == [0, 1]
    assert len(result["X"]) == len(result["Z"]) == 2
    assert [[dot(pack(x), pack(z)) for z in result["Z"]] for x in result["X"]] == [[1, 0], [0, 1]]


def test_integer_rounding_and_membership():
    family = [
        {"support": [0], "rows": [], "weight": 2},
        {"support": [1], "rows": [0], "weight": 1},
    ]
    assert verify_family([0b11], 0b01, 2, family) == {"totalWeight": 3, "cap": 2, "bound": 2}
    family[1]["rows"] = []
    with pytest.raises(ValueError, match="row combination"):
        verify_family([0b11], 0b01, 2, family)


@pytest.mark.parametrize("indices", [[0, 0], [-1], [True]])
def test_malformed_support(indices):
    with pytest.raises(ValueError):
        pack(indices)


def test_out_of_range_combination():
    with pytest.raises(ValueError):
        combination([1], 2)


def test_empty_family():
    with pytest.raises(ValueError):
        verify_family([3], 1, 2, [])


def test_complete_small_cycle_census_distinguishes_boundaries():
    code = {
        "n": 4,
        "checks": {"X": [[0, 1, 2, 3]], "Z": [[0, 1, 2, 3]]},
    }
    # The ordinary classical kernel has weight-two words, and these are logicals.
    with pytest.raises(ValueError, match="nontrivial logical"):
        structural_pilot(code)


def test_small_cycle_census_includes_degenerate_stabilizers():
    code = {"n": 3, "checks": {"X": [[0, 1], [2]], "Z": [[0, 1]]}}
    result = structural_pilot(code)
    assert result["X"]["all_nonzero_cycles_weight_at_most_three"] == [[2], [0, 1], [0, 1, 2]]
    assert result["Z"]["all_nonzero_cycles_weight_at_most_three"] == [[0, 1]]


def test_independent_sparse_validator_checks_same_class_and_arithmetic():
    code = {"checks": {"X": [[0, 1, 2, 3]], "Z": [[0, 1, 2, 3]]}}
    coordinates = {"4": {"X": [[0, 1]], "Z": [[0, 2]]}}
    entry = {
        "n": 4,
        "side": "X",
        "coordinate": 0,
        "family": [
            {"support": [0, 1], "rows": [], "weight": 1},
            {"support": [2, 3], "rows": [0], "weight": 1},
        ],
        "arithmetic": {"totalWeight": 2, "cap": 1, "bound": 2},
    }
    assert (
        validate({4: code}, coordinates, {"families": [entry]})["4-X"]["minimum_family_bound"] == 2
    )
    entry["arithmetic"]["cap"] = 2
    with pytest.raises(ValueError, match="arithmetic"):
        validate({4: code}, coordinates, {"families": [entry]})
    entry["family"][1]["rows"] = []
    with pytest.raises(ValueError, match="row-combination"):
        validate({4: code}, coordinates, {"families": [entry]})


def test_information_set_kernel_has_independently_zero_syndrome():
    matrix = np.array([[1, 1, 0], [0, 1, 1]], dtype=np.uint8)
    vectors = [pack(int(i) for i in indices) for indices in systematic_kernel(matrix)]
    assert vectors == [7]
    assert all(dot(v, row) == 0 for v in vectors for row in [3, 6])


def test_pruning_preserves_the_strict_integer_threshold():
    import random

    family = [{"support": [q], "rows": [], "weight": 1} for q in range(5)]
    reduced = prune(family, 3, random.Random(1))
    assert len(reduced) == 3
    assert {tuple(v["support"]) for v in reduced} <= {tuple(v["support"]) for v in family}
