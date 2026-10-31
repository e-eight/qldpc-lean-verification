"""Focused unit-packing controls; all fixtures are solver independent."""

import copy
import hashlib

import pytest
from distance566_sector_disjoint import (
    X_CERTIFICATE_SHA256,
    certificate_bytes,
    greedy_disjoint,
    unit_case,
)
from distance566_sector_verify import INPUT_HASHES, arithmetic, check_case, load
from emit_removal566 import HASHES


def tiny_case():
    blocks = [list(range(7)), list(range(7, 14))]
    checks = [[start, start + i] for start in (0, 7) for i in range(1, 7)]
    code = {"n": 14, "checks": {"Z": checks, "X": []}}
    coordinates = {"Z": [[0], [7]], "X": blocks}
    record = {
        "n": 14,
        "logical_dimension": 2,
        "good_rank": 1,
        "detector_side": "Z",
        "bounded_side": "X",
        "selected_basis": {
            "detectors": [[0], [7]],
            "paired_witnesses": [{"support": block} for block in blocks],
        },
        "pool": [
            {"support": [q], "mask": 1 << q, "class": 2, "quotient_class": 1} for q in blocks[1]
        ],
    }
    case = {
        "suffix_pattern": 1,
        "canonical_class": 2,
        "selected_pairing_coordinates": 2,
        "reference_support": blocks[1],
        "eligible_count": 7,
    }
    return code, coordinates, record, case


def test_seven_unit_detectors_are_disjoint_and_frozen_check_passes():
    code, coordinates, record, case = tiny_case()
    result = greedy_disjoint(record["pool"], case)
    assert result["success"] and len(result["attempts"]) == 1
    replacement = unit_case(record, case, result["selected_indices"])
    observed = check_case(code, coordinates, record, replacement, require_seven=True)
    assert observed["cap"] == 1 and observed["totalWeight"] == observed["bound"] == 7
    assert "weights" not in case


def test_set_checker_rejects_overlap_despite_seven_different_indices():
    _, _, record, case = tiny_case()
    record["pool"][6] = copy.deepcopy(record["pool"][0])
    with pytest.raises(ValueError, match="overlap"):
        unit_case(record, case, list(range(7)))
    assert not greedy_disjoint(record["pool"], case)["success"]


def test_selected_detector_must_have_compatible_quotient():
    _, _, record, case = tiny_case()
    record["pool"][0]["quotient_class"] = 0
    with pytest.raises(ValueError, match="quotient"):
        unit_case(record, case, list(range(7)))


def test_physical_pairing_is_checked_even_when_quotient_tag_is_compatible():
    _, _, record, case = tiny_case()
    record["pool"][0].update(support=[0], mask=1)
    with pytest.raises(ValueError, match="physical"):
        unit_case(record, case, list(range(7)))
    with pytest.raises(ValueError, match="physical"):
        greedy_disjoint(record["pool"], case)


def test_six_disjoint_units_fail_strict_seven_control():
    code, coordinates, record, case = tiny_case()
    result = unit_case(record, case, list(range(7)))
    result["weights"] = result["weights"][:6]
    result["arithmetic"] = arithmetic([{q} for q in range(7, 13)], [1] * 6, 14)
    assert not check_case(code, coordinates, record, result)["strict_seven"]
    with pytest.raises(ValueError, match="Strict inequality"):
        check_case(code, coordinates, record, result, require_seven=True)


@pytest.mark.parametrize(
    "name,digest",
    [
        ("focused", "c097a4a92565609f73fff4520a494471b4d1204292846e5614877eea2da487e2"),
        ("analysis", "fa54c2e0c13097f3e2433c9a4ca2e36a82763bff02eb0cddfec76a1b0b84fe78"),
        ("coordinates", "171d2327eeda9aedb7a2585332fa2f495ac61aef5859e9cf6f9d8297415f34a6"),
        ("x32", "e5e8f386598416454e563307c55024cf6a7fff36ff1263daad5fbfd00489ccfd"),
        ("literal", "061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be"),
    ],
)
def test_all_input_hashes_are_pinned_and_reject_wrong_bytes(tmp_path, name, digest):
    actual = {**INPUT_HASHES, "x32": X_CERTIFICATE_SHA256, "literal": HASHES[566]}
    assert actual[name] == digest
    path = tmp_path / "wrong.json"
    path.write_text("{}\n")
    assert hashlib.sha256(path.read_bytes()).hexdigest() != digest
    with pytest.raises(ValueError, match="hash"):
        load(path, digest)


def test_restarts_are_bounded_and_certificate_bytes_are_deterministic():
    _, _, record, case = tiny_case()
    with pytest.raises(ValueError, match="eight"):
        greedy_disjoint(record["pool"], case, restarts=9)
    assert greedy_disjoint(record["pool"], case)["selected_indices"] == list(range(7))
    replacement = unit_case(record, case, list(range(7)))
    assert certificate_bytes(replacement) == certificate_bytes(copy.deepcopy(replacement))
    assert certificate_bytes(replacement)[4:8] == bytes(4)
