"""Exact sector orientation, completeness, provenance and rounding controls."""

import copy
import gzip
import json
from fractions import Fraction

import pytest
from distance566_sector import (
    build_problem,
    choose_weights,
    exact_arithmetic,
    gzip_bytes,
    pack_residue,
)
from distance566_sector_verify import check_case, validate_record


def repetition_fixture(bounded="Z", good_rank=15):
    # Eighteen disjoint seven-bit repetition sectors: k=18, one distance seven.
    paired_rows = [[7 * i, 7 * i + j] for i in range(18) for j in range(1, 7)]
    singles = [[7 * i] for i in range(18)]
    blocks = [list(range(7 * i, 7 * i + 7)) for i in range(18)]
    side = "X" if bounded == "Z" else "Z"
    code = {"n": 126, "checks": {side: paired_rows, bounded: []}}
    coordinates = {side: singles, bounded: blocks}
    families = []
    for i in range(18):
        reps = [
            {
                "support": [7 * i + j],
                "rows": [] if j == 0 else [6 * i + j - 1],
                "weight": 1 if i < good_rank or j < 6 else 0,
            }
            for j in range(7)
        ]
        total = 7 if i < good_rank else 6
        families.append(
            {
                "n": 126,
                "detector_side": side,
                "bounded_side": bounded,
                "class": 1 << i,
                "base_support": singles[i],
                "representatives": reps,
                "arithmetic": {"totalWeight": total, "cap": 1, "bound": total},
            }
        )
    source = {
        "detector_side": side,
        "bounded_side": bounded,
        "families": families,
        "coverage": {
            "detector_side": side,
            "bounded_side": bounded,
            "classes": [1 << i for i in range(18)],
            "detectors": singles,
            "paired_witnesses": [{"support": blocks[i], "old_basis_rows": [i]} for i in range(18)],
            "bound": 6,
        },
    }
    record = build_problem(code, coordinates, source, bounded, None if bounded == "Z" else 32)
    record["residues"] = [pack_residue(record, case, source, 0)[0] for case in record["residues"]]
    record["all_requested_passed"] = True
    return code, coordinates, source, record


def nonidentity_bell_fixture(bounded="Z", good_rank=15):
    """Nonvacuous boundaries and a triangular detector/dual basis change."""
    side = "X" if bounded == "Z" else "Z"
    bell = [126, 127]
    rows = [[7 * i, 7 * i + j] for i in range(18) for j in range(1, 7)]
    code = {"n": 128, "checks": {side: rows + [bell], bounded: [bell]}}
    singles = [[7 * i] for i in range(18)]
    blocks = [list(range(7 * i, 7 * i + 7)) for i in range(18)]
    coordinates = {side: singles, bounded: blocks}
    labels = [1 << i for i in range(18)]
    labels[good_rank] ^= 1 << (good_rank + 1)
    paired = [{"support": blocks[i], "old_basis_rows": [i]} for i in range(18)]
    paired[good_rank + 1] = {
        "support": blocks[good_rank] + blocks[good_rank + 1],
        "old_basis_rows": [good_rank, good_rank + 1],
    }
    families = []
    for i in range(18):
        logical_blocks = [i, i + 1] if i == good_rank else [i]
        # Some valid detector bases meet the opposite Bell boundary in two bits.
        has_bell = i in (0, good_rank)
        base = [7 * block for block in logical_blocks] + (bell if has_bell else [])
        reps = []
        for j in range(7):
            indices = [6 * block + j - 1 for block in logical_blocks] if j else []
            if has_bell:
                indices.append(108)
            reps.append(
                {
                    "support": [7 * block + j for block in logical_blocks],
                    "rows": indices,
                    "weight": 1 if i < good_rank or j < 6 else 0,
                }
            )
        total = 7 if i < good_rank else 6
        families.append(
            {
                "n": 128,
                "detector_side": side,
                "bounded_side": bounded,
                "class": labels[i],
                "base_support": base,
                "representatives": reps,
                "arithmetic": {"totalWeight": total, "cap": 1, "bound": total},
            }
        )
    source = {
        "detector_side": side,
        "bounded_side": bounded,
        "families": families,
        "coverage": {
            "detector_side": side,
            "bounded_side": bounded,
            "classes": labels,
            "detectors": [family["base_support"] for family in families],
            "paired_witnesses": paired,
            "bound": 6,
        },
    }
    record = build_problem(code, coordinates, source, bounded, None if bounded == "Z" else 32)
    record["residues"] = [pack_residue(record, case, source, 0)[0] for case in record["residues"]]
    record["all_requested_passed"] = True
    return code, coordinates, source, record


def assert_selected_identity(record):
    basis = record["selected_basis"]
    assert all(
        len(set(witness["support"]) & set(detector)) % 2 == (i == j)
        for i, witness in enumerate(basis["paired_witnesses"])
        for j, detector in enumerate(basis["detectors"])
    )


def permute_selected_basis(record, first, second):
    """Keep the physical paired basis and detector coefficient tags consistent."""
    basis = record["selected_basis"]
    for key in ("classes", "detectors", "paired_witnesses"):
        basis[key][first], basis[key][second] = basis[key][second], basis[key][first]
    paired = [set(w["support"]) for w in basis["paired_witnesses"]]
    for collection, support_key in (
        (record["families"], "base_support"),
        (record["pool"], "support"),
    ):
        for entry in collection:
            vector = set(entry[support_key])
            coefficient = sum(
                1 << i for i, witness in enumerate(paired) if len(vector & witness) % 2
            )
            entry["selected_class_coordinates"] = coefficient
            entry["quotient_class"] = coefficient >> record["good_rank"]
    assert_selected_identity(record)


@pytest.mark.parametrize("bounded,good_rank", [("Z", 15), ("X", 7)])
def test_nonidentity_basis_with_nonempty_opposite_boundaries(bounded, good_rank):
    code, coordinates, source, record = nonidentity_bell_fixture(bounded, good_rank)
    assert code["checks"]["X"] and code["checks"]["Z"]
    assert_selected_identity(record)
    assert len(set(record["selected_basis"]["detectors"][0]) & {126, 127}) == 2
    second = next(case for case in record["residues"] if case["suffix_pattern"] == 2)
    assert second["canonical_class"] == (1 << good_rank) ^ (1 << (good_rank + 1))
    assert second["selected_pairing_coordinates"] == 1 << (good_rank + 1)
    assert second["reference_support"] == list(range(7 * good_rank, 7 * good_rank + 14))
    report = validate_record(code, coordinates, record, source)
    assert report["all_requested_passed"]
    assert report["complete_residue_coverage"] == (bounded == "Z")


def test_consistent_basis_permutation_with_wrong_good_prefix_is_rejected():
    code, coordinates, _, record = nonidentity_bell_fixture()
    permute_selected_basis(record, 14, 15)
    # The complete paired basis is still independent and paired correctly, but
    # a weak suffix class has moved into the asserted good prefix.
    with pytest.raises(ValueError, match="Wrong good-family prefix/span"):
        validate_record(code, coordinates, record)


def test_consistent_suffix_permutation_requires_reference_basis_change():
    code, coordinates, _, record = nonidentity_bell_fixture()
    permute_selected_basis(record, 15, 16)
    record["annihilator"]["canonical_basis"] = [
        sum(
            1 << j
            for j, detector in enumerate(coordinates[record["detector_side"]])
            if len(set(witness["support"]) & set(detector)) % 2
        )
        for witness in record["selected_basis"]["paired_witnesses"][15:]
    ]
    # Coefficients, witnesses and annihilator now describe the permuted basis.
    # The old reference supports must not be accepted with the same bit labels.
    with pytest.raises(ValueError, match="Wrong physical reference support"):
        validate_record(code, coordinates, record)


@pytest.mark.parametrize("bounded,good_rank", [("Z", 15), ("X", 7)])
def test_canonical_class_and_identity_pairing_do_not_replace_opposite_cycle_check(
    bounded, good_rank
):
    code, coordinates, _, record = nonidentity_bell_fixture(bounded, good_rank)
    detector = set(record["selected_basis"]["detectors"][good_rank]) ^ {126}
    record["selected_basis"]["detectors"][good_rank] = sorted(detector)
    assert_selected_identity(record)
    canonical = sum(
        1 << j for j, witness in enumerate(coordinates[bounded]) if len(detector & set(witness)) % 2
    )
    assert canonical == record["selected_basis"]["classes"][good_rank]
    assert len(detector & set(code["checks"][bounded][-1])) % 2 == 1
    with pytest.raises(ValueError, match="Nonzero syndrome"):
        validate_record(code, coordinates, record)


@pytest.mark.parametrize("bounded,good_rank", [("Z", 15), ("X", 7)])
def test_canonical_pairing_alone_does_not_certify_boundary_annihilation(bounded, good_rank):
    code, coordinates, _, record = nonidentity_bell_fixture(bounded, good_rank)
    coordinates[bounded][0] = sorted(set(coordinates[bounded][0]) ^ {126})
    assert all(
        len(set(x) & set(z)) % 2 == (i == j)
        for i, x in enumerate(coordinates["X"])
        for j, z in enumerate(coordinates["Z"])
    )
    side = record["detector_side"]
    assert len(set(coordinates[bounded][0]) & set(code["checks"][side][-1])) % 2 == 1
    with pytest.raises(ValueError, match="Nonzero syndrome"):
        validate_record(code, coordinates, record)


def test_seven_residues_cover_nonzero_sums_and_pair_physically():
    code, coordinates, source, record = repetition_fixture()
    report = validate_record(code, coordinates, record, source)
    assert report["cases_checked"] == 7
    assert report["good_rank"] == 15 and report["annihilator_dimension"] == 3
    assert report["complete_residue_coverage"] and report["all_requested_passed"]
    assert [r["suffix_pattern"] for r in record["residues"]] == list(range(1, 8))
    assert len(record["pool"]) == 21
    assert all(r["quotient_class"] for r in record["pool"])


@pytest.mark.parametrize(
    "fault",
    [
        "sector",
        "dependent",
        "good_span",
        "missing_sum",
        "reference",
        "row_index",
        "row_mask",
        "physical_mask",
        "weight_bool",
        "weight_float",
        "cap",
        "quotient",
        "annihilator",
    ],
)
def test_reject_malformed_sector_certificate(fault):
    code, coordinates, source, original = repetition_fixture()
    record = copy.deepcopy(original)
    if fault == "sector":
        record["bounded_side"] = record["detector_side"]
    elif fault == "dependent":
        record["selected_basis"]["classes"][1] = record["selected_basis"]["classes"][0]
    elif fault == "good_span":
        record["good_families"][0]["class"] = 1 << 17
    elif fault == "missing_sum":
        record["residues"] = [r for r in record["residues"] if r["suffix_pattern"] != 3]
    elif fault == "reference":
        record["residues"][0]["reference_support"].pop()
    elif fault == "row_index":
        record["pool"][0]["provenances"][0]["rows"] = [108]
    elif fault == "row_mask":
        record["pool"][0]["provenances"][0]["row_mask"] = 1
    elif fault == "physical_mask":
        record["pool"][0]["mask"] ^= 1
    elif fault == "weight_bool":
        record["residues"][0]["weights"][0][1] = True
    elif fault == "weight_float":
        record["residues"][0]["weights"][0][1] = 1.0
    elif fault == "cap":
        record["residues"][0]["arithmetic"]["cap"] = 2
    elif fault == "quotient":
        record["pool"][0]["quotient_class"] = 0
    elif fault == "annihilator":
        record["annihilator"]["canonical_basis"][1] = record["annihilator"]["canonical_basis"][0]
    with pytest.raises(ValueError):
        validate_record(code, coordinates, record, source)


def test_direct_pairing_check_does_not_trust_class_tag():
    code, coordinates, _, record = repetition_fixture()
    case = record["residues"][0]
    index = case["weights"][0][0]
    # The cached canonical/quotient tags still report compatibility. The actual
    # physical vector now lives in a different repetition block and pairs zero.
    record["pool"][index]["support"] = [7 * 16]
    with pytest.raises(ValueError, match="Direct physical pairing"):
        check_case(code, coordinates, record, case)


def test_strict_equality_is_not_seven_and_partial_profile_is_retained():
    code, coordinates, source, record = repetition_fixture()
    case = record["residues"][0]
    case["weights"].pop()
    vectors = [record["pool"][i]["mask"] for i, _ in case["weights"]]
    case["arithmetic"] = exact_arithmetic(vectors, [w for _, w in case["weights"]], 126)
    assert case["arithmetic"]["totalWeight"] == 6 * case["arithmetic"]["cap"]
    with pytest.raises(ValueError, match="Strict inequality"):
        check_case(code, coordinates, record, case, require_seven=True)
    with pytest.raises(ValueError, match="aggregate threshold"):
        validate_record(code, coordinates, record, source)
    record["all_requested_passed"] = False
    report = validate_record(code, coordinates, record, source)
    assert not report["all_requested_passed"]
    assert report["results"][0]["bound"] == 6


def test_pool_must_preserve_all_original_provenances():
    code, coordinates, source, record = repetition_fixture()
    record["pool"][0]["provenances"][0]["source_rep_index"] = 1
    with pytest.raises(ValueError, match="lost original"):
        validate_record(code, coordinates, record, source)


def test_x_pilot_is_partial_and_capped_at_thirty_two():
    code, coordinates, source, record = repetition_fixture("X", 7)
    report = validate_record(code, coordinates, record, source)
    assert report["cases_checked"] == 32 and not report["complete_residue_coverage"]
    assert record["residue_scope"]["total_nonzero"] == 2047
    with pytest.raises(ValueError, match="not authorized"):
        build_problem(code, coordinates, source, "X", 2047)


def test_export_bytes_are_stable_and_timestamp_free():
    record = repetition_fixture()[3]
    first = gzip_bytes(record)
    assert first == gzip_bytes(record)
    assert gzip_bytes({"a": 1, "b": 2}) == gzip_bytes({"b": 2, "a": 1})
    assert json.loads(gzip.decompress(first)) == record
    assert first[4:8] == bytes(4)


def test_optional_lp_proposal_is_exactly_rechecked():
    pytest.importorskip("scipy")
    vectors = [1, 1, 1, 2, 4]
    weights, arithmetic, dual, details = choose_weights(vectors, 3, [("uniform", [1] * 5)], 1)
    assert details["solver"]["success"]
    assert Fraction(arithmetic["totalWeight"], arithmetic["cap"]) == 3
    assert arithmetic == exact_arithmetic(vectors, weights, 3)
    assert all(
        sum(dual["qubit_weights"][q] for q in range(3) if v >> q & 1) >= dual["denominator"]
        for v in vectors
    )
