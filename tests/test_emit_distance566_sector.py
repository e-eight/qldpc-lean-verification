"""Threshold-seven pruning, immutable provenance, and exact regeneration."""

import copy
import os
from pathlib import Path

import pytest
from distance566_sector_verify import load, source_inputs, validate_record
from emit_distance566_sector import (
    COORDINATES,
    NUMERICAL,
    NUMERICAL_HASH,
    ROOT,
    WEIGHTED,
    arithmetic,
    compact_record,
    emit,
    require_target,
    retained_indices,
)


@pytest.fixture(scope="module")
def literal():
    upstream = Path(os.environ.get("QLDPC_REPO", ROOT.parent / "qldpc-challenge"))
    code, coordinates, sources, _ = source_inputs(
        upstream,
        WEIGHTED / "focused-v1/certificates.json.gz",
        WEIGHTED / "analysis-v1/lean-ready.json.gz",
        COORDINATES,
    )
    original = load(NUMERICAL, NUMERICAL_HASH)
    report = validate_record(code, coordinates, original, sources["Z"])
    require_target(original, report)
    compact = compact_record(code, coordinates, original)
    return upstream, code, coordinates, original, compact


def test_pruning_retains_strict_seven_instead_of_six():
    vectors = [1 << q for q in range(8)]
    kept = retained_indices(vectors, [1] * 8, 8)
    assert kept == list(range(1, 8))
    result = arithmetic([vectors[i] for i in kept], [1] * len(kept), 8)
    assert result["bound"] == 7 and result["strict_seven"]
    with pytest.raises(ValueError, match="below seven"):
        retained_indices(vectors[:6], [1] * 6, 8)


@pytest.mark.parametrize("weight", [True, 1.5, 0, -1])
def test_pruning_rejects_invalid_positive_weights(weight):
    with pytest.raises(ValueError, match="positive packing"):
        retained_indices([1], [weight], 2)


@pytest.mark.parametrize("vector", [True, 0, -1, 1.5, 4])
def test_pruning_rejects_invalid_physical_masks(vector):
    with pytest.raises(ValueError, match="positive packing"):
        retained_indices([vector], [1], 2)


def test_numerical_source_hash_is_required(tmp_path):
    changed = tmp_path / "changed.json.gz"
    changed.write_bytes(NUMERICAL.read_bytes() + b"\n")
    with pytest.raises(ValueError, match="immutable input hash"):
        load(changed, NUMERICAL_HASH)


def test_compaction_preserves_pairing_bases_references_and_row_provenance(literal):
    _, code, coordinates, original, compact = literal
    assert compact["selected_basis"] == original["selected_basis"]
    assert compact["annihilator"] == original["annihilator"]
    assert compact["families"] == original["families"]
    for old, new in zip(original["good_families"], compact["good_families"], strict=True):
        by_source = {r["source_rep_index"]: r for r in old["representatives"]}
        assert all(by_source[r["source_rep_index"]] == r for r in new["representatives"])
    for entry in compact["pool"]:
        restored = dict(entry)
        old_index = restored.pop("original_pool_index")
        assert restored == original["pool"][old_index]
    for old, new in zip(original["residues"], compact["residues"], strict=True):
        for key in [
            "suffix_pattern",
            "reference_support",
            "canonical_class",
            "selected_pairing_coordinates",
        ]:
            assert old[key] == new[key]
        old_weights = dict(old["weights"])
        assert all(
            old_weights[compact["pool"][i]["original_pool_index"]] == w for i, w in new["weights"]
        )
    report = validate_record(code, coordinates, compact)
    assert report["complete_residue_coverage"] and report["all_requested_passed"]
    assert len(compact["pool"]) < len(original["pool"])


@pytest.mark.parametrize("fault", ["row", "reference", "missing_sum"])
def test_compaction_rejects_corrupted_input_before_rendering(literal, fault):
    _, code, coordinates, original, _ = literal
    changed = copy.deepcopy(original)
    if fault == "row":
        rep = changed["good_families"][0]["representatives"][0]
        rep["rows"], rep["row_mask"] = [274], 1 << 274
    elif fault == "reference":
        changed["residues"][0]["reference_support"].pop()
    else:
        changed["residues"] = [r for r in changed["residues"] if r["suffix_pattern"] != 3]
    with pytest.raises(ValueError):
        compact_record(code, coordinates, changed)


def test_partial_or_opposite_sector_is_not_a_literal_z_gate(literal):
    record = copy.deepcopy(literal[3])
    good = {"complete_residue_coverage": True, "all_requested_passed": True}
    record["bounded_side"], record["detector_side"] = "X", "Z"
    with pytest.raises(ValueError, match="complete, successful literal-Z"):
        require_target(record, good)
    with pytest.raises(ValueError, match="complete, successful literal-Z"):
        require_target(literal[3], good | {"complete_residue_coverage": False})


def test_exact_regeneration_rejects_line_endings_and_changed_compact_bytes(literal, tmp_path):
    upstream = literal[0]
    lean_root = tmp_path / "QldpcVerification"
    output = tmp_path / "compact.json.gz"
    _, modules = emit(upstream, NUMERICAL, lean_root, output)
    emit(upstream, NUMERICAL, lean_root, output, check=True)
    target = lean_root / modules[0]
    pristine = target.read_bytes()
    target.write_bytes(pristine.replace(b"\n", b"\r\n"))
    with pytest.raises(ValueError, match="Generated module differs"):
        emit(upstream, NUMERICAL, lean_root, output, check=True)
    target.write_bytes(pristine)
    output.write_bytes(output.read_bytes() + b"\n")
    with pytest.raises(ValueError, match="Compact sector certificate differs"):
        emit(upstream, NUMERICAL, lean_root, output, check=True)
