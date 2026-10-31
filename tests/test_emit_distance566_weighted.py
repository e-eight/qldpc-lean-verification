"""Pruning, provenance, rejection, and byte regeneration for the additive proof."""

import copy
import os
from pathlib import Path

import pytest
from emit_distance566_weighted import (
    COORDINATE_HASH,
    COORDINATES,
    INPUT,
    INPUT_HASH,
    ROOT,
    compact_record,
    emit,
    family_modules,
    load_pinned,
    prune_family,
    target_entries,
    validate_targets,
)
from emit_removal566 import read_code


@pytest.fixture(scope="module")
def literal():
    upstream = Path(os.environ.get("QLDPC_REPO", ROOT.parent / "qldpc-challenge"))
    if not (upstream / "codes/566-18-20.json").is_file():
        pytest.skip("Pinned upstream literal input is not staged")
    return (
        upstream,
        read_code(upstream / "codes/566-18-20.json", 566),
        load_pinned(COORDINATES, COORDINATE_HASH)["coordinates"]["566"],
        load_pinned(INPUT, INPUT_HASH),
    )


def small_family():
    return {
        "representatives": [
            {"support": [i], "rows": [i], "weight": weight}
            for i, weight in enumerate([10] * 6 + [1])
        ],
        "restricted_dual": {"scope": "finite list"},
    }


def test_pruning_keeps_strict_boundary_and_actual_row_witnesses():
    original = small_family()
    snapshot = copy.deepcopy(original)
    compact = prune_family(original, 7)
    assert original == snapshot
    assert compact["representatives"] == original["representatives"][:6]
    assert compact["arithmetic"] == {"totalWeight": 60, "cap": 10, "bound": 6}
    assert compact["pruning"]["strict_surplus_at_six"] == 10


def test_pruning_rejects_equality_at_the_threshold():
    family = small_family()
    family["representatives"] = family["representatives"][:5]
    with pytest.raises(ValueError, match="below threshold six"):
        prune_family(family, 7)


def test_pinned_input_hash_is_required(tmp_path):
    changed = tmp_path / "changed.json.gz"
    changed.write_bytes(INPUT.read_bytes() + b" ")
    with pytest.raises(ValueError, match="immutable input hash"):
        load_pinned(changed, INPUT_HASH)


@pytest.mark.parametrize("fault", ["row", "row_range", "weight", "pairing", "sector"])
def test_export_rejects_corrupted_literal_certificates(literal, fault):
    _, code, coordinates, original = literal
    record = copy.deepcopy(original)
    target = target_entries(record)[0]
    rep = target["families"][0]["representatives"][0]
    if fault == "row":
        rep["rows"] = [] if rep["rows"] else [0]
    elif fault == "row_range":
        rep["rows"] = [274]
    elif fault == "weight":
        rep["weight"] = True
    elif fault == "pairing":
        target["coverage"]["paired_witnesses"][0]["support"] = []
    else:
        target["bounded_side"] = target["detector_side"]
    with pytest.raises(ValueError):
        validate_targets(code, coordinates, record)


def test_target_selection_rejects_duplicate_sectors(literal):
    record = copy.deepcopy(literal[3])
    record["results"].append(copy.deepcopy(target_entries(record)[0]))
    with pytest.raises(ValueError, match="exactly two target"):
        target_entries(record)


def test_compaction_preserves_both_independent_bases_and_memberships(literal):
    _, code, coordinates, record = literal
    result = compact_record(code, coordinates, record)
    assert {entry["n"] for entry in result["results"]} == {566}
    before = {e["detector_side"]: e for e in target_entries(record)}
    for entry in result["results"]:
        assert entry["coverage"] == before[entry["detector_side"]]["coverage"]
        assert all(f["pruning"]["strict_surplus_at_six"] > 0 for f in entry["families"])
    assert sum(len(f["representatives"]) for e in result["results"] for f in e["families"]) < 2892


def test_emission_uses_checked_raw_indices_and_bounded_blocks():
    family = small_family()
    family["arithmetic"] = {"cap": 10}
    modules = family_modules("X", 0, family)
    data = modules["Input/Distance566Weighted/X0Data.lean"]
    checks = modules["Input/Distance566Weighted/X0Checks.lean"]
    assert "List RawRep" in data and ".map decode" in data
    assert "rangeCheck 566 274 raw0" in checks
    assert "packedClassCheck RowData.xMask" in checks
    assert "capChunkCheck" in checks and "threshold" in checks
    # Only the family-coordinate index has a per-index Fin proof.
    assert data.count("by decide") == 1


def test_exact_byte_regeneration_and_tamper_rejection(literal, tmp_path):
    upstream = literal[0]
    root, compact = tmp_path / "lean", tmp_path / "compact.json.gz"
    _, modules = emit(upstream, INPUT, COORDINATES, root, compact)
    assert len(modules) == 79
    emit(upstream, INPUT, COORDINATES, root, compact, check=True)
    target = root / "Input/Distance566Weighted/X0Data.lean"
    original = target.read_bytes()
    target.write_bytes(original.replace(b"\n", b"\r\n"))
    with pytest.raises(ValueError, match="Generated module differs"):
        emit(upstream, INPUT, COORDINATES, root, compact, check=True)
    target.write_bytes(original + b"\n")
    with pytest.raises(ValueError, match="Generated module differs"):
        emit(upstream, INPUT, COORDINATES, root, compact, check=True)
