"""Regressions for integer rounding and historical screening outputs."""

import csv
import json

import candidates
import common
import pytest


def test_seven_qubit_packing_passes_the_screen():
    # Seven weight-three representatives of one nontrivial CSS logical class.
    checks = (0b1010101, 0b1100110, 0b1111000)
    boundaries = {0}
    for row in checks:
        boundaries |= {x ^ row for x in tuple(boundaries)}
    cycles = [x for x in range(128) if all((x & row).bit_count() % 2 == 0 for row in checks)]
    logicals = [x for x in cycles if x not in boundaries]
    family = [x for x in logicals if x.bit_count() == 3]
    assert len(family) == 7
    assert all((x ^ family[0]) in boundaries for x in family)
    assert all((x & z).bit_count() % 2 == 1 for x in logicals for z in family)
    assert max(sum((x >> q) & 1 for x in family) for q in range(7)) == 3
    assert min(x.bit_count() for x in logicals) == 3
    assert candidates.target_screen(7, 3, 3)["passes_target_screen"]
    assert 3 * 3 > 7  # The discarded unrounded rule excluded this certificate.


@pytest.mark.parametrize(
    "n,dx,dz,passes_x,passes_z",
    [
        (6, 3, 3, False, False),
        (9, 4, 3, False, True),
        (10, 4, 3, True, True),
        (3, 2, 2, True, True),
    ],
)
def test_strict_and_asymmetric_thresholds(n, dx, dz, passes_x, passes_z):
    result = candidates.target_screen(n, dx, dz)
    assert result["passes_X_screen"] is passes_x
    assert result["passes_Z_screen"] is passes_z
    assert result["passes_target_screen"] is (passes_x and passes_z)


def test_thresholds_do_not_round_large_integers_to_float():
    result = candidates.target_screen(2**60 + 1, 2, 2**60)
    assert result["passes_X_screen"]
    assert not result["passes_Z_screen"]


def test_report_preserves_history_and_does_not_drop_ratio_near_misses(tmp_path, monkeypatch):
    repo = tmp_path / "challenge"
    (repo / "codes").mkdir(parents=True)
    (repo / "certs").mkdir()
    historical = tmp_path / "packing_candidates.csv"
    historical.write_text("historical snapshot\n")
    for name, n, target in [("possible", 3, 2), ("excluded", 6, 3), ("certified", 7, 3)]:
        # Screening reads reported targets; it does not validate these input matrices.
        doc = {
            "name": name,
            "code_type": "CSS",
            "n": n,
            "k": 1,
            "distance": {"X": {"value": target}, "Z": {"value": target}},
            "checks": {"X": [[0]], "Z": [[1]]},
            "provenance": {},
        }
        (repo / "codes" / f"{name}.json").write_text(json.dumps(doc))
    (repo / "codes/non-css.json").write_text(json.dumps({"code_type": "stabilizer"}))
    (repo / "certs/certified.json").write_text(json.dumps({"d_exact": 3}))
    monkeypatch.setattr(common, "REPO", str(repo))
    monkeypatch.setattr(common, "DATA", str(tmp_path))
    candidates.main([])
    assert historical.read_text() == "historical snapshot\n"
    output = tmp_path / "candidate-screening"
    with (output / "candidates.csv").open() as stream:
        rows = {row["file"]: row for row in csv.DictReader(stream)}
    assert set(rows) == {"possible.json", "excluded.json"}
    assert float(rows["possible.json"]["target_product_ratio"]) > 1.3
    assert rows["possible.json"]["passes_target_screen"] == "True"
    assert rows["excluded.json"]["passes_target_screen"] == "False"
    summary = json.loads((output / "summary.json").read_text())
    assert summary["counts"] == {
        "total_codes": 4,
        "skipped_non_css": 1,
        "skipped_certified_css": 1,
        "screened_css": 2,
        "passes_target_screen": 1,
        "excluded_target_pair": 1,
        "passes_with_target_min_at_least_15": 0,
    }
    assert summary["challenge_snapshot"]["input_files"] == 5


def test_empty_screen_still_writes_csv_headers(tmp_path, monkeypatch):
    monkeypatch.setattr(common, "REPO", str(tmp_path))
    monkeypatch.setattr(common, "codes", lambda: iter(()))
    monkeypatch.setattr(common, "certs", dict)
    candidates.main(["--output-dir", str(tmp_path / "empty")])
    with (tmp_path / "empty/candidates.csv").open() as stream:
        reader = csv.DictReader(stream)
        assert reader.fieldnames == list(candidates.FIELDS)
        assert list(reader) == []
