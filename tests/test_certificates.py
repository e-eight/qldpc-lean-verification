"""Regression controls for certificate data and exact class arithmetic."""

import hashlib
import json
from fractions import Fraction
from pathlib import Path

import common
import gen_bicycle_lattice
import gen_lean_instance
import gen_orbit_instance
import gen_qeclean_surface
import numpy as np
import pytest
from class_search import certificate, class_value

ROOT = Path(common.NOTES)
SOURCE = Path(common.code_file("225-1-15"))
SOURCE_SHA256 = "7a180b0f143d672013952e2f24fa12664e20fe7b03f993994076194e4b28bebe"


def test_regenerate_audited_input(tmp_path):
    """Changes to dependencies must preserve the already audited finite input."""
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA256
    data, support = tmp_path / "Data.lean", tmp_path / "Support.lean"
    gen_lean_instance.main("225-1-15", "Surface225", data, support)
    for generated, name in [(data, "Surface225Data"), (support, "Surface225Support")]:
        assert (
            generated.read_bytes()
            == (ROOT / f"archive/QldpcCert/QldpcCert/{name}.lean").read_bytes()
        )
    assert (
        gen_qeclean_surface.generate(SOURCE)
        == (ROOT / "lean/QldpcVerification/Input/Surface225Labels.lean").read_text()
    )
    assert (
        gen_qeclean_surface.generate_supports(SOURCE)
        == (ROOT / "lean/QldpcVerification/Input/Surface225Support.lean").read_text()
    )


@pytest.mark.parametrize(
    "row,side",
    [([0, 1, 15], "X"), ([0, 0], "Z"), ([-1, 0], "Z"), ([224, 225], "X")],
)
def test_reject_malformed_support(row, side):
    with pytest.raises(ValueError):
        gen_qeclean_surface.face_label(row, side)


def test_reject_wrong_family(tmp_path):
    code = json.loads(SOURCE.read_bytes())
    code["n"] = 224
    source = tmp_path / "wrong.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match="225 qubits"):
        gen_qeclean_surface.generate(source)


def test_weighted_mixture_and_ceiling():
    value, used = class_value([(4, 10), (10, 4)], 281)
    assert value == Fraction(281, 7)
    assert set(used) == {(4, 10), (10, 4)}
    bound, _ = certificate({1: [(8, 8)], 2: [(8, 8)], 3: [(8, 8)]}, 113)
    assert bound == 15  # ceil(113/8), not floor(113/8).


def test_one_logical_class_does_not_certify_k2():
    assert certificate({1: [(1, 1)]}, 100)[0] == 0


def test_k2_uses_median_class_value():
    bound, _ = certificate({1: [(10, 10)], 2: [(5, 5)], 3: [(1, 1)]}, 100)
    assert bound == 20


def test_regenerate_weighted_orbit_certificate():
    text, data = gen_orbit_instance.generate("262-2-15", "QldpcVerification.Bicycle262Data")
    assert data["values"] == ["655/43", "131/9"]
    assert data["caps"] == [258, 9]
    assert text == (ROOT / "lean/QldpcVerification/Input/Bicycle262Data.lean").read_text()
    assert (
        gen_orbit_instance.generate_checks(
            "QldpcVerification.Input.Bicycle262Data", "QldpcVerification.Bicycle262Data"
        )
        == (ROOT / "lean/QldpcVerification/Input/Bicycle262Checks.lean").read_text()
    )


def test_dependent_detectors_have_no_paired_witness():
    a = np.array([[1, 1, 0], [1, 1, 0]], dtype=np.int8)
    with pytest.raises(ValueError, match="dual logical witnesses"):
        gen_orbit_instance.solve(a, np.array([1, 0], dtype=np.int8))


@pytest.mark.parametrize("size", [23, 31])
def test_regenerate_additional_surface(size):
    n = size * size
    source = Path(common.code_file(f"{n}-1-{size}"))
    directory = ROOT / "lean/QldpcVerification"
    for suffix, generated in [
        ("Labels", gen_qeclean_surface.generate(source, size)),
        ("Support", gen_qeclean_surface.generate_supports(source, size)),
        ("Lookup", gen_qeclean_surface.generate_lookup(source, size)),
        ("Match", gen_qeclean_surface.generate_match(size)),
    ]:
        assert generated == (directory / f"Input/Surface{n}{suffix}.lean").read_text()
    assert (
        gen_qeclean_surface.generate_instance(size) == (directory / f"Surface{n}.lean").read_text()
    )


def test_regenerate_bicycle_lattice_input():
    directory = ROOT / "lean/QldpcVerification/Input"
    assert (
        gen_bicycle_lattice.generate(Path(common.code_file("562-2-23")))
        == (directory / "Bicycle562Data.lean").read_text()
    )
    assert (
        gen_bicycle_lattice.generate_checks() == (directory / "Bicycle562Checks.lean").read_text()
    )


def test_reject_wrong_bicycle_row(tmp_path):
    code = common.load(common.code_file("562-2-23"))
    code["checks"]["X"][0][0] += 1
    source = tmp_path / "corrupted.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match="Unexpected X row 0"):
        gen_bicycle_lattice.generate(source)
