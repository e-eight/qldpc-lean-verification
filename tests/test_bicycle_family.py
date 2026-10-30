"""Regenerate family proofs and reject malformed recognition certificates."""

import json
from pathlib import Path

import common
import gen_bicycle_family
import pytest

ROOT = Path(common.NOTES)
CASES = [
    (Path(common.code_file("262-2-15")), "Bicycle262Lattice", 20),
    (Path(common.code_file("362-2-19")), "Bicycle362", 19),
    (Path(common.code_file("562-2-23")), "Bicycle562Family", 101),
    (ROOT / "tests/fixtures/gb-8-2.json", "BicycleEvenStep16", 2),
    (ROOT / "tests/fixtures/gb-8-3.json", "BicycleEven16Family", 3),
]


@pytest.mark.parametrize("source,name,step", CASES)
def test_regenerate_family_inputs(source, name, step):
    data = gen_bicycle_family.load_instance(source)
    assert data["a"] == step
    for relative, text in gen_bicycle_family.generate(source, name).items():
        assert text == (ROOT / "lean/QldpcVerification" / relative).read_text()


@pytest.mark.parametrize("side", ["X", "Z"])
def test_reject_wrong_cyclic_row(tmp_path, side):
    code = json.loads((ROOT / "tests/fixtures/gb-8-2.json").read_text())
    code["checks"][side][1][0] = 4
    source = tmp_path / "wrong.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match="row 1"):
        gen_bicycle_family.generate(source, "WrongRow")


def test_reject_nonunit_first_difference(tmp_path):
    code = json.loads((ROOT / "tests/fixtures/gb-8-2.json").read_text())
    code["checks"]["X"][0] = [0, 2, 8, 9]
    source = tmp_path / "nonunit.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match="cyclic unit"):
        gen_bicycle_family.generate(source, "Nonunit")


def test_reject_stabilizer_as_logical_witness(tmp_path):
    code = json.loads((ROOT / "tests/fixtures/gb-8-3.json").read_text())
    code["distance"]["X"]["witness"] = code["checks"]["X"][0]
    source = tmp_path / "stabilizer.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match="zero certified logical coordinates"):
        gen_bicycle_family.generate(source, "Stabilizer")


def test_reject_malformed_witness(tmp_path):
    code = json.loads((ROOT / "tests/fixtures/gb-8-2.json").read_text())
    code["distance"]["Z"]["witness"] = [0, 0, 8]
    source = tmp_path / "duplicate.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match="Malformed Z witness"):
        gen_bicycle_family.generate(source, "DuplicateWitness")


@pytest.mark.parametrize("field", ["dimension", "distance"])
def test_reject_inconsistent_parameter_claim(tmp_path, field):
    code = json.loads((ROOT / "tests/fixtures/gb-8-2.json").read_text())
    if field == "dimension":
        code["k"] = 4
        message = "claimed k"
    else:
        code["distance"]["X"]["value"] = 4
        message = "differs from its witness weight"
    source = tmp_path / "wrong-claim.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match=message):
        gen_bicycle_family.generate(source, "WrongClaim")


def test_reject_bound_above_shortest_relation(tmp_path):
    code = json.loads((ROOT / "tests/fixtures/gb-8-2.json").read_text())
    code["distance"]["X"].update(witness=list(range(8, 16)), value=8)
    code["distance"]["Z"].update(witness=list(range(8)), value=8)
    code["distance"]["d"] = 8
    source = tmp_path / "loose-witnesses.json"
    source.write_text(json.dumps(code))
    with pytest.raises(ValueError, match="shorter than target 8"):
        gen_bicycle_family.generate(source, "UnreachableBound")
