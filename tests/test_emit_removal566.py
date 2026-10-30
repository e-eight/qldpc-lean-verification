"""Regressions for the pinned sparse twelve-step removal certificate."""

import os
from copy import deepcopy
from pathlib import Path

import emit_removal566 as emitter
import pytest

UPSTREAM = Path(os.environ.get("QLDPC_REPO", emitter.ROOT.parent / "qldpc-challenge"))


def codes():
    return (
        emitter.read_code(UPSTREAM / "codes/578-18-20.json", 578),
        emitter.read_code(UPSTREAM / "codes/566-18-20.json", 566),
    )


def test_byte_for_byte_regeneration():
    generated = emitter.generate(UPSTREAM)
    assert len(generated) == 39
    for name, content in generated.items():
        assert (emitter.OUT / name).read_bytes() == content.encode(), name


def test_literal_endpoints_and_twelve_step_types():
    source, final = codes()
    stages, steps = emitter.reconstruct(source, final)
    assert stages[0] == source["checks"]
    assert stages[12] == final["checks"]
    assert [s["side"] for s in steps] == ["X"] * 6 + ["Z"] * 6
    assert [s["q"] for s in steps] == [272] * 6 + [558] * 6
    assert [len(s["fan"]) for s in steps] == [7] * 6 + [0] * 6
    assert all(not s["clear"] for s in steps[:6])
    assert all(578 - i - len(stage["X"]) - len(stage["Z"]) == 18 for i, stage in enumerate(stages))


def test_rejects_wrong_raw_hash(tmp_path):
    path = tmp_path / "578-18-20.json"
    path.write_text("{}\n")
    with pytest.raises(ValueError, match="pinned"):
        emitter.read_code(path, 578)


def test_rejects_malformed_row_after_hash_validation(tmp_path, monkeypatch):
    import hashlib
    import json

    source, _ = codes()
    source["checks"]["X"][0].append(578)
    raw = json.dumps(source).encode()
    path = tmp_path / "source.json"
    path.write_bytes(raw)
    monkeypatch.setitem(emitter.HASHES, 578, hashlib.sha256(raw).hexdigest())
    with pytest.raises(ValueError, match="Invalid sparse row"):
        emitter.read_code(path, 578)


def test_rejects_changed_final_matrix():
    source, final = codes()
    final = deepcopy(final)
    final["checks"]["X"][0] = [0]
    with pytest.raises(ValueError, match="literal final"):
        emitter.reconstruct(source, final)


def test_rejects_changed_layout():
    source, final = codes()
    final = deepcopy(final)
    final["locality"]["coordinates"][0] = [-100, -100]
    with pytest.raises(ValueError, match="layout"):
        emitter.reconstruct(source, final)


def test_rank_certificate_identity_and_dependence_rejection():
    rows = [[0, 2], [1, 2], [0, 1, 2]]
    ts, ps, columns = emitter.rank_certificate(rows)
    for i, mask in enumerate(ts):
        combined = 0
        for j, row in enumerate(rows):
            if mask >> j & 1:
                combined ^= sum(1 << q for q in row)
        assert [combined >> p & 1 for p in ps] == [int(i == j) for j in range(3)]
    assert columns == [[i for i, row in enumerate(rows) if p in row] for p in ps]
    with pytest.raises(ValueError, match="independent"):
        emitter.rank_certificate([[0], [0]])
