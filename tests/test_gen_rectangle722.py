"""Fixed-input recognition, malformed data rejection, and byte regeneration."""

import copy
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

import gen_rectangle722 as gen
import pytest

REPO = Path(os.environ.get("QLDPC_REPO", gen.ROOT.parent / "qldpc-challenge"))


@pytest.fixture(scope="module")
def raw():
    return (REPO / gen.SOURCE).read_bytes()


@pytest.fixture
def data(raw):
    return json.loads(raw)


def test_pinned_source(raw):
    assert hashlib.sha256(raw).hexdigest() == gen.SHA256
    result = subprocess.run(
        ["git", "-C", str(REPO), "show", f"{gen.REVISION}:{gen.SOURCE}"],
        check=True,
        capture_output=True,
    )
    assert result.stdout == raw


def test_regeneration(raw):
    outputs = gen.artifacts(raw)
    assert len(outputs) == 41
    for name, content in outputs.items():
        assert (gen.ROOT / name).read_bytes() == content.encode(), name
    generated = set((gen.ROOT / "lean/QldpcVerification/Input").glob("Rectangle722*.lean"))
    assert generated == {gen.ROOT / name for name in outputs if name.endswith(".lean")}


def test_cli_check(tmp_path):
    command = [
        sys.executable,
        str(gen.ROOT / "scripts/gen_rectangle722.py"),
        "--repo",
        str(REPO),
        "--output-root",
        str(tmp_path),
    ]
    subprocess.run(command, check=True, capture_output=True)
    subprocess.run([*command, "--check"], check=True, capture_output=True)
    target = tmp_path / "lean/QldpcVerification/Input/Rectangle722X00.lean"
    target.write_text(target.read_text() + "\n")
    result = subprocess.run([*command, "--check"], capture_output=True)
    assert result.returncode != 0
    assert b"regeneration mismatch" in result.stderr


def test_all_ordered_row_identities(data):
    assert gen.parse_input(json.dumps(data).encode()) == data
    for sector in ("X", "Z"):
        assert [gen.expected_row(sector, r) for r in range(357)] == data["checks"][sector]
    assert gen.expected_row("X", 0) == [0, 362, 363]
    assert gen.expected_row("X", 34) == [2, 19, 38, 361, 400, 401]
    assert gen.expected_row("Z", 0) == [38, 361, 380]
    assert {len(r) for r in data["checks"]["X"]} == {2, 3, 4, 6}


@pytest.mark.parametrize(
    "key,value",
    [
        ("schema_version", "0.2"),
        ("schema_version", 0.3),
        ("code_type", "non-CSS"),
        ("n", 721),
        ("n", 722.0),
        ("n", True),
        ("k", 9),
        ("k", 8.0),
        ("checks", None),
        ("checks", {"X": []}),
    ],
)
def test_schema_rejection(data, key, value):
    data[key] = value
    with pytest.raises(ValueError):
        gen.parse_input(json.dumps(data).encode())


@pytest.mark.parametrize(
    "replacement",
    [
        [],
        None,
        "0,362,363",
        [0, 362, 362],
        [362, 0, 363],
        [-1, 362, 363],
        [722, 362, 363],
        [False, 362, 363],
        [0.0, 362, 363],
        ["0", 362, 363],
        [0, 1, 2, 3, 4, 5, 6],
        [0, 361, 363],
    ],
)
@pytest.mark.parametrize("sector", ["X", "Z"])
def test_malformed_row(data, sector, replacement):
    data["checks"][sector][0] = replacement
    with pytest.raises(ValueError):
        gen.parse_input(json.dumps(data).encode())


@pytest.mark.parametrize("sector", ["X", "Z"])
def test_row_order_and_count(data, sector):
    swapped = copy.deepcopy(data)
    rows = swapped["checks"][sector]
    rows[0], rows[1] = rows[1], rows[0]
    with pytest.raises(ValueError, match="row identity"):
        gen.parse_input(json.dumps(swapped).encode())
    data["checks"][sector].pop()
    with pytest.raises(ValueError, match="357 rows"):
        gen.parse_input(json.dumps(data).encode())


@pytest.mark.parametrize("raw", [b"[]", b"null", b"{", b'{"n":722,"n":722}'])
def test_invalid_json(raw):
    with pytest.raises(ValueError):
        gen.parse_input(raw)


def test_changed_bytes_rejected(raw):
    with pytest.raises(ValueError, match="SHA256"):
        gen.artifacts(raw + b"\n")


def test_714_sparse_checks_and_no_search(raw):
    outputs = gen.artifacts(raw)
    chunks = [content for name, content in outputs.items() if name[-8:-5] in ("X00", "Z00")]
    assert chunks
    lean = "\n".join(content for name, content in outputs.items() if name.endswith(".lean"))
    assert lean.count("  decide\n") == 714
    assert "native_decide" not in lean
    assert "sorry" not in lean
    assert "maxHeartbeats 0" not in lean


def test_latex_appendix_rows(raw, data):
    outputs = gen.artifacts(raw)
    latex = outputs["analytical/rectangle722-submitted/INPUT.tex"]
    assert latex.startswith("\\documentclass") and latex.endswith("\\end{document}\n")
    rows = [line for line in latex.splitlines() if line.endswith(" \\\\") and "\\((" in line]
    assert len(rows) == 714
    expected = [
        f"  {r} & \\(({a + (-2 if s == 'X' else 2)}, {b})\\) & {', '.join(map(str, row))} \\\\"
        for s, width in (("X", 17), ("Z", 21))
        for r, row in enumerate(data["checks"][s])
        for a, b in [divmod(r, width)]
    ]
    assert rows == expected
    assert "$" not in latex and "\\[" not in latex
