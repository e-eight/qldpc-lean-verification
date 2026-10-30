"""Exercise command-line paths and optional accelerator selection."""

import os
import shutil
import subprocess
import sys
from pathlib import Path

import common
import gen_orbit_instance
import pytest

ROOT = Path(common.NOTES)
DATA_NAMESPACE = "QldpcVerification.Bicycle262Data"
DATA_MODULE = "QldpcVerification.Input.Bicycle262Data"


def test_search_prefers_local_accelerator(tmp_path):
    project = tmp_path / "project"
    scripts = project / "scripts"
    scripts.mkdir(parents=True)
    for name in ["class_search.py", "common.py"]:
        shutil.copyfile(ROOT / "scripts" / name, scripts / name)
    local = project / ".build/python"
    sibling = tmp_path / "qldpc-challenge"
    verify = sibling / "verify"
    audits = sibling / "research/audits"
    for directory in [local, verify, audits]:
        directory.mkdir(parents=True)
    (verify / "gf2.py").write_text("")
    (local / "gf2_fast.py").write_text("ORIGIN = 'local'\n")
    (verify / "gf2_fast.py").write_text("ORIGIN = 'sibling'\n")
    # Model the audit helper's transitive import, then stop before any search.
    (audits / "leader_audit.py").write_text(
        "import sys\n"
        "from pathlib import Path\n"
        "sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'verify'))\n"
        "import gf2_fast\n"
        "print(gf2_fast.ORIGIN)\n"
        "raise SystemExit(0)\n"
    )
    result = subprocess.run(
        [sys.executable, str(scripts / "class_search.py"), "unused"],
        env={**os.environ, "QLDPC_REPO": str(sibling)},
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert result.stdout.strip() == "local"


@pytest.fixture
def lean_project(tmp_path, monkeypatch):
    project = tmp_path / "project"
    (project / "lean/QldpcVerification/Input").mkdir(parents=True)
    monkeypatch.setattr(common, "NOTES", str(project))
    return project


@pytest.mark.parametrize("path_style", ["project_relative", "lean_relative", "absolute"])
def test_orbit_cli_module_path(lean_project, monkeypatch, path_style):
    output = lean_project / "lean/QldpcVerification/Input/Bicycle262Data.lean"
    checks = output.with_name("Bicycle262Checks.lean")
    cwd = lean_project / "lean" if path_style == "lean_relative" else lean_project
    monkeypatch.chdir(cwd)
    argument = output if path_style == "absolute" else output.relative_to(cwd)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "gen_orbit_instance.py",
            "262-2-15",
            DATA_NAMESPACE,
            str(argument),
            "--checks",
            str(checks),
        ],
    )
    gen_orbit_instance.main()
    assert (
        output.read_bytes()
        == (ROOT / "lean/QldpcVerification/Input/Bicycle262Data.lean").read_bytes()
    )
    assert (
        checks.read_bytes()
        == (ROOT / "lean/QldpcVerification/Input/Bicycle262Checks.lean").read_bytes()
    )


def test_orbit_cli_explicit_module_outside_package(lean_project, monkeypatch):
    output = lean_project / "ExportData.lean"
    checks = lean_project / "ExportChecks.lean"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "gen_orbit_instance.py",
            "262-2-15",
            DATA_NAMESPACE,
            str(output),
            "--checks",
            str(checks),
            "--data-module",
            DATA_MODULE,
        ],
    )
    gen_orbit_instance.main()
    assert checks.read_text() == gen_orbit_instance.generate_checks(DATA_MODULE, DATA_NAMESPACE)


def test_orbit_cli_rejects_unknown_module_before_writing(lean_project, monkeypatch, capsys):
    output = lean_project / "ExportData.lean"
    checks = lean_project / "ExportChecks.lean"
    monkeypatch.setattr(
        sys,
        "argv",
        ["gen_orbit_instance.py", "262-2-15", DATA_NAMESPACE, str(output), "--checks", str(checks)],
    )
    with pytest.raises(SystemExit) as error:
        gen_orbit_instance.main()
    assert error.value.code == 2
    assert "--data-module" in capsys.readouterr().err
    assert not output.exists()
    assert not checks.exists()
