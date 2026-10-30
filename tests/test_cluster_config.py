"""Exercise local Slurm configuration without contacting a scheduler."""

import json
import os
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SUBMIT = ROOT / "scripts/cluster/submit.sh"


@pytest.fixture
def scheduler(tmp_path, monkeypatch):
    executable = tmp_path / "sbatch"
    capture = tmp_path / "submission.json"
    executable.write_text(
        "#!/usr/bin/env python3\n"
        "import json, os, sys\n"
        "from pathlib import Path\n"
        "Path(os.environ['SBATCH_CAPTURE']).write_text(json.dumps({\n"
        "    'args': sys.argv[1:], 'cwd': os.getcwd(),\n"
        "    'config': os.environ['QLDPC_CLUSTER_CONFIG']}))\n"
    )
    executable.chmod(0o755)
    monkeypatch.setenv("PATH", f"{tmp_path}:{os.environ['PATH']}")
    monkeypatch.setenv("SBATCH_CAPTURE", str(capture))
    return capture


@pytest.mark.parametrize("archive", [False, True])
def test_submission_uses_local_config(tmp_path, monkeypatch, scheduler, archive):
    config = tmp_path / "cluster settings.env"
    config.write_text(
        "QLDPC_SLURM_ACCOUNT='test-account'\nQLDPC_SLURM_PARTITION='test-partition'\n"
    )
    monkeypatch.setenv("QLDPC_CLUSTER_CONFIG", config.name)
    args = ["bash", str(SUBMIT), *(["--archive"] if archive else []), "--mem=12G"]
    result = subprocess.run(args, cwd=tmp_path, capture_output=True, text=True, check=False)
    assert result.returncode == 0, result.stderr
    submission = json.loads(scheduler.read_text())
    expected = ROOT / (
        "archive/QldpcCert/kernel.sbatch" if archive else "scripts/cluster/verify.sbatch"
    )
    assert submission == {
        "args": [
            "--export=ALL",
            "--account=test-account",
            "--partition=test-partition",
            "--mem=12G",
            str(expected),
        ],
        "cwd": str(ROOT),
        "config": str(config),
    }


def test_missing_config_does_not_submit(tmp_path, monkeypatch, scheduler):
    monkeypatch.setenv("QLDPC_CLUSTER_CONFIG", str(tmp_path / "missing.env"))
    result = subprocess.run(["bash", str(SUBMIT)], capture_output=True, text=True, check=False)
    assert result.returncode == 2
    assert "Missing local cluster configuration" in result.stderr
    assert not scheduler.exists()


def test_empty_scheduler_settings_do_not_submit(tmp_path, monkeypatch, scheduler):
    config = tmp_path / "empty.env"
    config.write_text("QLDPC_SLURM_ACCOUNT=''\nQLDPC_SLURM_PARTITION=''\n")
    monkeypatch.setenv("QLDPC_CLUSTER_CONFIG", str(config))
    result = subprocess.run(["bash", str(SUBMIT)], capture_output=True, text=True, check=False)
    assert result.returncode == 2
    assert "QLDPC_SLURM_ACCOUNT and QLDPC_SLURM_PARTITION" in result.stderr
    assert not scheduler.exists()


@pytest.mark.parametrize("custom_bundle", [True, False])
def test_toolchain_download_uses_certificate_bundle(tmp_path, monkeypatch, custom_bundle):
    config = tmp_path / "cluster.env"
    bundle = tmp_path / "site certificates.pem"
    config.write_text(f"QLDPC_CURL_CA_BUNDLE='{bundle if custom_bundle else ''}'\n")
    capture = tmp_path / "curl.json"
    executable = tmp_path / "curl"
    executable.write_text(
        "#!/usr/bin/env python3\n"
        "import json, os\n"
        "from pathlib import Path\n"
        "Path(os.environ['CURL_CAPTURE']).write_text(\n"
        "    json.dumps(os.environ.get('CURL_CA_BUNDLE')))\n"
        "raise SystemExit(71)\n"
    )
    executable.chmod(0o755)
    monkeypatch.setenv("PATH", f"{tmp_path}:{os.environ['PATH']}")
    monkeypatch.setenv("SLURM_SUBMIT_DIR", str(tmp_path))
    monkeypatch.setenv("QLDPC_CLUSTER_CONFIG", str(config))
    monkeypatch.setenv("CURL_CAPTURE", str(capture))
    monkeypatch.setenv("CURL_CA_BUNDLE", "inherited.pem")
    result = subprocess.run(
        ["bash", str(ROOT / "scripts/cluster/verify.sbatch")],
        capture_output=True,
        text=True,
        timeout=10,
        check=False,
    )
    # The fake curl stops provisioning at the first download, without network access.
    assert result.returncode == 71, result.stderr
    assert json.loads(capture.read_text()) == (str(bundle) if custom_bundle else "inherited.pem")
