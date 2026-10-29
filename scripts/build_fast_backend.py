"""Build the optional sibling accelerator entirely inside this project's .build.

Run with: uv run --group search python scripts/build_fast_backend.py
The sibling verify/ directory is read only.
"""

import subprocess
import sys
from pathlib import Path

import common


def main():
    build = Path(common.NOTES) / ".build"
    build.mkdir(exist_ok=True)
    source = Path(common.REPO) / "verify" / "setup_gf2_fast.py"
    if not source.is_file():
        raise SystemExit(f"Missing accelerator source: {source}. Set QLDPC_REPO.")
    subprocess.run(
        [
            sys.executable,
            str(source),
            "build_ext",
            "--build-lib",
            str(build / "python"),
            "--build-temp",
            str(build / "temp"),
        ],
        cwd=build,
        check=True,
    )


if __name__ == "__main__":
    main()
