"""Screen reported CSS distance pairs with the rounded packing ceiling.

A family value V <= n/d_Z can prove target D_X only when (D_X-1)*D_Z < n,
if both reported targets are to be certified. The symmetric condition is also
necessary. Passing does not supply a certificate or validate either target.
All uncertified CSS entries are reported; the product ratio is diagnostic only.
Outputs are separate from the historical data/packing_candidates.csv.
"""

import argparse
import csv
import hashlib
import json
import os
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

FIELDS = (
    "file",
    "name",
    "n",
    "k",
    "dX",
    "dZ",
    "d",
    "w",
    "family",
    "layout",
    "origin",
    "authors",
    "user_entry",
    "target_product_ratio",
    "packing_ceiling_X",
    "packing_ceiling_Z",
    "passes_X_screen",
    "passes_Z_screen",
    "passes_target_screen",
)


def target_screen(n, dx, dz):
    """Necessary integer conditions for certifying both reported side distances."""
    if any(type(value) is not int or value <= 0 for value in (n, dx, dz)):
        raise ValueError("Qubit count and CSS distance targets must be positive integers.")
    passes_x = (dx - 1) * dz < n
    passes_z = (dz - 1) * dx < n
    return {
        "packing_ceiling_X": (n + dz - 1) // dz,
        "packing_ceiling_Z": (n + dx - 1) // dx,
        "passes_X_screen": passes_x,
        "passes_Z_screen": passes_z,
        "passes_target_screen": passes_x and passes_z,
    }


def snapshot_identity():
    """Identify the actual JSON inputs even when the checkout is not clean."""
    root = Path(common.REPO)
    hashes = {}
    for directory in ("codes", "certs"):
        for path in sorted((root / directory).glob("*.json")):
            hashes[path.relative_to(root).as_posix()] = hashlib.sha256(
                path.read_bytes()
            ).hexdigest()
    manifest = "".join(f"{sha}  {name}\n" for name, sha in hashes.items())
    try:
        commit = subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", "HEAD"], text=True, stderr=subprocess.DEVNULL
        ).strip()
        dirty = bool(
            subprocess.check_output(
                ["git", "-C", str(root), "status", "--porcelain"],
                text=True,
                stderr=subprocess.DEVNULL,
            )
        )
    except (OSError, subprocess.CalledProcessError):
        commit, dirty = None, None
    return {"commit": commit, "dirty": dirty, "input_files": len(hashes)}, manifest


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(common.DATA) / "candidate-screening",
        help="Report directory; historical data/packing_candidates.csv is never overwritten.",
    )
    args = parser.parse_args(argv)
    cert_map = common.certs()
    rows = []
    counts = {"total_codes": 0, "skipped_non_css": 0, "skipped_certified_css": 0}
    for filename, doc in common.codes():
        counts["total_codes"] += 1
        if doc.get("code_type") != "CSS":
            counts["skipped_non_css"] += 1
            continue
        if common.certified_exact(cert_map.get(filename)):
            counts["skipped_certified_css"] += 1
            continue
        n = doc["n"]
        dx, dz = doc["distance"]["X"]["value"], doc["distance"]["Z"]["value"]
        auth = doc["provenance"].get("authors")
        rows.append(
            {
                "file": filename,
                "name": doc["name"][:70],
                "n": n,
                "k": doc["k"],
                "dX": dx,
                "dZ": dz,
                "d": min(dx, dz),
                "w": common.max_check_weight(doc),
                "family": str(doc.get("family")),
                "layout": bool(doc.get("locality")),
                "origin": doc["provenance"].get("origin"),
                "authors": ";".join(auth) if isinstance(auth, list) else str(auth),
                "user_entry": common.mentions_user(doc),
                "target_product_ratio": round(dx * dz / n, 3),
                **target_screen(n, dx, dz),
            }
        )
    rows.sort(key=lambda row: (not row["passes_target_screen"], -row["d"], row["n"], row["file"]))
    counts["screened_css"] = len(rows)
    counts["passes_target_screen"] = sum(row["passes_target_screen"] for row in rows)
    counts["excluded_target_pair"] = len(rows) - counts["passes_target_screen"]
    counts["passes_with_target_min_at_least_15"] = sum(
        row["passes_target_screen"] and row["d"] >= 15 for row in rows
    )
    identity, manifest = snapshot_identity()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    report = args.output_dir / "candidates.csv"
    with report.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows)
    (args.output_dir / "input-sha256.txt").write_text(manifest)
    summary = {
        "generated_at_utc": datetime.now(UTC).isoformat(),
        "challenge_snapshot": identity,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "conditions": ["(D_X - 1)*D_Z < n", "(D_Z - 1)*D_X < n"],
        "scope": "Necessary conditions for certifying both reported targets; no distance proof.",
        "non_css": "Unsupported non-CSS entries are counted and skipped.",
        "ratio": "Diagnostic only; no ratio cutoff is applied.",
        "counts": counts,
        "output_sha256": {
            "candidates.csv": hashlib.sha256(report.read_bytes()).hexdigest(),
            "input-sha256.txt": hashlib.sha256(manifest.encode()).hexdigest(),
        },
    }
    (args.output_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Wrote {report}: {len(rows)} uncertified CSS target pairs")
    print(
        f"Not excluded: {counts['passes_target_screen']}; excluded: {counts['excluded_target_pair']}"
    )
    print(f"Skipped non-CSS: {counts['skipped_non_css']}")


if __name__ == "__main__":
    main()
