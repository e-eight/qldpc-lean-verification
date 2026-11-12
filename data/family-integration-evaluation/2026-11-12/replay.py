"""Replay the instance-to-family integration inside an already detached, resource-capped allocation.

This checks warm imports. It does not provision dependencies or launch Lean
without an allocation: use the bounded command in the adjacent README.
Raw compiler output stays under the ignored .local directory.
"""

import argparse
import hashlib
import json
import os
import resource
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
MODULES = [
    "Bicycle/NormalizedShortest",
    "NormalizedShortestAudit",
    "Audit/Dependencies",
    "Lattice/BasisSeparation",
    "BasisSeparationAudit",
    "Lattice/Bicycle4Arithmetic",
    "Lattice/Bicycle58Arithmetic",
    "Lattice/Bicycle82Arithmetic",
    "Lattice/Bicycle100Arithmetic",
    "Lattice/Bicycle110Arithmetic",
    "Lattice/Bicycle122Arithmetic",
    "Lattice/Bicycle170Arithmetic",
    "Lattice/Bicycle226Arithmetic",
    "Lattice/Bicycle262LatticeArithmetic",
    "Lattice/Bicycle278Arithmetic",
    "Lattice/Bicycle298Arithmetic",
    "Lattice/Bicycle346Arithmetic",
    "Lattice/Bicycle362Arithmetic",
    "Lattice/Bicycle422Arithmetic",
    "Lattice/Bicycle454Arithmetic",
    "Lattice/Bicycle562FamilyArithmetic",
    "Lattice/BicycleEven16FamilyArithmetic",
    "Lattice/BicycleEvenStep16Arithmetic",
    "Bicycle4",
    "Bicycle58",
    "Bicycle82",
    "Bicycle100",
    "Bicycle110",
    "Bicycle122",
    "Bicycle170",
    "Bicycle226",
    "Bicycle262Lattice",
    "Bicycle278",
    "Bicycle298",
    "Bicycle346",
    "Bicycle362",
    "Bicycle422",
    "Bicycle454",
    "Bicycle562Family",
    "BicycleEven16Family",
    "BicycleEvenStep16",
    "Bicycle262",
    "Bicycle562",
    "BatchAudit",
    "FamilyAudit",
    "BicycleAudit",
    "BicycleFamilyDependencyAudit",
    "Planar/Rectangle722Family",
    "Rectangle722",
    "Rectangle722Audit",
    "Rectangle722Seventeen",
    "Rectangle722Fifteen",
    "Rectangle722Distance",
    "Rectangle722Submitted",
    "Rectangle722SubmittedSeventeen",
    "Rectangle722Witness",
    "Rectangle722SubmittedBounds",
    "Rectangle722FamilyAudit",
    "Rectangle722FamilyDependencyAudit",
    "Rectangle722FifteenAudit",
    "Rectangle722DistanceAudit",
    "Rectangle722SeventeenAudit",
    "Rectangle722SubmittedAudit",
    "Rectangle722SubmittedSeventeenAudit",
    "Rectangle722SubmittedBoundsAudit",
    "FamilyTheory",
    "FamilyTheoryAudit",
    "FamilyIntegrationAudit",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record-dir", default=".local/family-integration-2026-11-12")
    parser.add_argument("--modules", nargs="+", choices=MODULES)
    args = parser.parse_args()
    records_dir = ROOT / args.record_dir
    records_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    toolchain = ROOT / ".tools/lean-4.30.0-rc2-linux/bin"
    if toolchain.is_dir():
        env["PATH"] = str(toolchain) + os.pathsep + env.get("PATH", "")
    records = []
    with (records_dir / "replay.log").open("w") as log:
        for module in args.modules or MODULES:
            relative = Path("QldpcVerification") / (module + ".lean")
            source = ROOT / "lean" / relative
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            output = ROOT / "lean/.lake/build/lib/lean" / relative.with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            log.write(f"Checking {relative}\n")
            log.flush()
            started = time.monotonic()
            result = subprocess.run(
                [
                    "lake",
                    "env",
                    "lean",
                    "-DautoImplicit=false",
                    "-DmaxSynthPendingDepth=3",
                    "-o",
                    str(output),
                    str(relative),
                ],
                cwd=ROOT / "lean",
                env=env,
                stdout=log,
                stderr=subprocess.STDOUT,
                check=False,
            )
            unchanged = hashlib.sha256(source.read_bytes()).hexdigest() == digest
            records.append(
                {
                    "module": module,
                    "source_sha256": digest,
                    "source_unchanged_during_check": unchanged,
                    "exit_code": result.returncode,
                    "elapsed_seconds": round(time.monotonic() - started, 3),
                    "children_peak_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                }
            )
            (records_dir / "replay.json").write_text(json.dumps(records, indent=2) + "\n")
            if result.returncode or not unchanged:
                (records_dir / "replay.exit").write_text("1\n")
                return 1
    (records_dir / "replay.exit").write_text("0\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
