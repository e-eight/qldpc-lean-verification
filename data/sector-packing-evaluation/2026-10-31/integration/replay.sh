#!/usr/bin/env bash
set -euo pipefail

if [[ -z ${SLURM_JOB_ID:-} || -z ${SLURM_MEM_PER_NODE:-${SLURM_MEM_PER_CPU:-}} ]]; then
  printf '%s\n' 'Run inside a detached Slurm allocation with an enforced memory limit.' >&2
  exit 64
fi

SECTOR_RECORD="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
SECTOR_ROOT="$(cd -- "$SECTOR_RECORD/../../../.." && pwd)"
export LEAN_NUM_THREADS=1
python3 - <<'PY'
import os
from pathlib import Path

root = Path('/sys/fs/cgroup')
limits = {'memory.max': [], 'memory.swap.max': []}
for line in Path('/proc/self/cgroup').read_text().splitlines():
    if line.startswith('0::'):
        path = root / line.split(':', 2)[2].lstrip('/')
        while path == root or root in path.parents:
            for field, values in limits.items():
                file = path / field
                if file.is_file() and file.read_text().strip().isdecimal():
                    values.append(int(file.read_text().strip()))
            if path == root:
                break
            path = path.parent
caps = {field: min(values) if values else None for field, values in limits.items()}
if caps['memory.max'] is None or caps['memory.max'] > 8589934592:
    raise SystemExit('An effective memory ceiling of at most 8 GiB is required.')
if caps['memory.swap.max'] != 0:
    raise SystemExit('The effective swap ceiling must be zero.')
if len(os.sched_getaffinity(0)) != 1:
    raise SystemExit('Exactly one CPU of affinity is required.')
PY
cd "$SECTOR_ROOT"
sha256sum --check "$SECTOR_RECORD/source-sha256.txt"
cd lean
python3 - <<'PY'
from pathlib import Path

output = Path('.lake/build/lib/lean/QldpcVerification.olean')
for path in [output, *output.parents]:
    if path.is_symlink():
        raise SystemExit(f'Refusing a linked output or parent: {path}')
if not output.parent.is_dir():
    raise SystemExit('Prepare a real owned build directory before replay.')
if output.exists() and not output.is_file():
    raise SystemExit('The root artifact destination must be a regular file.')
PY
lake env lean --version
lake env lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  -o .lake/build/lib/lean/QldpcVerification.olean QldpcVerification.lean
for sector_audit in Distance566SectorAudit SectorPackingAudit Distance566WeightedAudit \
  Distance566Audit Boundary566Audit \
  QubitRemovalAudit ComponentAudit JointAudit ConnectivityAudit BatchAudit \
  FamilyAudit WindingAudit BicycleAudit KernelAudit; do
  printf 'AUDIT %s\n' "$sector_audit"
  lake env lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
    "QldpcVerification/$sector_audit.lean"
done
printf '%s\n' 'AUDIT SectorPackingHelperAudit (standalone finite controls)'
lake env lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  ../data/sector-packing-evaluation/2026-10-31/literal-z/helper/HelperAudit.lean
cd "$SECTOR_ROOT"
sha256sum --check "$SECTOR_RECORD/source-sha256.txt"
