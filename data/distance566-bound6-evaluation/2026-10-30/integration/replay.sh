#!/usr/bin/env bash
set -euo pipefail

if [[ -z ${SLURM_JOB_ID:-} || -z ${SLURM_MEM_PER_NODE:-${SLURM_MEM_PER_CPU:-}} ]]; then
  printf '%s\n' 'Run inside a detached Slurm allocation with an enforced memory limit.' >&2
  exit 64
fi

BOUND6_RECORD="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
BOUND6_ROOT="$(cd -- "$BOUND6_RECORD/../../../.." && pwd)"
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
assert caps['memory.max'] is not None and caps['memory.max'] <= 8589934592
assert caps['memory.swap.max'] == 0
assert len(os.sched_getaffinity(0)) == 1
PY
cd "$BOUND6_ROOT"
sha256sum --check "$BOUND6_RECORD/source-sha256.txt"
cd lean
lake env lean --version
lake env lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  -o .lake/build/lib/lean/QldpcVerification.olean QldpcVerification.lean
for bound6_audit in Distance566WeightedAudit Distance566Audit Boundary566Audit \
  QubitRemovalAudit ComponentAudit JointAudit ConnectivityAudit BatchAudit \
  FamilyAudit WindingAudit BicycleAudit KernelAudit; do
  printf 'AUDIT %s\n' "$bound6_audit"
  lake env lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
    "QldpcVerification/$bound6_audit.lean"
done
