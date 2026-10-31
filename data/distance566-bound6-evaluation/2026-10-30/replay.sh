#!/usr/bin/env bash
set -euo pipefail
if [[ -z ${SLURM_JOB_ID:-} || -z ${SLURM_MEM_PER_NODE:-${SLURM_MEM_PER_CPU:-}} ]]; then
  printf '%s\n' 'Run inside a detached Slurm allocation with enforced memory and swap limits.' >&2
  exit 64
fi
BOUND_RECORD="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
BOUND_ROOT="$(cd -- "$BOUND_RECORD/../../.." && pwd)"
export LEAN_NUM_THREADS=1
bound_start=${1:-0}
bound_count=${2:-84}
if [[ ! $bound_start =~ ^[0-9]+$ || ! $bound_count =~ ^[0-9]+$ ]]; then
  printf '%s\n' 'Optional arguments are the zero-based module start and module count.' >&2
  exit 64
fi
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
cd "$BOUND_ROOT"
sha256sum --check "$BOUND_RECORD/source-sha256.txt"
cd lean
lake env lean --version
mapfile -t bound_modules <"$BOUND_RECORD/proof-modules.txt"
for bound_module in "${bound_modules[@]:bound_start:bound_count}"; do
  bound_path="${bound_module//./\/}"
  mkdir -p ".lake/build/lib/lean/$(dirname -- "$bound_path")"
  lake env lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
    -o ".lake/build/lib/lean/$bound_path.olean" "$bound_path.lean"
done
