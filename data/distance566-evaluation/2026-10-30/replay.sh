#!/usr/bin/env bash
set -euo pipefail
if [[ -z ${SLURM_JOB_ID:-} || -z ${SLURM_MEM_PER_NODE:-${SLURM_MEM_PER_CPU:-}} ]]; then
  printf '%s\n' 'Run this replay inside a Slurm allocation with an enforced memory limit.' >&2
  exit 64
fi
DISTANCE_RECORD="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
DISTANCE_ROOT="$(cd -- "$DISTANCE_RECORD/../../.." && pwd)"
export LEAN_NUM_THREADS=1
cd "$DISTANCE_ROOT/lean"
lake env lean --version
while read -r distance_module; do
  distance_path="${distance_module//./\/}"
  mkdir -p ".lake/build/lib/lean/$(dirname -- "$distance_path")"
  lake env lean -o ".lake/build/lib/lean/$distance_path.olean" "$distance_path.lean"
done <"$DISTANCE_RECORD/proof-modules.txt"
