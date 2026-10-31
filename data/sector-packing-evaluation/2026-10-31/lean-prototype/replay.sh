#!/usr/bin/env bash
set -euo pipefail
: "${SLURM_JOB_ID:?Run in a detached bounded allocation}"
: "${SLURM_MEM_PER_NODE:?An enforced Slurm memory request is required}"
export LEAN_NUM_THREADS=1
SECTOR_RECORD=$(cd -- "$(dirname -- "$0")" && pwd)
SECTOR_ROOT=$(cd -- "$SECTOR_RECORD/../../../.." && pwd)
"${SECTOR_PYTHON:-python3}" "$SECTOR_RECORD/check-resources.py"
cd "$SECTOR_ROOT"
sha256sum --check "$SECTOR_RECORD/source-sha256.txt"
cd lean
lean --version
for module in SectorPacking SectorPackingExamples SectorPackingAudit; do
  printf 'COMPILE %s\n' "$module"
  output=".lake/build/lib/lean/QldpcVerification/$module.olean"
  if [[ -L "$output" ]]; then
    printf 'Refusing to replace a retained artifact link: %s\n' "$output" >&2
    exit 1
  fi
  lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
    -o "$output" "QldpcVerification/$module.lean"
done
