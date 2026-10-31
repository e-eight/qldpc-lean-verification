#!/usr/bin/env bash
set -euo pipefail
: "${SLURM_JOB_ID:?Run in a detached bounded allocation}"
: "${SLURM_MEM_PER_NODE:?An enforced Slurm memory request is required}"
export LEAN_NUM_THREADS=1
HELPER_RECORD=$(cd -- "$(dirname -- "$0")" && pwd)
HELPER_ROOT=$(cd -- "$HELPER_RECORD/../../../../.." && pwd)
cd "$HELPER_ROOT"
"${SECTOR_PYTHON:-python3}" \
  data/sector-packing-evaluation/2026-10-31/lean-prototype/check-resources.py
sha256sum --check "$HELPER_RECORD/source-sha256.txt"
cd lean
lean --version
HELPER_OBJECT=.lake/build/lib/lean/QldpcVerification/SectorPackingCertificates.olean
AUDIT_OBJECT=.lake/build/lib/lean/SectorPackingHelperAudit.olean
for object in "$HELPER_OBJECT" "$AUDIT_OBJECT"; do
  if [[ -L "$object" ]]; then
    printf 'Refusing to replace a retained artifact link: %s\n' "$object" >&2
    exit 1
  fi
done
lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  -o "$HELPER_OBJECT" QldpcVerification/SectorPackingCertificates.lean
cd "$HELPER_ROOT"
lean -j1 -M7000 -DautoImplicit=false -DmaxSynthPendingDepth=3 \
  -o "lean/$AUDIT_OBJECT" \
  data/sector-packing-evaluation/2026-10-31/literal-z/helper/HelperAudit.lean
