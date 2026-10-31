#!/usr/bin/env bash
set -euo pipefail

if [[ -z ${SLURM_JOB_ID:-} || -z ${SLURM_MEM_PER_NODE:-${SLURM_MEM_PER_CPU:-}} ]]; then
  printf '%s\n' 'Run this replay inside a Slurm allocation with an enforced memory limit.' >&2
  exit 64
fi

INTEGRATION_RECORD="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
INTEGRATION_ROOT="$(cd -- "$INTEGRATION_RECORD/../../../.." && pwd)"
export LEAN_NUM_THREADS=1
cd "$INTEGRATION_ROOT"
sha256sum --check "$INTEGRATION_RECORD/source-sha256.txt"
cd lean
lake env lean --version

# Reuse the previously checked module artifacts, then rebuild the changed root.
lake env lean -o .lake/build/lib/lean/QldpcVerification.olean QldpcVerification.lean
for integration_audit in Distance566Audit Boundary566Audit QubitRemovalAudit \
  ComponentAudit JointAudit ConnectivityAudit BatchAudit FamilyAudit \
  WindingAudit BicycleAudit KernelAudit; do
  printf 'AUDIT %s\n' "$integration_audit"
  lake env lean "QldpcVerification/$integration_audit.lean"
done
