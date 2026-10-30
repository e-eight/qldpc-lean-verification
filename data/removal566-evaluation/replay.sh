#!/usr/bin/env bash
set -euo pipefail

# Run inside a detached allocation with enforced memory, swap, CPU and wall limits.
# Select one module or a small sequential group from proof-modules.txt per allocation.
REMOVAL_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REMOVAL_ROOT/lean"
export LEAN_NUM_THREADS=1

removal_compile() {
  local removal_module="$1"
  if [[ ! $removal_module =~ ^QldpcVerification(\.[A-Za-z0-9_]+)*$ ]]; then
    printf 'Invalid module: %s\n' "$removal_module" >&2
    exit 64
  fi
  local removal_path="${removal_module//./\/}"
  mkdir -p ".lake/build/lib/lean/$(dirname -- "$removal_path")"
  lake env lean -o ".lake/build/lib/lean/$removal_path.olean" "$removal_path.lean"
}

if [[ $# == 0 ]]; then
  printf '%s\n' 'Usage: replay.sh MODULE... | --audit' >&2
  exit 64
fi

if [[ $1 == --audit ]]; then
  lake env lean --version
  removal_compile QldpcVerification
  for removal_audit in Boundary566Audit QubitRemovalAudit ComponentAudit \
    JointAudit ConnectivityAudit BatchAudit FamilyAudit WindingAudit BicycleAudit KernelAudit; do
    lake env lean "QldpcVerification/$removal_audit.lean"
  done
else
  for removal_module in "$@"; do
    removal_compile "$removal_module"
  done
fi
