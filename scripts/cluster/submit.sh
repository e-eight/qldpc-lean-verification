#!/usr/bin/env bash
set -euo pipefail

TASK_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
TASK_SCRIPT="$TASK_ROOT/scripts/cluster/verify.sbatch"
if [[ ${1:-} == --help ]]; then
  printf '%s\n' 'Usage: scripts/cluster/submit.sh [--archive] [sbatch options...]' \
    'Run on the submission host. Configuration defaults to .local/cluster.env.'
  exit 0
fi
if [[ ${1:-} == --archive ]]; then
  TASK_SCRIPT="$TASK_ROOT/archive/QldpcCert/kernel.sbatch"
  shift
fi
TASK_CONFIG="${QLDPC_CLUSTER_CONFIG:-$TASK_ROOT/.local/cluster.env}"
if [[ ! -f "$TASK_CONFIG" ]]; then
  printf 'Missing local cluster configuration: %s\n' "$TASK_CONFIG" >&2
  printf '%s\n' 'Copy scripts/cluster/config.example.env to .local/cluster.env and fill it in.' >&2
  exit 2
fi
TASK_CONFIG="$(cd -- "$(dirname -- "$TASK_CONFIG")" && pwd)/$(basename -- "$TASK_CONFIG")"
# The local file is user-owned shell configuration, never a tracked credential file.
source "$TASK_CONFIG"
if [[ -z ${QLDPC_SLURM_ACCOUNT:-} || -z ${QLDPC_SLURM_PARTITION:-} ]]; then
  printf '%s\n' 'Set QLDPC_SLURM_ACCOUNT and QLDPC_SLURM_PARTITION in the local configuration.' >&2
  exit 2
fi
export QLDPC_CLUSTER_CONFIG="$TASK_CONFIG"
mkdir -p "$TASK_ROOT/.local/cluster/logs"
cd "$TASK_ROOT"
exec sbatch --export=ALL --account="$QLDPC_SLURM_ACCOUNT" \
  --partition="$QLDPC_SLURM_PARTITION" "$@" "$TASK_SCRIPT"
