#!/bin/bash
#SBATCH --job-name=qldpc-verify
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --output=.local/cluster/logs/verify-%j.log
set -euo pipefail

# Submit from the remote project root. All compilation runs in this allocation.
TASK_ROOT="$SLURM_SUBMIT_DIR"
TASK_CONFIG="${QLDPC_CLUSTER_CONFIG:-$TASK_ROOT/.local/cluster.env}"
if [[ -f "$TASK_CONFIG" ]]; then source "$TASK_CONFIG"; fi
TASK_TOOLS="$TASK_ROOT/tools"
TASK_LEAN_VERSION=4.30.0-rc2
mkdir -p "$TASK_TOOLS"
if [[ ! -x "$TASK_TOOLS/lean-$TASK_LEAN_VERSION-linux/bin/lean" ]]; then
  curl -fL --retry 3 -o "$TASK_TOOLS/lean.tar.zst" \
    "https://github.com/leanprover/lean4/releases/download/v$TASK_LEAN_VERSION/lean-$TASK_LEAN_VERSION-linux.tar.zst"
  tar --use-compress-program="${QLDPC_ZSTD:-zstd}" \
    -xf "$TASK_TOOLS/lean.tar.zst" -C "$TASK_TOOLS"
fi
export PATH="$TASK_TOOLS/lean-$TASK_LEAN_VERSION-linux/bin:$PATH"
export LEAN_NUM_THREADS="${SLURM_CPUS_PER_TASK:-2}"
if [[ -n ${QLDPC_CURL_CA_BUNDLE:-} ]]; then
  export CURL_CA_BUNDLE="$QLDPC_CURL_CA_BUNDLE"
fi
export XDG_CACHE_HOME="$TASK_ROOT/.cache"
export MATHLIB_CACHE_DIR="$TASK_ROOT/.cache/mathlib"
cd "$TASK_ROOT/lean"
date -u
hostname
lean --version
if [[ "${QLDPC_FETCH_CACHE:-1}" == 1 ]]; then
  if [[ ! -f lake-manifest.json ]]; then lake update; fi
  lake exe cache get
fi
/usr/bin/time -v lake build "${QLDPC_TARGET:-QldpcVerification}"
if [[ "${QLDPC_AUDIT:-1}" == 1 ]]; then
  lake env lean QldpcVerification/KernelAudit.lean
fi
date -u
