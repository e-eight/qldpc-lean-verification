#!/usr/bin/env bash
#SBATCH --job-name=qldpc-kernel
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --time=02:00:00
#SBATCH --output=.local/cluster/logs/kernel-%j.log

set -euo pipefail
TASK_CONFIG="${QLDPC_CLUSTER_CONFIG:-${SLURM_SUBMIT_DIR:?}/.local/cluster.env}"
if [[ -f "$TASK_CONFIG" ]]; then source "$TASK_CONFIG"; fi
cd "${SLURM_SUBMIT_DIR:?}/archive/QldpcCert"
export PATH="$SLURM_SUBMIT_DIR/tools/lean/bin:$PATH"
if [[ -n ${QLDPC_CURL_CA_BUNDLE:-} ]]; then
  export CURL_CA_BUNDLE="$QLDPC_CURL_CA_BUNDLE"
fi
date -u
hostname
lean --version
sha256sum QldpcCert/*.lean lake-manifest.json lean-toolchain
# Fetch the dependencies pinned by the manifest, then their matching oleans.
if [[ ${QLDPC_FETCH_CACHE:-1} == 1 ]]; then
  lake exe cache get
fi
/usr/bin/time -v lake build QldpcCert.SparseRank QldpcCert.Surface225Data QldpcCert.Surface225Support
# Limit runaway kernel reduction, but allow substantially more than the default.
/usr/bin/time -v lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=0 \
  -Dprofiler=true -Dprofiler.threshold=1000 \
  -o .lake/build/lib/lean/QldpcCert/Surface225.olean QldpcCert/Surface225.lean
lake env lean QldpcCert/KernelAudit.lean
date -u
