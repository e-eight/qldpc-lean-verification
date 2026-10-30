# Local cluster configuration

Connection details, scheduler accounts, partitions, workspace paths, and raw logs belong under the ignored `.local/` directory.
The tracked scripts contain generic resource defaults and pinned proof toolchains.
They do not establish an SSH connection.

From the repository root, create the local configuration:

```bash
mkdir -p .local
cp scripts/cluster/config.example.env .local/cluster.env
chmod 600 .local/cluster.env
```

Set `QLDPC_SLURM_ACCOUNT` and `QLDPC_SLURM_PARTITION` in that file.
Fill in the optional SSH and workspace fields for local reference.
If the site needs a custom zstd executable or certificate bundle, set the corresponding optional fields.
`QLDPC_CURL_CA_BUNDLE` applies to the initial Lean toolchain download and later dependency downloads.
The file is trusted shell configuration, so use only configuration that you control.

On the submission host, place a private copy of the configuration at the same relative location in its workspace.
Submit from that workspace:

```bash
bash scripts/cluster/submit.sh --cpus-per-task=2 --mem=48G
```

For the archived proof, use:

```bash
bash scripts/cluster/submit.sh --archive --cpus-per-task=2 --mem=16G
```

`QLDPC_CLUSTER_CONFIG` can select another local configuration file.
The helper passes account and partition arguments to Slurm and creates `.local/cluster/logs/` before submission.
Both batch scripts write their raw logs there.
Normal `sbatch` options can override the resource defaults.

Published evaluation records retain proof-source hashes, outcomes, and resource measurements.
Their logs omit operational identifiers and use descriptive run labels instead of scheduler job IDs.
Exact records and the identifier mapping remain under `.local/cluster/records/` on this checkout.
