import json
import os
import sys
from pathlib import Path

if "PYTHONOPTIMIZE" in os.environ or sys.flags.optimize != 0:
    raise SystemExit("Resource preflight requires unset PYTHONOPTIMIZE and Python optimization0")
root = Path("/sys/fs/cgroup")
observed = {"memory.max": [], "memory.swap.max": []}
for line in Path("/proc/self/cgroup").read_text().splitlines():
    if not line.startswith("0::"):
        continue
    parent = root / line.split(":", 2)[2].lstrip("/")
    while parent == root or root in parent.parents:
        for field, values in observed.items():
            entry = parent / field
            if entry.is_file():
                value = entry.read_text().strip()
                if value.isdecimal():
                    values.append(int(value))
        if parent == root:
            break
        parent = parent.parent
caps = {field: min(values) if values else None for field, values in observed.items()}
if caps["memory.max"] is None or not 0 < caps["memory.max"] <= 8589934592:
    raise SystemExit("Resource preflight requires effective cgroup memory.max at most8GiB")
if caps["memory.swap.max"] != 0:
    raise SystemExit("Resource preflight requires effective cgroup memory.swap.max=0")
affinity = len(os.sched_getaffinity(0))
if affinity != 1:
    raise SystemExit("Resource preflight requires exactly one CPU of affinity")
for name in ["OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"]:
    if os.environ.get(name) != "1":
        raise SystemExit(f"Resource preflight requires {name}=1")
Path(sys.argv[1]).write_text(
    json.dumps(
        {
            "caps_bytes": caps,
            "cpu_affinity_count": affinity,
            "threads": 1,
            "PYTHONOPTIMIZE_present": False,
            "python_optimization_flag": sys.flags.optimize,
            "gate_implementation": "Explicit SystemExit failures; no assert-dependent gates",
        },
        indent=2,
    )
    + "\n"
)
