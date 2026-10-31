"""Reject a replay outside the measured one-CPU, 8 GiB, zero-swap envelope."""

import os
from pathlib import Path

root = Path("/sys/fs/cgroup")
limits = {"memory.max": [], "memory.swap.max": []}
for line in Path("/proc/self/cgroup").read_text().splitlines():
    if line.startswith("0::"):
        current = root / line.split(":", 2)[2].lstrip("/")
        while current == root or root in current.parents:
            for field, values in limits.items():
                location = current / field
                if location.is_file():
                    value = location.read_text().strip()
                    if value.isdecimal():
                        values.append(int(value))
            if current == root:
                break
            current = current.parent

caps = {field: min(values) if values else None for field, values in limits.items()}
if caps["memory.max"] is None or caps["memory.max"] > 8_589_934_592:
    raise SystemExit("Replay requires an effective cgroup memory cap of at most 8 GiB")
if caps["memory.swap.max"] != 0:
    raise SystemExit("Replay requires an effective cgroup swap cap of zero")
if len(os.sched_getaffinity(0)) != 1:
    raise SystemExit("Replay requires CPU affinity restricted to one CPU")
print("ONE_CPU_8_GIB_ZERO_SWAP_VERIFIED")
