"""Reproduce the data audit behind RECOMMENDATIONS.md. Reads files and git
history only; no distance searches.

Prints the board size and certified-exact count, the solvers behind the
certificates, the exact-distance envelope, recorded SAT solve times by
distance, the uncertified codes by distance, and whether any code named in a
correction commit ever had a certificate.
"""
import collections
import os
import re
import statistics
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402


def git(*args):
    return subprocess.run(["git", "-C", common.REPO, *args],
                          capture_output=True, text=True, check=True).stdout


def main():
    print("repo:", common.REPO, "| HEAD", git("log", "-1", "--format=%h %cs %s").strip())
    cert_map = common.certs()
    docs = dict(common.codes())
    exact = {f for f in docs if common.certified_exact(cert_map.get(f))}
    print(f"codes on board: {len(docs)}; certified exact (cert with d_exact for a current code): {len(exact)}")

    print(f"cert files: {len(cert_map)}; matching a current code: {len(set(cert_map) & set(docs))}")
    solvers = collections.Counter(c.get("solver") for c in cert_map.values() if common.certified_exact(c))
    for s, k in solvers.most_common():
        print(f"  {k:4d}  {s}")

    top = sorted(((docs[f]["distance"]["d"], docs[f]["n"], docs[f]["k"], f) for f in exact), reverse=True)
    print("highest certified distances (d, n, k, file):", top[:5])

    by_d = collections.defaultdict(list)
    for f in exact:
        c = cert_map[f]
        if "CryptoMiniSat" in str(c.get("solver")):
            by_d[docs[f]["distance"]["d"]].append(sum(float(s.get("secs") or 0) for s in c["sides"].values()))
    print("CryptoMiniSat solve time by d, both sides summed (median_high / max, seconds):")
    for dd in sorted(by_d):
        v = sorted(by_d[dd])
        print(f"  d={dd:2d}  count={len(v):3d}  median={statistics.median_high(v):8.1f}  max={v[-1]:8.1f}")

    bins = collections.Counter()
    for f, doc in docs.items():
        if f not in exact:
            dd = doc["distance"]["d"]
            bins["d<=10" if dd <= 10 else "d11-14" if dd <= 14 else "d15-20" if dd <= 20
                 else "d21-40" if dd <= 40 else "d>40"] += 1
    print(f"uncertified: {sum(bins.values())} by d: {dict(sorted(bins.items()))}")

    names = set()
    for line in git("log", "--format=%s").splitlines():
        if re.match(r"^(Correct|Tighten|Revise|Refute)", line):
            names.update(re.findall(r"\[\[(\d+),(\d+),(\d+)\]\]", line))
    had_cert = [n for n in names
                if git("log", "--all", "--format=%h", "--", f"certs/{'-'.join(n)}.json").strip()]
    print(f"codes named in correction commits: {len(names)}; ever had a cert file: {len(had_cert)} {had_cert}")


if __name__ == "__main__":
    main()
