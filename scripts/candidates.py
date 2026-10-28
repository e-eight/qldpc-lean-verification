"""Write data/packing_candidates.csv: uncertified codes where a packing
certificate is not ruled out by counting.

Any per-class packing certificate (CERTIFICATES.md) proves at most n/d_Z for
d_X and n/d_X for d_Z. Exactness therefore needs ratio = d_X*d_Z/n <= 1.
Ratios here use the claimed values, which are upper bounds, so the true ratio
can only be lower. Rows with ratio in (1, 1.3] are kept as near misses: they
can only get partial bounds.
"""
import collections
import csv
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402


def main():
    cert_map = common.certs()
    rows = []
    for f, d in common.codes():
        if common.certified_exact(cert_map.get(f)):
            continue
        n = d["n"]
        dx, dz = d["distance"]["X"]["value"], d["distance"]["Z"]["value"]
        ratio = dx * dz / n
        if ratio > 1.3:
            continue
        auth = d["provenance"].get("authors")
        rows.append(dict(
            file=f, name=d["name"][:70], n=n, k=d["k"], dX=dx, dZ=dz, d=min(dx, dz),
            w=common.max_check_weight(d), family=str(d.get("family")),
            layout=bool(d.get("locality")), origin=d["provenance"].get("origin"),
            authors=";".join(auth) if isinstance(auth, list) else str(auth),
            user_entry=common.mentions_user(d), ratio=round(ratio, 3),
            ceil_dX=round(n / dz, 1), ceil_dZ=round(n / dx, 1)))
    rows.sort(key=lambda r: (r["ratio"] > 1, -r["d"], r["n"]))
    os.makedirs(common.DATA, exist_ok=True)
    out = os.path.join(common.DATA, "packing_candidates.csv")
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)

    fit = [r for r in rows if r["ratio"] <= 1]
    near = [r for r in rows if r["ratio"] > 1]
    big = [r for r in fit if r["d"] >= 15]
    print(f"wrote {out}: {len(rows)} rows")
    print(f"in regime (ratio <= 1): {len(fit)}; with d >= 15: {len(big)} "
          f"({sum(not r['user_entry'] for r in big)} excluding the user's entries)")
    print(f"near misses (1 < ratio <= 1.3): {len(near)}; with d >= 15: {sum(r['d'] >= 15 for r in near)} "
          f"({sum(r['d'] >= 15 and not r['user_entry'] for r in near)} excluding the user's)")
    fam = collections.defaultdict(list)
    for r in big:
        if not r["user_entry"]:
            fam[r["family"]].append(r)
    print("in regime, d >= 15, excluding the user's entries, by family:")
    for name, rs in sorted(fam.items(), key=lambda kv: -len(kv[1])):
        print(f"  {name:22s} {len(rs):3d}  n {min(r['n'] for r in rs)}-{max(r['n'] for r in rs)}  "
              f"k {min(r['k'] for r in rs)}-{max(r['k'] for r in rs)}  "
              f"d {min(r['d'] for r in rs)}-{max(r['d'] for r in rs)}  "
              f"laid out {sum(r['layout'] for r in rs)}/{len(rs)}")


if __name__ == "__main__":
    main()
