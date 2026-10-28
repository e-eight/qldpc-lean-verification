"""Print the code lists used in CHECKS_AND_RESULTS.md, one JSON path per line.

  topological  uncertified surface/toric codes with d >= 15 and dX*dZ <= n (17)
  smallk       uncertified codes with d >= 15, dX*dZ <= n, k <= 6, not topological,
               not the user's (16 two-block codes)
  control      solver-certified generalized-bicycle codes with k <= 6 and even n

Usage: python scripts/select_codes.py {topological|smallk|control}
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402


def main(which):
    cert_map = common.certs()
    for f, d in common.codes():
        exact = common.certified_exact(cert_map.get(f))
        dx, dz = d["distance"]["X"]["value"], d["distance"]["Z"]["value"]
        regime = dx * dz <= d["n"]
        big = d["distance"]["d"] >= 15
        fam = d.get("family")
        if which == "topological":
            pick = not exact and big and regime and fam == "topological"
        elif which == "smallk":
            pick = (not exact and big and regime and d["k"] <= 6 and fam != "topological"
                    and not common.mentions_user(d))
        elif which == "control":
            pick = exact and fam == "generalized-bicycle" and d["k"] <= 6 and d["n"] % 2 == 0
        else:
            sys.exit(__doc__)
        if pick:
            print(os.path.join(common.REPO, "codes", f))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "")
