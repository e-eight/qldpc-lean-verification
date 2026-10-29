"""Shared helpers for the scripts in this directory.

The scripts read a qldpc-challenge checkout. They find it through the QLDPC_REPO
environment variable, or default to ../qldpc-challenge next to this directory.
Run them in this project's locked environment:

    uv run --locked python scripts/<script>.py ...
"""

import glob
import json
import os
import sys

import numpy as np

NOTES = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.abspath(os.environ.get("QLDPC_REPO", os.path.join(NOTES, "..", "qldpc-challenge")))
DATA = os.path.join(NOTES, "data")
sys.path.insert(0, os.path.join(REPO, "verify"))
# Optional accelerators built here take precedence over a sibling checkout's
# binary, which can target a different Python version.
sys.path.insert(0, os.path.join(NOTES, ".build", "python"))
import gf2  # noqa: E402,F401  (the checkout's own GF(2) helpers, re-exported)

USER_HANDLE = "e-eight"

# Group shapes of the non-cyclic two-block codes, from each entry's construction
# string (630-2-21 from its note). Other two-block codes default to cyclic (n/2,).
# Every use verifies the translations as automorphisms, so a wrong shape fails.
DIMS = {
    "672-2-24": (7, 4, 4, 3),
    "560-2-22": (2, 5, 7, 4),
    "700-2-25": (5, 7, 5, 2),
    "630-2-21": (3, 3, 5, 7),
}


def group_dims(slug, n):
    return DIMS.get(slug, (n // 2,))


def code_file(arg):
    """Accept a path or a slug like 362-2-19 and return the code's JSON path."""
    if os.path.exists(arg):
        return arg
    return os.path.join(REPO, "codes", arg if arg.endswith(".json") else arg + ".json")


def load(path):
    with open(path) as f:
        return json.load(f)


def matrix(rows, n):
    H = np.zeros((len(rows), n), dtype=np.int8)
    for i, r in enumerate(rows):
        H[i, r] = 1
    return H


def codes():
    """Yield (file name, document) for every board entry."""
    for p in sorted(glob.glob(os.path.join(REPO, "codes", "*.json"))):
        yield os.path.basename(p), load(p)


def certs():
    return {os.path.basename(p): load(p) for p in glob.glob(os.path.join(REPO, "certs", "*.json"))}


def certified_exact(cert):
    return bool(cert and cert.get("d_exact"))


def max_check_weight(doc):
    return max(len(r) for side in ("X", "Z") for r in doc["checks"][side])


def mentions_user(doc):
    """True when the user's handle appears in the provenance or a witness provenance."""
    return USER_HANDLE in json.dumps(doc["provenance"]) + json.dumps(doc["distance"])
