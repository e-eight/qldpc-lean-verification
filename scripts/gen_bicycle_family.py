"""Emit sparse recognition and exact-distance proofs using the normalized bicycle family.

The first binomial difference must be a unit modulo the cyclic length.
Lean checks all emitted row supports, witnesses, and lattice exclusions.
No numerical rank certificate or per-instance coverage certificate is emitted.
"""

import argparse
import hashlib
import json
import math
import re
from pathlib import Path


def mask(support):
    return sum(1 << q for q in support)


def load_instance(source):
    raw = source.read_bytes()
    code = json.loads(raw)
    n = code["n"]
    if code["code_type"] != "CSS" or not isinstance(n, int) or n < 4 or n % 2:
        raise ValueError("Expected a two-block CSS code of even length at least four.")
    if code["k"] != 2:
        raise ValueError("The connected unit-step family requires a claimed k of two.")
    m = n // 2
    rows = code["checks"]
    for side in ("X", "Z"):
        if len(rows[side]) != m:
            raise ValueError(f"Expected {m} {side} rows in cyclic order.")
        for i, row in enumerate(rows[side]):
            if (
                len(row) != 4
                or len(set(row)) != 4
                or any(type(q) is not int or not 0 <= q < n for q in row)
            ):
                raise ValueError(f"Malformed {side} row {i}.")
    first = rows["X"][0]
    h = sorted(q for q in first if q < m)
    v = sorted(q - m for q in first if q >= m)
    if len(h) != 2 or len(v) != 2:
        raise ValueError("Each X row must have two entries in each cyclic block.")
    step = (h[1] - h[0]) % m
    if math.gcd(step, m) != 1:
        raise ValueError("The first binomial difference must be a cyclic unit.")
    inverse = pow(step, -1, m)
    a = (v[1] - v[0]) * inverse % m
    r, s = h[1], v[1]
    for i in range(m):
        expected_x = {
            (i + r) % m,
            (i + r - step) % m,
            m + (i + s) % m,
            m + (i + s - step * a) % m,
        }
        expected_z = {
            (i - s) % m,
            (i - s + step * a) % m,
            m + (i - r) % m,
            m + (i - r + step) % m,
        }
        for side, expected in [("X", expected_x), ("Z", expected_z)]:
            if set(rows[side][i]) != expected:
                raise ValueError(f"Unexpected {side} row {i}; expected cyclic binomial order.")
    witnesses = {}
    detectors = {}
    for side, opposite in [("X", "Z"), ("Z", "X")]:
        support = code["distance"][side]["witness"]
        if (
            not support
            or len(set(support)) != len(support)
            or any(type(q) is not int or not 0 <= q < n for q in support)
        ):
            raise ValueError(f"Malformed {side} witness.")
        if code["distance"][side]["value"] != len(support):
            raise ValueError(f"The claimed {side} distance differs from its witness weight.")
        w = mask(support)
        if any((mask(row) & w).bit_count() % 2 for row in rows[opposite]):
            raise ValueError(f"The {side} witness has nonzero syndrome.")
        candidates = [[], []]
        for q in range(n):
            block, index = divmod(q, m)
            vertex = (index - (r if block == 0 else s)) * inverse % m
            if side == "X":
                block, vertex = 1 - block, -vertex % m
            carry = (vertex + (1 if block == 0 else a)) // m
            if carry % 2:
                candidates[0].append(q)
            if block == 1:
                candidates[1].append(q)
        detector = next((qs for qs in candidates if (mask(qs) & w).bit_count() % 2), None)
        if detector is None:
            raise ValueError(f"The {side} witness has zero certified logical coordinates.")
        dmask = mask(detector)
        if any((mask(row) & dmask).bit_count() % 2 for row in rows[side]):
            raise ValueError(f"The {side} detector fails its opposite-cycle check.")
        witnesses[side] = w
        detectors[side] = dmask
    D = len(code["distance"]["X"]["witness"])
    if any(len(code["distance"][side]["witness"]) != D for side in ("X", "Z")):
        raise ValueError("This exact-distance emitter requires equal X and Z witness weights.")
    if code["distance"]["d"] != D:
        raise ValueError("The claimed overall distance differs from the witness weights.")
    for u in range(1 - D, D):
        for v in range(1 - D, D):
            if (u or v) and abs(u) + abs(v) < D and (u + a * v) % m == 0:
                raise ValueError(f"Lattice relation {(u, v)} is shorter than target {D}.")
    return {
        "n": n,
        "m": m,
        "a": a,
        "D": D,
        "r": r,
        "s": s,
        "step": step,
        "inverse": inverse,
        "rows": rows,
        "witnesses": witnesses,
        "detectors": detectors,
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def generate(source, name):
    if re.fullmatch(r"[A-Z][A-Za-z0-9_]*", name) is None:
        raise ValueError("The Lean instance name must be an uppercase identifier.")
    d = load_instance(source)
    n, m, a, D = (d[k] for k in ("n", "m", "a", "D"))
    data_ns = f"QldpcVerification.{name}Data"
    model_ns = f"QldpcVerification.{name}Model"
    arithmetic_ns = f"QldpcVerification.Lattice.{name}Arithmetic"
    parts = [
        "import Mathlib.Data.Finset.Insert\nimport Mathlib.Data.Fintype.Fin\n",
        f"/-! Generated from {source.name}. Input SHA256: {d['sha256']} -/\n",
        f"namespace {data_ns}\n",
        f"def nq : Nat := {n}\ndef cyclicLength : Nat := {m}\ndef target : Nat := {D}\n",
    ]
    for side in ("X", "Z"):
        supports = [
            "{" + ", ".join(f"⟨{q}, by decide⟩" for q in row) + "}" for row in d["rows"][side]
        ]
        parts.append(
            f"def h{side.lower()} : List (Finset (Fin {n})) := [\n  "
            + ",\n  ".join(supports)
            + "]\n"
        )
        parts.append(f"def w{side.lower()} : Nat := {d['witnesses'][side]}\n")
        parts.append(f"def det{side.lower()} : Nat := {d['detectors'][side]}\n")
    parts.append(f"end {data_ns}\n")
    model = f"""import QldpcVerification.Input.BicycleRecognition
import QldpcVerification.Input.LogicalWitness
import QldpcVerification.Input.{name}Data

namespace {model_ns}
open Matrix Module Input Input.Sparse Input.BicycleRecognition Bicycle {name}Data
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def unitStep : (ZMod {m})ˣ where
  val := {d["step"]}
  inv := {d["inverse"]}
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def baseQubits : Normalized.Edge {m} ≃ Fin {n} := Normalized.qubits
def rowVertex : Fin {m} ≃ ZMod {m} := (ZMod.finEquiv {m}).toEquiv
def xp (i : Fin {m}) := hPoints unitStep {d["r"]} {d["s"]} {a} (rowVertex i)
def zp (i : Fin {m}) := fPoints unitStep {d["r"]} {d["s"]} {a} (rowVertex i)

theorem x_supports : ∀ i : Fin {m}, hx.get i = ((xp i).map baseQubits).toFinset := by
  decide +kernel
theorem z_supports : ∀ i : Fin {m}, hz.get i = ((zp i).map baseQubits).toFinset := by
  decide +kernel
theorem x_distinct : ∀ i : Fin {m}, ((xp i).map baseQubits).Nodup := by decide +kernel
theorem z_distinct : ∀ i : Fin {m}, ((zp i).map baseQubits).Nodup := by decide +kernel

def matching : Bicycle.Match {m} {a} {n} {m} {m} :=
  matchBinomial unitStep {d["r"]} {d["s"]} (matrix hx) (matrix hz) baseQubits
    rowVertex rowVertex rowVertex.surjective rowVertex.surjective
    (fun i => (row_of_points baseQubits (hx.get i) (xp i) (x_supports i) (x_distinct i)).trans
      (hPoints_sum unitStep {d["r"]} {d["s"]} {a} (rowVertex i)))
    (fun i => (row_of_points baseQubits (hz.get i) (zp i) (z_supports i) (z_distinct i)).trans
      (fPoints_sum unitStep {d["r"]} {d["s"]} {a} (rowVertex i)))

abbrev code := matching.code

theorem wx_kernel : kernelCheck hz wx = true := by decide +kernel
theorem wz_kernel : kernelCheck hx wz = true := by decide +kernel
theorem detx_kernel : kernelCheck hx detx = true := by decide +kernel
theorem detz_kernel : kernelCheck hz detz = true := by decide +kernel
theorem wx_pair : vec nq wx ⬝ᵥ vec nq detx = 1 := by decide +kernel
theorem wz_pair : vec nq wz ⬝ᵥ vec nq detz = 1 := by decide +kernel

theorem wx_logical : code.IsXLogical (vec nq wx) :=
  code.x_logical_of_pair _ _ (kernel_of_check hz wx wx_kernel)
    (kernel_of_check hx detx detx_kernel) wx_pair
theorem wz_logical : code.IsZLogical (vec nq wz) :=
  code.z_logical_of_pair _ _ (kernel_of_check hx wz wz_kernel)
    (kernel_of_check hz detz detz_kernel) wz_pair
theorem wx_weight : hammingNorm (vec nq wx) = {D} := by
  rw [weight_eq]
  decide +kernel
theorem wz_weight : hammingNorm (vec nq wz) = {D} := by
  rw [weight_eq]
  decide +kernel

end {model_ns}
"""
    arithmetic = f"""import QldpcVerification.Lattice.FiniteBound

namespace {arithmetic_ns}

theorem finite_exclusion : ∀ i j : Fin {2 * (D - 1) + 1},
    let u : ℤ := (i.val : ℤ) - {D - 1}
    let v : ℤ := (j.val : ℤ) - {D - 1}
    u.natAbs + v.natAbs ≤ {D - 1} → (u + {a} * v) % {m} = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod {m}) * (u : ZMod {m}) + {a} * (v : ZMod {m}) = 0) :
    {D} ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion {m} {a} {D} (by decide)
    finite_exclusion u v hn hc

end {arithmetic_ns}
"""
    capstone = f"""import QldpcVerification.Input.{name}Match
import QldpcVerification.Lattice.{name}Arithmetic

namespace QldpcVerification.{name}
open Module Input {name}Data {name}Model

abbrev code := {name}Model.code

theorem rankX : finrank (ZMod 2) code.xStab = {m - 1} := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = {m - 1} := matching.rankZ

theorem parameters :
    ({n} - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX {D} ∧ code.DistZ {D} :=
  matching.parameters {D} Lattice.{name}Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.{name}
"""
    return {
        f"Input/{name}Data.lean": "\n".join(parts),
        f"Input/{name}Match.lean": model,
        f"Lattice/{name}Arithmetic.lean": arithmetic,
        f"{name}.lean": capstone,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--name", required=True)
    parser.add_argument("--output-root", type=Path, default=Path("lean/QldpcVerification"))
    args = parser.parse_args()
    for name, text in generate(args.source, args.name).items():
        path = args.output_root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


if __name__ == "__main__":
    main()
