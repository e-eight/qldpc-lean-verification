"""Recognize the submitted 722 input by sparse, fixed row identities.

No distance search or logical/error enumeration. Lean replay is a separate,
resource-capped task; this generator never invokes Lean.
"""

import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REVISION = "8c87413d16b78cdd934b7b7a8592cddc81ae6eed"
SHA256 = "4ab209d0c450dc7a96e6054ed29322808be87ee52eb3002c51ab4531dcc91b15"
SOURCE = "codes/722-8-20.json"
F = ((1, 0), (2, 0), (0, 2))
G = ((0, 0), (2, 1), (2, 2))


def expected_row(sector: str, row: int) -> list[int]:
    """Ordinary integer translations, with board truncation (never modulo 19)."""
    if sector not in ("X", "Z") or type(row) is not int or not 0 <= row < 357:
        raise ValueError("invalid sector or row")
    a, b = divmod(row, 17 if sector == "X" else 21)
    a += -2 if sector == "X" else 2
    sign = 1 if sector == "X" else -1
    shifts = (F, G) if sector == "X" else (G, F)
    return sorted(
        species * 361 + 19 * i + j
        for species, block in enumerate(shifts)
        for x, y in block
        for i, j in [(a + sign * x, b + sign * y)]
        if 0 <= i < 19 and 0 <= j < 19
    )


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def parse_input(raw: bytes) -> dict:
    data = json.loads(raw, object_pairs_hook=unique_object)
    if not isinstance(data, dict):
        raise ValueError("input must be an object")
    for key, expected in (("schema_version", "0.3"), ("code_type", "CSS"), ("n", 722), ("k", 8)):
        if type(data.get(key)) is not type(expected) or data[key] != expected:
            raise ValueError(f"invalid {key}")
    checks = data.get("checks")
    if not isinstance(checks, dict) or set(checks) != {"X", "Z"}:
        raise ValueError("checks must contain exactly X and Z")
    for sector in ("X", "Z"):
        rows = checks[sector]
        if not isinstance(rows, list) or len(rows) != 357:
            raise ValueError(f"{sector}: expected 357 rows")
        for index, row in enumerate(rows):
            if not isinstance(row, list) or not 1 <= len(row) <= 6:
                raise ValueError(f"{sector}[{index}]: invalid sparse row")
            if any(type(q) is not int or not 0 <= q < 722 for q in row):
                raise ValueError(f"{sector}[{index}]: invalid qubit")
            if row != sorted(set(row)):
                raise ValueError(f"{sector}[{index}]: support must be strictly increasing")
            if row != expected_row(sector, index):
                raise ValueError(f"{sector}[{index}]: row identity mismatch")
    return data


SUPPORT = r"""import QldpcVerification.Rectangle722

/-! Generated symbolic sparse-row bridge. No enumeration of qubits or errors. -/
namespace QldpcVerification.Input.Rectangle722Recognition

open Planar.Commutation

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-- A clipped monomial, in the existing physical qubit numbering. -/
def point (b : Bool) (p : Lattice) : Multiset (Fin 722) :=
  if h : 0 ≤ p.1 ∧ p.1 < 19 ∧ 0 ≤ p.2 ∧ p.2 < 19 then
    {Rectangle722.qubits (b, (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩))}
  else 0

/-- Sparse row semantics: sum of singleton indicators over F₂. -/
def row (s : Multiset (Fin 722)) (q : Fin 722) : F2 :=
  (s.map (fun r => if q = r then (1 : F2) else 0)).sum

@[simp] theorem row_add (s t : Multiset (Fin 722)) (q : Fin 722) :
    row (s + t) q = row s q + row t q := by
  simp [row, Multiset.map_add]

/-- The generic indicator bridge, including points discarded at the boundary. -/
theorem point_row (b : Bool) (p : Lattice) (q : Q) :
    row (point b p) (Rectangle722.qubits q) =
      if q.1 = b then atom p q.2 else 0 := by
  unfold point
  split
  · rename_i h
    let c : Cell := (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩)
    have hc : cell c = p := by
      apply Prod.ext <;> simp [cell, c, h.1, h.2.2.1]
    have he : q = (b, c) ↔ q.1 = b ∧ cell q.2 = p := by
      constructor
      · intro hq
        subst q
        exact ⟨rfl, hc⟩
      · rintro ⟨hb, hp⟩
        exact Prod.ext hb (cell_injective (hp.trans hc.symm))
    change row {Rectangle722.qubits (b, c)} (Rectangle722.qubits q) = _
    simp only [row, Multiset.map_singleton, Multiset.sum_singleton,
      Rectangle722.qubits.injective.eq_iff, he, atom]
    split_ifs <;> simp_all
  · rename_i h
    have hp : cell q.2 ≠ p := by
      intro hp
      have hx := q.2.1.isLt
      have hy := q.2.2.isLt
      have hx' := congrArg Prod.fst hp
      have hy' := congrArg Prod.snd hp
      simp only [cell] at hx' hy'
      omega
    simp [row, atom, hp]

/-- Six translated terms before boundary truncation. -/
def expectedX (a : XAnchor) : Multiset (Fin 722) :=
  point false (xAnchor a + fShift 0) +
  point false (xAnchor a + fShift 1) +
  point false (xAnchor a + fShift 2) +
  point true (xAnchor a + gShift 0) +
  point true (xAnchor a + gShift 1) +
  point true (xAnchor a + gShift 2)

def expectedZ (c : ZAnchor) : Multiset (Fin 722) :=
  point false (zAnchor c - gShift 0) +
  point false (zAnchor c - gShift 1) +
  point false (zAnchor c - gShift 2) +
  point true (zAnchor c - fShift 0) +
  point true (zAnchor c - fShift 1) +
  point true (zAnchor c - fShift 2)

/-- Symbolic in both anchor and qubit; only the three polynomial terms expand. -/
theorem expectedX_row (a : XAnchor) (q : Q) :
    row (expectedX a) (Rectangle722.qubits q) = HX a q := by
  rcases q with ⟨b, q⟩
  cases b <;>
    simp [expectedX, row_add, point_row, HX, xBlock, Fin.sum_univ_succ, add_assoc]

theorem expectedZ_row (c : ZAnchor) (q : Q) :
    row (expectedZ c) (Rectangle722.qubits q) = HZ c q := by
  rcases q with ⟨b, q⟩
  cases b <;>
    simp [expectedZ, row_add, point_row, HZ, zBlock, Fin.sum_univ_succ, add_assoc]

end QldpcVerification.Input.Rectangle722Recognition
"""


def header() -> str:
    return (
        "/-! Generated by scripts/gen_rectangle722.py. Fixed input data, not a search certificate.\n"
        f"Source: qldpc-challenge/{SOURCE}\nRevision: {REVISION}\nSHA256: {SHA256}\n"
        "Kernel replay must use the external capped runner. -/\n"
    )


def artifacts(raw: bytes) -> dict[str, str]:
    data = parse_input(raw)
    if hashlib.sha256(raw).hexdigest() != SHA256:
        raise ValueError("input SHA256 differs from pinned bytes")
    prefix = "lean/QldpcVerification/Input/Rectangle722"
    out = {prefix + "Support.lean": SUPPORT}
    imports = []
    # Each file checks at most 21 rows. Each decide checks only one <=6-entry multiset.
    for sector, width, count in (("X", 17, 21), ("Z", 21, 17)):
        for a in range(count):
            module = f"Rectangle722{sector}{a:02d}"
            imports.append(f"import QldpcVerification.Input.{module}")
            lines = [
                "import QldpcVerification.Input.Rectangle722Support",
                header(),
                "namespace QldpcVerification.Input.Rectangle722Recognition",
                "set_option maxRecDepth 4096",
                "set_option maxHeartbeats 800000",
            ]
            for b in range(width):
                i = a * width + b
                values = ", ".join(map(str, data["checks"][sector][i]))
                lines += [
                    f"def raw{sector}{i} : Multiset (Fin 722) := {{{values}}}",
                    f"theorem fixed{sector}{i} : raw{sector}{i} = expected{sector} ({a}, {b}) := by",
                    "  decide",
                ]
            lines.append("end QldpcVerification.Input.Rectangle722Recognition")
            out[f"{prefix}{sector}{a:02d}.lean"] = "\n\n".join(lines) + "\n"
    lines = [
        *imports,
        header(),
        "namespace QldpcVerification.Input.Rectangle722Recognition",
        "set_option maxRecDepth 4096",
        "set_option maxHeartbeats 800000",
    ]
    for sector, width in (("X", 17), ("Z", 21)):
        # Nested vectors keep reduction depth bounded by 21, not 357.
        groups = [
            "![" + ", ".join(f"raw{sector}{a * width + b}" for b in range(width)) + "]"
            for a in range(357 // width)
        ]
        lines += [
            f"def raw{sector} (a : {sector}Anchor) : Multiset (Fin 722) :=\n"
            + "  (!["
            + ",\n    ".join(groups)
            + "]) a.1 a.2",
            f"theorem fixed{sector} (a : {sector}Anchor) : raw{sector} a = expected{sector} a := by",
            "  rcases a with ⟨a, b⟩",
            "  fin_cases a <;> fin_cases b",
            *(f"  · exact fixed{sector}{i}" for i in range(357)),
        ]
    lines.insert(len(imports) + 2, "open Planar.Commutation")
    lines.append("end QldpcVerification.Input.Rectangle722Recognition")
    out[prefix + "Recognition.lean"] = "\n".join(lines) + "\n"
    out["analytical/rectangle722-submitted/INPUT.tex"] = appendix(data)
    return out


APPENDIX_TEX = r"""\documentclass{article}

\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{longtable}
\usepackage[hidelinks]{hyperref}

\begin{document}

\section{Submitted rectangle: fixed input support tables}\label{sec:input}

This appendix contains input data and integer identities, not a search certificate
or a new proof document. It makes no claim that the submitted distance label 20
has been proved. The analytic model has a separate lower bound of 15.

Source: \nolinkurl{qldpc-challenge/@SOURCE@}.

Upstream revision: \texttt{@REVISION@}.

SHA-256 of the exact JSON bytes:
\begin{center}
  \texttt{@SHA256@}
\end{center}

Schema version 0.3; CSS; 722 qubits; declared \(k = 8\). The two check arrays
have 357 rows each. Row numbers and qubit numbers below start at zero.
All entries below are copied from the input arrays, retaining row order.

\section{How to check every identity by hand}\label{sec:by-hand}

Let \(A(i,j) = 19i + j\) and \(B(i,j) = 361 + 19i + j\), for integers
\(0 \le i,j \le 18\). Discard a term if either coordinate lies outside this interval;
do not wrap coordinates. Sort the remaining integer labels.

For X row \(r = 17a + b\), with \(0 \le a \le 20\) and \(0 \le b \le 16\), put \(u = a - 2\).
The six terms are
\begin{equation}
  A(u+1,b),\ A(u+2,b),\ A(u,b+2),\ B(u,b),\ B(u+2,b+1),\ B(u+2,b+2).
\end{equation}
For Z row \(r = 21c + d\), with \(0 \le c \le 16\) and \(0 \le d \le 20\), put \(v = c + 2\).
The six terms are
\begin{equation}
  A(v,d),\ A(v-2,d-1),\ A(v-2,d-2),\ B(v-1,d),\ B(v-2,d),\ B(v,d-2).
\end{equation}
Compare the sorted retained terms with the corresponding row below. For example,
X row 0 has anchor \((-2,0)\) and retains \(A(0,0)\), \(B(0,1)\), \(B(0,2)\),
which give 0, 362, 363. Boundary rows can contain fewer than six entries.
The 714 identities require only these integer substitutions.

The Lean input uses multisets of physical labels. It checks each sparse identity
separately with \texttt{decide}, then uses a symbolic sum-of-singleton-indicators bridge.
The existing physical equivalence numbers false/A first, then true/B, with
row-major coordinates. The ordered anchors are \(\mathrm{Fin}\,21 \times \mathrm{Fin}\,17\)
for X and \(\mathrm{Fin}\,17 \times \mathrm{Fin}\,21\) for Z. No dense matrix evaluation,
error enumeration, or logical enumeration is part of this recognition. Generation does not
run Lean; proof replay and the guarded axiom audit require the external bounded runner.
"""


def appendix(data: dict) -> str:
    """LaTeX support tables for every input row, in input order."""
    text = (
        APPENDIX_TEX.replace("@SOURCE@", SOURCE)
        .replace("@REVISION@", REVISION)
        .replace("@SHA256@", SHA256)
    )
    for sector, width in (("X", 17), ("Z", 21)):
        label = f"sec:{sector.lower()}-supports"
        text += f"\n\\section{{{sector} supports}}\\label{{{label}}}\n\n"
        text += "\\begin{longtable}{lll}\n"
        text += "  Row & Anchor & Physical support \\\\\n  \\hline\n  \\endhead\n"
        for r, row in enumerate(data["checks"][sector]):
            a, b = divmod(r, width)
            a += -2 if sector == "X" else 2
            text += f"  {r} & \\(({a}, {b})\\) & {', '.join(map(str, row))} \\\\\n"
        text += "\\end{longtable}\n"
    text += "\n\\end{document}\n"
    return text


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=Path(os.environ.get("QLDPC_REPO", ROOT.parent / "qldpc-challenge")),
    )
    parser.add_argument("--output-root", type=Path, default=ROOT)
    parser.add_argument("--check", action="store_true", help="check byte-for-byte regeneration")
    args = parser.parse_args()
    raw = (args.repo / SOURCE).read_bytes()
    pinned = subprocess.run(
        ["git", "-C", str(args.repo), "show", f"{REVISION}:{SOURCE}"],
        check=True,
        capture_output=True,
    ).stdout
    if raw != pinned:
        raise ValueError("working input differs from the recorded upstream revision")
    outputs = artifacts(raw)
    for name, content in outputs.items():
        path = args.output_root / name
        encoded = content.encode()
        if args.check:
            if not path.exists() or path.read_bytes() != encoded:
                raise ValueError(f"regeneration mismatch: {name}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(encoded)
    print(
        f"{'Checked' if args.check else 'Generated'} {len(outputs)} files; 714 sparse row identities"
    )


if __name__ == "__main__":
    main()
