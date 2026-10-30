"""Emit literal sparse matrices and the reconstructed twelve-step removal certificate.

Only pinned upstream JSON is accepted. Lean checks sparse row equalities, each
legal elementary step, and rank certificates. This generator proves no distance.
"""

import argparse
import hashlib
import json
import os
import resource
import signal
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "lean/QldpcVerification/Input"
REVISION = "8c87413d16b78cdd934b7b7a8592cddc81ae6eed"
HASHES = {
    578: "440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514",
    566: "061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be",
}


def read_code(path, n):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != HASHES[n]:
        raise ValueError(f"Expected pinned {n}-qubit input hash")
    code = json.loads(raw)
    if code["n"] != n or code["code_type"] != "CSS":
        raise ValueError("Invalid input parameters")
    for side in ("X", "Z"):
        for row in code["checks"][side]:
            if row != sorted(set(row)) or any(type(q) is not int or not 0 <= q < n for q in row):
                raise ValueError("Invalid sparse row")
    return code


def support(mask):
    return [q for q in range(mask.bit_length()) if (mask >> q) & 1]


def finset(values):
    if not values:
        return "∅"
    return "{" + ", ".join(f"⟨{q}, by decide⟩" for q in values) + "}"


def sparse_list(name, rows, n):
    raw = (
        f"def {name}Raw : List (List ℕ) := [\n  "
        + ",\n  ".join("[" + ", ".join(map(str, row)) + "]" for row in rows)
        + "]\n"
    )
    return raw + (
        f"def {name} : List (Finset (Fin {n})) :=\n"
        f"  {name}Raw.map fun row => (row.map (Fin.ofNat {n})).toFinset\n"
        f"theorem {name}_range : {name}Raw.all (fun row => row.all (fun q => decide (q < {n}))) = true := by\n"
        "  decide +kernel\n"
    )


def reconstruct(source, final):
    rows = {s: [set(r) for r in source["checks"][s]] for s in ("X", "Z")}
    provenance = {s: list(range(len(rows[s]))) for s in rows}
    live = list(range(578))
    stages, plans = [], []
    plans_in = [("X", 272 + i, 182 + i) for i in range(6)]
    plans_in += [("Z", 564 + i, 201 + 6 * i) for i in range(6)]
    for side, source_q, source_p in plans_in:
        index = {q: i for i, q in enumerate(live)}
        stages.append({s: [sorted(index[q] for q in r) for r in rows[s]] for s in rows})
        q = live.index(source_q)
        p = provenance[side].index(source_p)
        pivot = rows[side][p]
        if source_q not in pivot:
            raise ValueError("Invalid pivot")
        kept = live[:q] + live[q + 1 :]
        fan = sorted(kept.index(x) for x in pivot if x != source_q)
        others = [i for i in range(len(rows[side])) if i != p]
        clear = [j for j, i in enumerate(others) if source_q in rows[side][i]]
        if side == "X" and (len(fan) != 7 or clear):
            raise ValueError("Expected seven-bit X fan with no row clearing")
        if side == "Z" and fan:
            raise ValueError("Expected zero-fan Z cleanup")
        plans.append({"side": side, "q": q, "p": p, "fan": fan, "clear": clear})
        rows[side] = [
            rows[side][i] ^ (pivot if source_q in rows[side][i] else set()) for i in others
        ]
        provenance[side].pop(p)
        for s in rows:
            rows[s] = [r - {source_q} for r in rows[s]]
        live.pop(q)
    index = {q: i for i, q in enumerate(live)}
    stages.append({s: [sorted(index[q] for q in r) for r in rows[s]] for s in rows})
    if stages[-1] != final["checks"]:
        raise ValueError("Reconstructed matrices differ from literal final input")
    if [source["locality"]["coordinates"][q] for q in live] != final["locality"]["coordinates"]:
        raise ValueError("Physical layout order does not match")
    return stages, plans


def rank_certificate(rows):
    """RREF with explicit row-combination masks, checked independently by Lean."""
    vectors = [sum(1 << q for q in row) for row in rows]
    combinations = [1 << i for i in range(len(rows))]
    pivots = []
    for q in range(max(v.bit_length() for v in vectors)):
        r = len(pivots)
        p = next((i for i in range(r, len(vectors)) if vectors[i] >> q & 1), None)
        if p is None:
            continue
        vectors[r], vectors[p] = vectors[p], vectors[r]
        combinations[r], combinations[p] = combinations[p], combinations[r]
        for i in range(len(vectors)):
            if i != r and vectors[i] >> q & 1:
                vectors[i] ^= vectors[r]
                combinations[i] ^= combinations[r]
        pivots.append(q)
    if len(pivots) != len(rows):
        raise ValueError("Expected independent final rows")
    cols = [[i for i, row in enumerate(rows) if q in row] for q in pivots]
    return combinations, pivots, cols


def stage_module(i):
    return (
        "Removal578Data" if i == 0 else "Removal566Data" if i == 12 else f"Removal566Stage{i}Data"
    )


def chunked_all_idx(name, data, count, result):
    """Return separate bounded facts and their exact append composition."""
    chunks = [f"({data}.drop {start}).take 16" for start in range(0, count, 16)]
    facts = [
        f"theorem {name}_block_{i} : allIdx {name}Pred ({chunk}) {16 * i} = true := by\n"
        "  decide +kernel\n"
        for i, chunk in enumerate(chunks)
    ]
    lengths = "".join(
        f"  have hl{i} : ({chunk}).length = {min(16, count - 16 * i)} := by rfl\n"
        for i, chunk in enumerate(chunks)
    )
    composition = (
        f"theorem {name}_check : {result} = true := by\n"
        f"  change allIdx {name}Pred {data} 0 = true\n"
        + lengths
        + f"  have hs : {data} = "
        + " ++ ".join(f"({c})" for c in chunks)
        + " ++ [] := by rfl\n"
        + "  rw [hs]\n  simp only [QubitRemovalSequence.allIdx_append, List.length_append, "
        + ", ".join(f"hl{i}" for i in range(len(chunks)))
        + "]\n"
        + "  rw ["
        + ", ".join(f"{name}_block_{i}" for i in range(len(chunks)))
        + "]\n  rfl\n"
    )
    return facts, composition


def commutation_checks(count):
    chunks = [f"(hx.drop {start}).take 16" for start in range(0, count, 16)]
    facts = [
        f"theorem comm_block_{i} : commCheck ({chunk}) hz = true := by decide +kernel\n"
        for i, chunk in enumerate(chunks)
    ]
    outputs = {}
    body = (
        "namespace QldpcVerification.Removal566.Stage12\n"
        "open Input Input.Sparse QubitRemovalSequence\n"
        "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    )
    for part in range(3):
        outputs[f"Removal566Comm{part}.lean"] = (
            "import QldpcVerification.Input.Removal566Data\n"
            + body
            + "\n".join(facts[part * 6 : (part + 1) * 6])
            + "end QldpcVerification.Removal566.Stage12\n"
        )
    outputs["Removal566Comm.lean"] = (
        "\n".join(f"import QldpcVerification.Input.Removal566Comm{i}" for i in range(3))
        + "\n"
        + body
        + "theorem comm_check : commCheck hx hz = true := by\n"
        "  have hs : hx = " + " ++ ".join(f"({c})" for c in chunks) + " ++ [] := by rfl\n"
        "  rw [hs]\n  simp only [commCheck_append]\n"
        "  rw [" + ", ".join(f"comm_block_{i}" for i in range(len(chunks))) + "]\n"
        "  rfl\n"
        "def code : CSSCode 566 274 274 := ⟨matrix hx, matrix hz, comm_of_check hx hz comm_check⟩\n"
        "end QldpcVerification.Removal566.Stage12\n"
    )
    return outputs


def generate(upstream):
    source = read_code(upstream / "codes/578-18-20.json", 578)
    final = read_code(upstream / "codes/566-18-20.json", 566)
    stages, plans = reconstruct(source, final)
    outputs = {}
    for i, stage in enumerate(stages):
        n = 578 - i
        prefix = (
            "import QldpcVerification.QubitRemovalSequence\n\n"
            "/-! Generated by scripts/emit_removal566.py.\n"
            f"Pinned upstream revision: {REVISION}\n"
            f"578 JSON SHA256: {HASHES[578]}\n"
            f"566 JSON SHA256: {HASHES[566]}\n"
            "Intermediate rows are reconstructed, not an upstream move-history claim. -/\n"
            f"namespace QldpcVerification.Removal566.Stage{i}\n"
            "open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport\n"
            "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        )
        parts = [prefix, sparse_list("hx", stage["X"], n), sparse_list("hz", stage["Z"], n)]
        parts += [f"end QldpcVerification.Removal566.Stage{i}\n"]
        outputs[stage_module(i) + ".lean"] = "\n".join(parts)
    for i, plan in enumerate(plans):
        side = plan["side"]
        main, other = ("hx", "hz") if side == "X" else ("hz", "hx")
        nx = len(stages[i + 1][side])
        n = 577 - i
        parts = [
            f"import QldpcVerification.Input.{stage_module(i)}\n"
            f"import QldpcVerification.Input.{stage_module(i + 1)}\n\n"
            "/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/\n"
            f"namespace QldpcVerification.Removal566.Step{i}\n"
            "open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport\n"
            "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n",
            f"def fan : Finset (Fin {n}) := {finset(plan['fan'])}\n",
            f"def clear : Finset (Fin {nx + 1}) := {finset(plan['clear'])}\n",
            f"theorem clear_last : Fin.last {nx} ∉ clear := by decide +kernel\n",
            f"def e := moveLast (⟨{plan['q']}, by decide⟩ : Fin {n + 1})\n",
            f"def rx := moveLast (⟨{plan['p']}, by decide⟩ : Fin {nx + 1})\n",
            f"def rz := Equiv.refl (Fin {len(stages[i + 1]['Z' if side == 'X' else 'X'])})\n",
            f"theorem xcheck : ∀ i, Stage{i}.{main}.get i =\n"
            f"    (normalX Stage{i + 1}.{main} fan clear (rx i)).map e.symm.toEmbedding := by\n"
            "  decide +kernel\n",
            f"theorem zcheck : ∀ i, Stage{i}.{other}.get i =\n"
            f"    (normalZ Stage{i + 1}.{other} fan (rz i)).map e.symm.toEmbedding := by\n"
            "  decide +kernel\n",
            f"end QldpcVerification.Removal566.Step{i}\n",
        ]
        outputs[f"Removal566Step{i}Checks.lean"] = "\n".join(parts)
    for side in ("X", "Z"):
        rows = stages[-1][side]
        ts, ps, cols = rank_certificate(rows)
        namespace = f"QldpcVerification.Removal566.Rank{side}"
        header = (
            f"namespace {namespace}\nopen Input Input.Sparse QubitRemovalSequence\n"
            "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
        )
        data = [
            "import QldpcVerification.Input.Removal566Data\n",
            header,
            "def ts : List ℕ := [" + ", ".join(map(str, ts)) + "]\n",
            "def ps : List (Fin 566) := [" + ", ".join(f"⟨{q}, by decide⟩" for q in ps) + "]\n",
            sparse_list("cols", cols, len(rows)),
            f"def columnPred (j : ℕ) (p : Fin 566) : Bool :=\n"
            f"  (List.finRange Stage12.h{side.lower()}.length).all fun i =>\n"
            f"    decide (p ∈ Stage12.h{side.lower()}.get i) == decide (i ∈ cols.getD j ∅)\n",
            "def pivotPred (i t : ℕ) : Bool :=\n"
            "  allIdx (fun j s => parity s t == (i == j)) cols 0\n",
            f"end {namespace}\n",
        ]
        outputs[f"Removal566Rank{side}Data.lean"] = "\n".join(data)
        column_facts, column_composition = chunked_all_idx(
            "column", "ps", len(rows), f"columnCheck Stage12.h{side.lower()} ps cols"
        )
        pivot_facts, pivot_composition = chunked_all_idx(
            "pivot", "ts", len(rows), "pivotCheck ts cols"
        )
        for part in range(3):
            outputs[f"Removal566Rank{side}Part{part}.lean"] = (
                f"import QldpcVerification.Input.Removal566Rank{side}Data\n"
                + header
                + "\n".join(column_facts[part * 6 : (part + 1) * 6])
                + "\n".join(pivot_facts[part * 6 : (part + 1) * 6])
                + f"end {namespace}\n"
            )
        outputs[f"Removal566Rank{side}.lean"] = (
            "\n".join(
                f"import QldpcVerification.Input.Removal566Rank{side}Part{i}" for i in range(3)
            )
            + "\n"
            + header
            + column_composition
            + pivot_composition
            + f"theorem rank_lower : 274 ≤ Module.finrank (ZMod 2)\n"
            f"    (Submodule.span (ZMod 2) (Set.range (matrix Stage12.h{side.lower()}))) :=\n"
            f"  rank_of_check Stage12.h{side.lower()} ts ps cols (by rfl) (by rfl) column_check pivot_check\n"
            f"end {namespace}\n"
        )
    outputs.update(commutation_checks(len(stages[-1]["X"])))
    return outputs


def main():
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    signal.alarm(120)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--upstream",
        type=Path,
        default=Path(os.environ.get("QLDPC_REPO", ROOT.parent / "qldpc-challenge")),
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = generate(args.upstream)
    for name, content in outputs.items():
        path = OUT / name
        if args.check:
            if not path.exists() or path.read_bytes() != content.encode():
                raise SystemExit(f"Regeneration mismatch: {name}")
        else:
            path.write_bytes(content.encode())
    print(f"{'Checked' if args.check else 'Generated'} {len(outputs)} pinned Lean input modules")


if __name__ == "__main__":
    main()
