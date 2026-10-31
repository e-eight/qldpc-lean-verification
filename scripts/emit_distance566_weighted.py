"""Export additive target-only weighted packing proofs using standard-library checks.

Run generation and regeneration inside bounded allocations. The emitted finite
checks, rather than this parser or validator, discharge the Lean obligations.
"""

import argparse
import copy
import gzip
import hashlib
import json
import os
from pathlib import Path

from distance566_weighted_verify import label_support, rank_sets, validate_problem
from emit_removal566 import HASHES, REVISION, read_code

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "data/distance566-bound6-evaluation/2026-10-30"
INPUT = ROOT / "data/distance566-packing/2026-10-30-weighted/analysis-v1/lean-ready.json.gz"
COORDINATES = ROOT / "data/distance566-evaluation/2026-10-30/coordinates.json"
INPUT_HASH = "fa54c2e0c13097f3e2433c9a4ca2e36a82763bff02eb0cddfec76a1b0b84fe78"
COORDINATE_HASH = "171d2327eeda9aedb7a2585332fa2f495ac61aef5859e9cf6f9d8297415f34a6"
BASELINE = "4461ec5e8d711cbb1cf29da5d35d0aebe987f038"
BLOCK = 8
CAP_BLOCK = 64


def packed(support):
    return sum(1 << q for q in support)


def load_pinned(path, digest):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != digest:
        raise ValueError("Unexpected immutable input hash")
    return json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)


def target_entries(record):
    if record["baseline_commit"] != BASELINE or record["challenge_revision"] != REVISION:
        raise ValueError("Unexpected baseline or challenge revision")
    if record["input_sha256"] != {str(n): digest for n, digest in HASHES.items()}:
        raise ValueError("Unexpected literal input identities")
    selected = [r for r in record["results"] if r["n"] == 566]
    if len(selected) != 2 or {r["detector_side"] for r in selected} != {"X", "Z"}:
        raise ValueError("Expected exactly two target detector sectors")
    return sorted(selected, key=lambda r: r["detector_side"])


def validate_targets(code, coordinates, record):
    if code["n"] != 566 or any(len(code["checks"][s]) != 274 for s in ("X", "Z")):
        raise ValueError("Expected the literal target matrix dimensions")
    checked = []
    for entry in target_entries(record):
        result = validate_problem(code, coordinates, entry)
        if entry["coverage"]["bound"] < 6:
            raise ValueError("Insufficient complete weighted bound")
        if len(entry["families"]) != 18:
            raise ValueError("Expected one selected family per detector coordinate")
        if any(r["weight"] <= 0 for f in entry["families"] for r in f["representatives"]):
            raise ValueError("Expected positive-weight representatives only")
        checked.append(result)
    return checked


def prune_family(family, n=566):
    """Only delete entries, preserving the exact strict threshold for six."""
    result = copy.deepcopy(family)
    representatives = result["representatives"]
    loads = [0] * n
    total = 0
    for rep in representatives:
        total += rep["weight"]
        for q in rep["support"]:
            loads[q] += rep["weight"]
    if not total > 5 * max(loads):
        raise ValueError("Cannot prune a family below threshold six")
    retained = set(range(len(representatives)))
    order = sorted(retained, key=lambda i: (representatives[i]["weight"], i))
    for i in order:
        rep = representatives[i]
        trial = loads.copy()
        for q in rep["support"]:
            trial[q] -= rep["weight"]
        if total - rep["weight"] > 5 * max(trial):
            retained.remove(i)
            loads, total = trial, total - rep["weight"]
    result["representatives"] = [r for i, r in enumerate(representatives) if i in retained]
    cap = max(loads)
    result["arithmetic"] = {"totalWeight": total, "cap": cap, "bound": (total + cap - 1) // cap}
    result["restricted_dual"]["scope"] = "Only the newly pruned finite list"
    result["pruning"] = {
        "method": "One deterministic ascending-natural-weight deletion pass",
        "original_representatives": len(representatives),
        "remaining_representatives": len(retained),
        "strict_surplus_at_six": total - 5 * cap,
    }
    return result


def compact_record(code, coordinates, record):
    validate_targets(code, coordinates, record)
    result = {k: copy.deepcopy(v) for k, v in record.items() if k != "results"}
    result["results"] = []
    result["source_certificate_sha256"] = INPUT_HASH
    result["scope"] = "New target-only exact pruning for bound-six kernel emission"
    for entry in target_entries(record):
        compact = copy.deepcopy(entry)
        by_class = {f["class"]: f for f in entry["families"]}
        compact["families"] = [prune_family(by_class[c]) for c in entry["coverage"]["classes"]]
        compact["coverage"]["bound"] = min(f["arithmetic"]["bound"] for f in compact["families"])
        maximum = max(20, *(f["arithmetic"]["bound"] for f in compact["families"]))
        compact["rank_vs_bound"] = []
        for d in range(1, maximum + 1):
            eligible = [
                f
                for f in compact["families"]
                if (d - 1) * f["arithmetic"]["cap"] < f["arithmetic"]["totalWeight"]
            ]
            compact["rank_vs_bound"].append(
                {
                    "bound": d,
                    "rank": rank_sets([label_support(f["class"]) for f in eligible]),
                    "eligible_classes": len(eligible),
                }
            )
        result["results"].append(compact)
    validate_targets(code, coordinates, result)
    return result


def header(imports, namespace):
    return (
        "".join(f"import {name}\n" for name in imports)
        + "\n/-! Generated by scripts/emit_distance566_weighted.py.\n"
        + f"Challenge revision: {REVISION}\nTarget JSON SHA256: {HASHES[566]}\n"
        + f"Original weighted export SHA256: {INPUT_HASH}\n"
        + "Additive bound-six certificates; historical inputs remain unchanged. -/\n\n"
        + f"namespace QldpcVerification.Distance566Weighted.{namespace}\n"
        + "open Input Input.Sparse WeightedPackingCertificates\n"
        + "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
    )


def end(namespace):
    return f"end QldpcVerification.Distance566Weighted.{namespace}\n"


def numeral_list(values):
    return "[" + ", ".join(map(str, values)) + "]"


def support_definition(name, values):
    return (
        f"def {name}Raw : List (List ℕ) := [\n  "
        + ",\n  ".join(numeral_list(v) for v in values)
        + "]\n"
        + f"def {name} : List (Finset (Fin 566)) :=\n"
        + f"  {name}Raw.map fun s => (s.map (Fin.ofNat 566)).toFinset\n\n"
    )


def combine_check(expression, chunks, lemma, facts, definition=None):
    text = ""
    if definition:
        text += f"  unfold {definition}\n"
    else:
        text += f"  change capChunkCheck (List.finRange 566) {expression} = true\n"
        text += "  have hs : List.finRange 566 = " + " ++ ".join(chunks) + " ++ [] := by rfl\n"
        text += "  rw [hs]\n"
    text += "  simp only [" + ", ".join([lemma, *facts]) + "] <;> rfl\n\n"
    return text


def family_modules(side, index, family):
    tag, row_side = f"{side}{index}", side.lower()
    namespace = f"Families.{tag}"
    imports = [
        "QldpcVerification.Input.Distance566WeightedRows",
        "QldpcVerification.Input.Distance566WeightedData",
    ]
    data = header(imports, namespace)
    data += f"def base : ℕ := Data.{row_side}Masks.get ⟨{index}, by decide⟩\n"
    data += f"def cap : ℕ := {family['arithmetic']['cap']}\n\n"
    reps = family["representatives"]
    blocks = list(range(0, len(reps), BLOCK))
    for b, start in enumerate(blocks):
        data += f"def raw{b} : List RawRep := [\n  "
        data += (
            ",\n  ".join(
                f"(({packed(r['support'])}, {numeral_list(r['rows'])}), {r['weight']})"
                for r in reps[start : start + BLOCK]
            )
            + "]\n"
        )
        data += f"def reps{b} : List (Rep 274) := raw{b}.map decode\n\n"
    raw_chunks = [f"raw{b}" for b in range(len(blocks))]
    rep_chunks = [f"reps{b}" for b in range(len(blocks))]
    data += "def raw : List RawRep := " + " ++ ".join(raw_chunks) + " ++ []\n"
    data += "def reps : List (Rep 274) := " + " ++ ".join(rep_chunks) + " ++ []\n"
    data += "def weightedFamily : List (ℕ × ℕ) := family reps\n\n" + end(namespace)
    checks = header([f"QldpcVerification.Input.Distance566Weighted.{tag}Data"], namespace)
    for b in range(len(blocks)):
        checks += f"theorem range{b} : rangeCheck 566 274 raw{b} = true := by decide +kernel\n\n"
        checks += (
            f"theorem class{b} : packedClassCheck RowData.{row_side}Mask base reps{b} = true :=\n"
            "  by decide +kernel\n\n"
        )
    checks += "theorem range_check : rangeCheck 566 274 raw = true := by\n"
    checks += combine_check(
        "", raw_chunks, "rangeCheck_append", [f"range{b}" for b in range(len(blocks))], "raw"
    )
    checks += (
        f"theorem class_check : packedClassCheck RowData.{row_side}Mask base reps = true := by\n"
    )
    checks += combine_check(
        "", rep_chunks, "packedClassCheck_append", [f"class{b}" for b in range(len(blocks))], "reps"
    )
    cap_chunks = []
    for b, start in enumerate(range(0, 566, CAP_BLOCK)):
        chunk = f"((List.finRange 566).drop {start}).take {min(CAP_BLOCK, 566 - start)}"
        cap_chunks.append(f"({chunk})")
        checks += (
            f"theorem cap{b} : capChunkCheck ({chunk}) weightedFamily cap = true :=\n"
            "  by decide +kernel\n\n"
        )
    checks += "theorem cap_check : capCheck 566 weightedFamily cap = true := by\n"
    checks += combine_check(
        "weightedFamily cap",
        cap_chunks,
        "capChunkCheck_append",
        [f"cap{b}" for b in range(len(cap_chunks))],
    )
    checks += (
        "theorem threshold : (6 - 1) * cap < (weightedFamily.map Prod.snd).sum :=\n"
        "  by decide +kernel\n\n" + end(namespace)
    )
    return {
        f"Input/Distance566Weighted/{tag}Data.lean": data,
        f"Input/Distance566Weighted/{tag}Checks.lean": checks,
    }


def render(code, compact):
    entries = {e["detector_side"]: e for e in target_entries(compact)}
    files = {}
    rows = header(
        ["QldpcVerification.WeightedPackingCertificates", "QldpcVerification.Input.Removal566Data"],
        "RowData",
    )
    for side in ("X", "Z"):
        name = side.lower()
        rows += (
            f"def {name}Masks : List ℕ := "
            + numeral_list(packed(r) for r in code["checks"][side])
            + "\n\n"
        )
        rows += f"def {name}Mask (i : Fin 274) : ℕ := {name}Masks.get i\n\n"
        rows += (
            f"theorem {name}_check : rowMasksCheck Removal566.Stage12.h{name} {name}Mask = true :=\n"
            "  by decide +kernel\n\n"
        )
    files["Input/Distance566WeightedRows.lean"] = rows + end("RowData")
    data = header(["QldpcVerification.Input.Distance566WeightedRows"], "Data")
    for side in ("X", "Z"):
        name, entry = side.lower(), entries[side]
        data += (
            f"def {name}Masks : List ℕ := "
            + numeral_list(packed(v) for v in entry["coverage"]["detectors"])
            + "\n\n"
        )
        data += support_definition(f"{name}Supports", entry["coverage"]["detectors"])
        data += (
            f"def {name}PairedMasks : List ℕ := "
            + numeral_list(packed(v["support"]) for v in entry["coverage"]["paired_witnesses"])
            + "\n\n"
        )
    files["Input/Distance566WeightedData.lean"] = data + end("Data")
    for block in range(3):
        checks = header(["QldpcVerification.Input.Distance566WeightedData"], "Checks")
        for i in range(6 * block, 6 * block + 6):
            a = f"⟨{i}, by decide⟩"
            for name, other in (("x", "z"), ("z", "x")):
                for suffix, predicate in (
                    (
                        "Kernel",
                        f"kernelCheck Removal566.Stage12.h{other} (Data.{name}Masks.get {a}) = true",
                    ),
                    (
                        "PairedKernel",
                        f"kernelCheck Removal566.Stage12.h{name} (Data.{name}PairedMasks.get {a}) = true",
                    ),
                    (
                        "Vector",
                        f"vectorCheck (Data.{name}Masks.get {a}) (Data.{name}Supports.get {a}) = true",
                    ),
                ):
                    checks += f"theorem {name}{suffix}{i} : {predicate} := by decide +kernel\n\n"
        files[f"Input/Distance566WeightedChecks{block}.lean"] = checks + end("Checks")
    checks = header(
        [f"QldpcVerification.Input.Distance566WeightedChecks{b}" for b in range(3)], "Checks"
    )
    for name, other in (("x", "z"), ("z", "x")):
        for suffix, predicate in (
            ("Kernel", f"kernelCheck Removal566.Stage12.h{other} (Data.{name}Masks.get a) = true"),
            (
                "PairedKernel",
                f"kernelCheck Removal566.Stage12.h{name} (Data.{name}PairedMasks.get a) = true",
            ),
            ("Vector", f"vectorCheck (Data.{name}Masks.get a) (Data.{name}Supports.get a) = true"),
        ):
            checks += f"theorem {name}{suffix} : ∀ a : Fin 18, {predicate} := by\n  intro a\n  fin_cases a\n"
            checks += "".join(f"  · exact {name}{suffix}{i}\n" for i in range(18)) + "\n"
        checks += f"theorem {name}Paired : pairingCheck Data.{name}Supports Data.{name}PairedMasks = true := by decide +kernel\n\n"
        checks += f"theorem {name}Supports_range : Data.{name}SupportsRaw.all (fun s => s.all (fun q => decide (q < 566))) = true := by decide +kernel\n\n"
        for tag in ("Masks", "PairedMasks"):
            checks += f"theorem {name}{tag}_range : Data.{name}{tag}.all (fun m => decide (m < 2 ^ 566)) = true := by decide +kernel\n\n"
    files["Input/Distance566WeightedChecks.lean"] = checks + end("Checks")
    for side in ("X", "Z"):
        for i, family in enumerate(entries[side]["families"]):
            files.update(family_modules(side, i, family))
    imports = ["QldpcVerification.Input.Distance566WeightedChecks"]
    imports += [
        f"QldpcVerification.Input.Distance566Weighted.{side}{i}Checks"
        for side in ("X", "Z")
        for i in range(18)
    ]
    packing = header(imports, "PackingData")
    for side in ("X", "Z"):
        name = side.lower()
        for suffix, typ, values in (
            ("Reps", "List (Rep 274)", [f"Families.{side}{i}.reps" for i in range(18)]),
            ("Raw", "List RawRep", [f"Families.{side}{i}.raw" for i in range(18)]),
            ("Caps", "ℕ", [f"Families.{side}{i}.cap" for i in range(18)]),
        ):
            packing += f"def {name}{suffix} : List ({typ}) := [" + ", ".join(values) + "]\n\n"
        packing += f"def {name}Family (a : Fin 18) : List (ℕ × ℕ) := family ({name}Reps.get a)\n\n"
        for suffix, predicate, fact in (
            (
                "Class",
                f"packedClassCheck RowData.{name}Mask (Data.{name}Masks.get a) ({name}Reps.get a) = true",
                "class_check",
            ),
            ("Range", f"rangeCheck 566 274 ({name}Raw.get a) = true", "range_check"),
            ("Cap", f"capCheck 566 ({name}Family a) ({name}Caps.get a) = true", "cap_check"),
            (
                "Threshold",
                f"(6 - 1) * ({name}Caps.get a) < (({name}Family a).map Prod.snd).sum",
                "threshold",
            ),
        ):
            packing += f"theorem {name}{suffix} : ∀ a : Fin 18, {predicate} := by\n  intro a\n  fin_cases a\n"
            packing += "".join(f"  · exact Families.{side}{i}.{fact}\n" for i in range(18)) + "\n"
    files["Input/Distance566WeightedPacking.lean"] = packing + end("PackingData")
    return files


def emit(upstream, certificate, coordinates, lean_root, output, check=False):
    record = load_pinned(certificate, INPUT_HASH)
    coordinate_record = load_pinned(coordinates, COORDINATE_HASH)["coordinates"]["566"]
    code = read_code(upstream / "codes/566-18-20.json", 566)
    compact = compact_record(code, coordinate_record, record)
    files = render(code, compact)
    raw = (json.dumps(compact, indent=2) + "\n").encode()
    encoded = gzip.compress(raw, mtime=0)
    for name, text in files.items():
        target = lean_root / name
        if check:
            if not target.is_file() or target.read_bytes() != text.encode():
                raise ValueError(f"Generated module differs: {name}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(text.encode())
    if check:
        if not output.is_file() or output.read_bytes() != encoded:
            raise ValueError("Compact certificate differs")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(encoded)
    return compact, list(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--upstream",
        type=Path,
        default=Path(os.environ.get("QLDPC_REPO", ROOT.parent / "qldpc-challenge")),
    )
    parser.add_argument("--certificate", type=Path, default=INPUT)
    parser.add_argument("--coordinates", type=Path, default=COORDINATES)
    parser.add_argument("--lean-root", type=Path, default=ROOT / "lean/QldpcVerification")
    parser.add_argument("--out", type=Path, default=RECORD / "compact.json.gz")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    compact, modules = emit(
        args.upstream, args.certificate, args.coordinates, args.lean_root, args.out, args.check
    )
    print(
        json.dumps(
            {
                "generated_modules": len(modules),
                "checked": args.check,
                "sectors": [
                    {
                        "detector_side": e["detector_side"],
                        "bounded_side": e["bounded_side"],
                        "representatives": sum(len(f["representatives"]) for f in e["families"]),
                        "complete_bound": e["coverage"]["bound"],
                    }
                    for e in compact["results"]
                ],
            }
        )
    )


if __name__ == "__main__":
    main()
