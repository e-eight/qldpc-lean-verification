"""Emit additive literal-Z certificates after exact, threshold-seven pruning.

Generation and tests belong in bounded cluster allocations. This exporter uses
no solver and changes no earlier certificate or generated input.
"""

import argparse
import copy
import gzip
import json
import os
from pathlib import Path

from distance566_sector_verify import INPUT_HASHES, load, source_inputs, validate_record
from emit_removal566 import HASHES, REVISION

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "data/sector-packing-evaluation/2026-10-31/literal-z"
NUMERICAL = RECORD.parent / "numerical/z-v1/certificates.json.gz"
NUMERICAL_HASH = "d4a006802074810f13b37cc2a47728043a4f3c2a7cf7e3635dccacde11033d8e"
WEIGHTED = ROOT / "data/distance566-packing/2026-10-30-weighted"
COORDINATES = ROOT / "data/distance566-evaluation/2026-10-30/coordinates.json"
BLOCK = 8
CAP_BLOCK = 64
BASE_BLOCK = 6


def packed(support):
    return sum(1 << q for q in support)


def arithmetic(vectors, weights, n=566):
    loads = [0] * n
    for vector, weight in zip(vectors, weights, strict=True):
        if (
            type(weight) is not int
            or weight <= 0
            or type(vector) is not int
            or not 0 < vector < 2**n
        ):
            raise ValueError("Invalid positive packing entry")
        for q in range(n):
            if vector >> q & 1:
                loads[q] += weight
    total, cap = sum(weights), max(loads, default=0)
    if not total or not cap:
        raise ValueError("Empty packing")
    return {
        "loads": loads,
        "totalWeight": total,
        "cap": cap,
        "bound": (total + cap - 1) // cap,
        "strict_seven": 6 * cap < total,
    }


def retained_indices(vectors, weights, n=566):
    """Delete only, retaining the original natural weights and strict seven."""
    initial = arithmetic(vectors, weights, n)
    if not initial["strict_seven"]:
        raise ValueError("Cannot compact a packing below seven")
    total, loads = initial["totalWeight"], initial["loads"]
    retained = set(range(len(vectors)))
    for i in sorted(retained, key=lambda j: (weights[j], j)):
        trial = [
            value - weights[i] if vectors[i] >> q & 1 else value for q, value in enumerate(loads)
        ]
        if total - weights[i] > 6 * max(trial):
            retained.remove(i)
            total, loads = total - weights[i], trial
    return sorted(retained)


def require_target(record, report):
    if (
        record["n"] != 566
        or record["bounded_side"] != "Z"
        or record["detector_side"] != "X"
        or record["good_rank"] != 15
        or record["residue_scope"] != {"mode": "complete", "total_nonzero": 7}
        or not report["complete_residue_coverage"]
        or not report["all_requested_passed"]
    ):
        raise ValueError("Expected a complete, successful literal-Z handoff")


def compact_record(code, coordinates, original):
    report = validate_record(code, coordinates, original)
    require_target(original, report)
    compact = copy.deepcopy(original)
    for family in compact["good_families"]:
        representatives = family["representatives"]
        chosen = retained_indices(
            [r["mask"] for r in representatives], [r["weight"] for r in representatives]
        )
        family["representatives"] = [representatives[i] for i in chosen]
        family["arithmetic"] = arithmetic(
            [r["mask"] for r in family["representatives"]],
            [r["weight"] for r in family["representatives"]],
        )
    for case in compact["residues"]:
        weighted = case["weights"]
        chosen = retained_indices(
            [compact["pool"][i]["mask"] for i, _ in weighted], [w for _, w in weighted]
        )
        case["weights"] = [weighted[i] for i in chosen]
        case["arithmetic"] = arithmetic(
            [compact["pool"][i]["mask"] for i, _ in case["weights"]],
            [w for _, w in case["weights"]],
        )
    used = sorted({i for case in compact["residues"] for i, _ in case["weights"]})
    remap = {old: new for new, old in enumerate(used)}
    compact["pool"] = [copy.deepcopy(original["pool"][i]) for i in used]
    for new, old in enumerate(used):
        compact["pool"][new]["original_pool_index"] = old
    for case in compact["residues"]:
        case["weights"] = [[remap[i], w] for i, w in case["weights"]]
        case["eligible_count"] = sum(
            (entry["quotient_class"] & case["suffix_pattern"]).bit_count() % 2
            for entry in compact["pool"]
        )
    compact["compaction"] = {
        "source_certificate_sha256": NUMERICAL_HASH,
        "method": "Deterministic deletion only, preserving every strict threshold for seven",
        "natural_weights_unchanged": True,
        "original_pool_indices": used,
        "source_alignment": "Retained rows, supports and weights are unchanged subsets",
    }
    report = validate_record(code, coordinates, compact)
    require_target(compact, report)
    return compact


def numbers(values):
    return "[" + ", ".join(map(str, values)) + "]"


def header(imports, namespace):
    return (
        "".join(f"import {name}\n" for name in imports)
        + "\n/-! Generated by scripts/emit_distance566_sector.py.\n"
        + f"Challenge revision: {REVISION}\nLiteral target SHA256: {HASHES[566]}\n"
        + f"Numerical source SHA256: {NUMERICAL_HASH}\n"
        + "Additive threshold-seven Z certificates; earlier inputs remain unchanged. -/\n\n"
        + f"namespace QldpcVerification.Distance566SectorZ.{namespace}\n"
        + "open Matrix Input Input.Sparse WeightedPackingCertificates SectorPackingCertificates\n"
        + "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
    )


def finish(namespace):
    return f"end QldpcVerification.Distance566SectorZ.{namespace}\n"


def support_definition(name, supports):
    return (
        f"def {name}Raw : List (List ℕ) := [\n  "
        + ",\n  ".join(numbers(s) for s in supports)
        + "]\n"
        + f"def {name} : List (Finset (Fin 566)) :=\n"
        + f"  {name}Raw.map fun s => (s.map (Fin.ofNat 566)).toFinset\n\n"
    )


def concatenation(definition, chunks, lemma, facts):
    return f"  unfold {definition}\n  simp only [" + ", ".join([lemma, *facts]) + "] <;> rfl\n\n"


def cap_checks():
    text, chunks, facts = "", [], []
    for i, start in enumerate(range(0, 566, CAP_BLOCK)):
        chunk = f"(((List.finRange 566).drop {start}).take {min(CAP_BLOCK, 566 - start)})"
        chunks.append(chunk)
        facts.append(f"cap{i}")
        text += (
            f"theorem cap{i} : capChunkCheck {chunk} weightedFamily cap = true :=\n"
            "  by decide +kernel\n\n"
        )
    text += "theorem cap_check : capCheck 566 weightedFamily cap = true := by\n"
    text += "  change capChunkCheck (List.finRange 566) weightedFamily cap = true\n"
    text += "  have hs : List.finRange 566 = " + " ++ ".join(chunks) + " ++ [] := by rfl\n"
    text += (
        "  rw [hs]\n  simp only [" + ", ".join(["capChunkCheck_append", *facts]) + "] <;> rfl\n\n"
    )
    text += (
        "theorem threshold : (7 - 1) * cap < (weightedFamily.map Prod.snd).sum :=\n"
        "  by decide +kernel\n\n"
    )
    return text


def family_modules(tag, representatives, cap, mixed=False, base_ids=None, pattern=None):
    namespace = f"Families.{tag}"
    data = header(["QldpcVerification.Input.Distance566SectorZData"], namespace)
    if not mixed:
        index = int(tag.removeprefix("Good"))
        data += (
            f"def base : ℕ := QldpcVerification.Distance566Weighted.Data.xMasks.get "
            f"⟨{index}, by decide⟩\n"
        )
    data += f"def cap : ℕ := {cap}\n\n"
    starts = list(range(0, len(representatives), BLOCK))
    for b, start in enumerate(starts):
        entries = []
        for rep in representatives[start : start + BLOCK]:
            raw = f"(({rep['mask']}, {numbers(rep['rows'])}), {rep['weight']})"
            entries.append(f"({base_ids[rep['class']]}, {raw})" if mixed else raw)
        data += f"def raw{b} : List {'RawMixedRep' if mixed else 'RawRep'} := [\n  "
        data += ",\n  ".join(entries) + "]\n"
        rep_type = "MixedRep Data.numBases 274" if mixed else "Rep 274"
        decoder = "decodeMixed" if mixed else "decode"
        data += f"def reps{b} : List ({rep_type}) := raw{b}.map {decoder}\n\n"
    raw_chunks = [f"raw{i}" for i in range(len(starts))]
    rep_chunks = [f"reps{i}" for i in range(len(starts))]
    data += "def raw := " + " ++ ".join(raw_chunks) + " ++ []\n"
    data += "def reps := " + " ++ ".join(rep_chunks) + " ++ []\n"
    data += f"def weightedFamily := {'mixedFamily' if mixed else 'family'} reps\n\n"
    data += finish(namespace)
    checks = header([f"QldpcVerification.Input.Distance566SectorZ.{tag}Data"], namespace)
    range_name = "mixedRangeCheck 566 Data.numBases 274" if mixed else "rangeCheck 566 274"
    class_name = (
        "mixedClassCheck QldpcVerification.Distance566Weighted.RowData.xMask Data.baseMask"
        if mixed
        else "packedClassCheck QldpcVerification.Distance566Weighted.RowData.xMask base"
    )
    range_lemma = "mixedRangeCheck_append" if mixed else "rangeCheck_append"
    class_lemma = "mixedClassCheck_append" if mixed else "packedClassCheck_append"
    for b in range(len(starts)):
        checks += f"theorem range{b} : {range_name} raw{b} = true := by decide +kernel\n\n"
        checks += f"theorem class{b} : {class_name} reps{b} = true := by decide +kernel\n\n"
        if mixed:
            checks += (
                f"theorem pair{b} : mixedPairCheck Data.baseSupport "
                f"(Data.referenceMasks.get ⟨{pattern - 1}, by decide⟩) reps{b} = true :=\n"
                "  by decide +kernel\n\n"
            )
    checks += f"theorem range_check : {range_name} raw = true := by\n"
    checks += concatenation(
        "raw", raw_chunks, range_lemma, [f"range{i}" for i in range(len(starts))]
    )
    checks += f"theorem class_check : {class_name} reps = true := by\n"
    checks += concatenation(
        "reps", rep_chunks, class_lemma, [f"class{i}" for i in range(len(starts))]
    )
    if mixed:
        checks += (
            "theorem pair_check : mixedPairCheck Data.baseSupport "
            f"(Data.referenceMasks.get ⟨{pattern - 1}, by decide⟩) reps = true := by\n"
        )
        checks += concatenation(
            "reps", rep_chunks, "mixedPairCheck_append", [f"pair{i}" for i in range(len(starts))]
        )
    checks += cap_checks() + finish(namespace)
    return {
        f"Input/Distance566SectorZ/{tag}Data.lean": data,
        f"Input/Distance566SectorZ/{tag}Checks.lean": checks,
    }


def render(compact):
    families = {f["class"]: f for f in compact["families"]}
    used_classes = sorted({entry["class"] for entry in compact["pool"]})
    base_ids = {c: i for i, c in enumerate(used_classes)}
    data = header(
        [
            "QldpcVerification.SectorPackingCertificates",
            "QldpcVerification.Distance566WeightedCoverage",
        ],
        "Data",
    )
    data += f"abbrev numBases : ℕ := {len(used_classes)}\n"
    data += "instance : NeZero numBases := ⟨by decide⟩\n\n"
    data += (
        "def baseMasks : List ℕ := "
        + numbers(families[c]["base_mask"] for c in used_classes)
        + "\n\n"
    )
    data += support_definition("baseSupports", [families[c]["base_support"] for c in used_classes])
    data += "def baseMask (i : Fin numBases) : ℕ := baseMasks.get i\n"
    data += "def baseSupport (i : Fin numBases) : Finset (Fin 566) := baseSupports.get i\n\n"
    data += (
        "def referenceMasks : List ℕ := "
        + numbers(packed(r["reference_support"]) for r in compact["residues"])
        + "\n\n"
    )
    files = {"Input/Distance566SectorZData.lean": data + finish("Data")}
    base_imports = []
    for block, start in enumerate(range(0, len(used_classes), BASE_BLOCK)):
        name = f"Input/Distance566SectorZ/BaseChecks{block}.lean"
        base_imports.append("QldpcVerification." + name.removesuffix(".lean").replace("/", "."))
        checks = header(["QldpcVerification.Input.Distance566SectorZData"], "Checks")
        for i in range(start, min(start + BASE_BLOCK, len(used_classes))):
            a = f"⟨{i}, by decide⟩"
            checks += (
                f"theorem baseKernel{i} : kernelCheck Removal566.Stage12.hz "
                f"(Data.baseMasks.get {a}) = true := by decide +kernel\n\n"
            )
            checks += (
                f"theorem baseVector{i} : vectorCheck (Data.baseMasks.get {a}) "
                f"(Data.baseSupports.get {a}) = true := by decide +kernel\n\n"
            )
        files[name] = checks + finish("Checks")
    for i in range(7):
        name = f"Input/Distance566SectorZ/RefChecks{i}.lean"
        base_imports.append("QldpcVerification." + name.removesuffix(".lean").replace("/", "."))
        checks = header(["QldpcVerification.Input.Distance566SectorZData"], "Checks")
        a = f"⟨{i}, by decide⟩"
        checks += (
            f"theorem refKernel{i} : kernelCheck Removal566.Stage12.hx "
            f"(Data.referenceMasks.get {a}) = true := by decide +kernel\n\n"
        )
        checks += (
            f"theorem refPattern{i} : patternCheck "
            "QldpcVerification.Distance566Weighted.Data.xSupports "
            f"(Data.referenceMasks.get {a}) {(i + 1) * 2**15} = true := by decide +kernel\n\n"
        )
        files[name] = checks + finish("Checks")
    checks = header(base_imports, "Checks")
    for name, count, predicate in [
        (
            "baseKernel",
            len(used_classes),
            "kernelCheck Removal566.Stage12.hz (Data.baseMasks.get a) = true",
        ),
        (
            "baseVector",
            len(used_classes),
            "vectorCheck (Data.baseMasks.get a) (Data.baseSupports.get a) = true",
        ),
        ("refKernel", 7, "kernelCheck Removal566.Stage12.hx (Data.referenceMasks.get a) = true"),
        (
            "refPattern",
            7,
            "patternCheck QldpcVerification.Distance566Weighted.Data.xSupports (Data.referenceMasks.get a) ((a.val + 1) * 2^15) = true",
        ),
    ]:
        typ = "Data.numBases" if name.startswith("base") else "7"
        checks += f"theorem {name} : ∀ a : Fin {typ}, {predicate} := by\n  intro a\n  fin_cases a\n"
        checks += "".join(f"  · exact {name}{i}\n" for i in range(count)) + "\n"
    checks += (
        "theorem baseSupports_range : Data.baseSupportsRaw.all "
        "(fun s => s.all (fun q => decide (q < 566))) = true := by decide +kernel\n\n"
    )
    for name in ["baseMasks", "referenceMasks"]:
        checks += (
            f"theorem {name}_range : Data.{name}.all (fun m => decide (m < 2^566)) "
            "= true := by decide +kernel\n\n"
        )
    files["Input/Distance566SectorZChecks.lean"] = checks + finish("Checks")
    for j, family in enumerate(compact["good_families"]):
        files.update(
            family_modules(f"Good{j}", family["representatives"], family["arithmetic"]["cap"])
        )
    for case in compact["residues"]:
        representatives = []
        for index, weight in case["weights"]:
            entry = compact["pool"][index]
            representatives.append(
                {
                    "class": entry["class"],
                    "mask": entry["mask"],
                    "rows": entry["provenances"][0]["rows"],
                    "weight": weight,
                }
            )
        files.update(
            family_modules(
                f"Residual{case['suffix_pattern'] - 1}",
                representatives,
                case["arithmetic"]["cap"],
                True,
                base_ids,
                case["suffix_pattern"],
            )
        )
    imports = ["QldpcVerification.Input.Distance566SectorZChecks"]
    imports += [
        f"QldpcVerification.Input.Distance566SectorZ.{tag}{i}Checks"
        for tag, count in [("Good", 15), ("Residual", 7)]
        for i in range(count)
    ]
    packing = header(imports, "PackingData")
    for prefix, tag, count, typ, family_fn in [
        ("good", "Good", 15, "Rep 274", "family"),
        ("residual", "Residual", 7, "MixedRep Data.numBases 274", "mixedFamily"),
    ]:
        packing += (
            f"def {prefix}Reps : List (List ({typ})) := ["
            + ", ".join(f"Families.{tag}{i}.reps" for i in range(count))
            + "]\n\n"
        )
        packing += (
            f"def {prefix}Caps : List ℕ := ["
            + ", ".join(f"Families.{tag}{i}.cap" for i in range(count))
            + "]\n\n"
        )
        packing += f"def {prefix}Family (a : Fin {count}) := {family_fn} ({prefix}Reps.get a)\n\n"
        if prefix == "good":
            class_predicate = "packedClassCheck QldpcVerification.Distance566Weighted.RowData.xMask (QldpcVerification.Distance566Weighted.Data.xMasks.get (Fin.castAdd 3 a)) (goodReps.get a) = true"
        else:
            class_predicate = "mixedClassCheck QldpcVerification.Distance566Weighted.RowData.xMask Data.baseMask (residualReps.get a) = true"
        facts = [
            ("Class", class_predicate, "class_check"),
            ("Cap", f"capCheck 566 ({prefix}Family a) ({prefix}Caps.get a) = true", "cap_check"),
            (
                "Threshold",
                f"(7-1) * ({prefix}Caps.get a) < (({prefix}Family a).map Prod.snd).sum",
                "threshold",
            ),
        ]
        if prefix == "residual":
            facts.append(
                (
                    "Pair",
                    "mixedPairCheck Data.baseSupport (Data.referenceMasks.get a) (residualReps.get a) = true",
                    "pair_check",
                )
            )
        for suffix, predicate, fact in facts:
            packing += f"theorem {prefix}{suffix} : ∀ a : Fin {count}, {predicate} := by\n  intro a\n  fin_cases a\n"
            packing += "".join(f"  · exact Families.{tag}{i}.{fact}\n" for i in range(count)) + "\n"
        raw_type = "RawRep" if prefix == "good" else "RawMixedRep"
        packing += (
            f"def {prefix}Raw : List (List {raw_type}) := ["
            + ", ".join(f"Families.{tag}{i}.raw" for i in range(count))
            + "]\n\n"
        )
        range_predicate = (
            "rangeCheck 566 274" if prefix == "good" else "mixedRangeCheck 566 Data.numBases 274"
        )
        packing += f"theorem {prefix}Range : ∀ a : Fin {count}, {range_predicate} ({prefix}Raw.get a) = true := by\n  intro a\n  fin_cases a\n"
        packing += (
            "".join(f"  · exact Families.{tag}{i}.range_check\n" for i in range(count)) + "\n"
        )
    files["Input/Distance566SectorZPacking.lean"] = packing + finish("PackingData")
    return files


def emit(upstream, certificate, lean_root, output, check=False):
    original = load(certificate, NUMERICAL_HASH)
    code, coordinates, sources, _ = source_inputs(
        upstream,
        WEIGHTED / "focused-v1/certificates.json.gz",
        WEIGHTED / "analysis-v1/lean-ready.json.gz",
        COORDINATES,
    )
    require_target(original, validate_record(code, coordinates, original, sources["Z"]))
    compact = compact_record(code, coordinates, original)
    files = render(compact)
    for name, source in files.items():
        path = lean_root / name
        if check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise ValueError(f"Generated module differs: {name}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(source.encode())
    encoded = gzip.compress(
        (json.dumps(compact, sort_keys=True, indent=2) + "\n").encode(), mtime=0
    )
    if check:
        if not output.is_file() or output.read_bytes() != encoded:
            raise ValueError("Compact sector certificate differs")
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
    parser.add_argument("--certificate", type=Path, default=NUMERICAL)
    parser.add_argument("--lean-root", type=Path, default=ROOT / "lean/QldpcVerification")
    parser.add_argument("--out", type=Path, default=RECORD / "compact.json.gz")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    compact, files = emit(args.upstream, args.certificate, args.lean_root, args.out, args.check)
    print(
        json.dumps(
            {
                "generated_modules": len(files),
                "checked": args.check,
                "good_representatives": sum(
                    len(f["representatives"]) for f in compact["good_families"]
                ),
                "residual_representatives": [len(c["weights"]) for c in compact["residues"]],
                "used_pool": len(compact["pool"]),
                "source_hashes": INPUT_HASHES,
            }
        )
    )


if __name__ == "__main__":
    main()
