#!/usr/bin/env python3.13
"""Exact, bounded GF(2) reconstruction; no distance search or upstream imports."""

import argparse
import hashlib
import itertools
import json
import platform
import resource
import signal
import subprocess
from pathlib import Path

MEMORY_LIMIT = 1 << 30
SECONDS_LIMIT = 120
REPO = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def support(v):
    result = []
    while v:
        bit = v & -v
        result.append(bit.bit_length() - 1)
        v ^= bit
    return result


def pack(indices):
    result = 0
    for i in indices:
        result ^= 1 << i
    return result


def echelon(rows):
    result = {}
    for v in rows:
        while v:
            p = v.bit_length() - 1
            if p not in result:
                result[p] = v
                break
            v ^= result[p]
    return result


def rank(rows):
    return len(echelon(rows))


def canonical(rows):
    result = echelon(rows)
    for p in sorted(result):
        for q in result:
            if q > p and (result[q] >> p) & 1:
                result[q] ^= result[p]
    return [result[p] for p in sorted(result, reverse=True)]


def same_space(a, b):
    return canonical(a) == canonical(b)


def in_span(v, rows):
    basis = echelon(rows)
    while v:
        p = v.bit_length() - 1
        if p not in basis:
            return False
        v ^= basis[p]
    return True


def space_hash(rows):
    encoded = json.dumps([support(v) for v in canonical(rows)], separators=(",", ":"))
    return hashlib.sha256(encoded.encode()).hexdigest()


def dot(a, b):
    return (a & b).bit_count() & 1


def commute(x, z):
    return all(not dot(a, b) for a in x for b in z)


def puncture(v, kept):
    return pack(i for i, q in enumerate(kept) if (v >> q) & 1)


def shorten(rows, coordinates):
    """Keep ambient source labels; return the kernel of these coordinate maps."""
    rows = list(rows)
    for q in coordinates:
        pivot = next(i for i, v in enumerate(rows) if (v >> q) & 1)
        s = rows[pivot]
        rows = [v ^ s if (v >> q) & 1 else v for i, v in enumerate(rows) if i != pivot]
    return rows


def kernel(rows, n):
    reduced = canonical(rows)
    pivots = {v.bit_length() - 1 for v in reduced}
    result = [
        (1 << q) ^ pack(v.bit_length() - 1 for v in reduced if (v >> q) & 1)
        for q in range(n)
        if q not in pivots
    ]
    assert rank(result) == n - rank(rows)
    assert all(not dot(v, row) for v in result for row in rows)
    return result


def normalize_at(rows, q, pivot, alternate=False):
    rows = list(rows)
    if alternate:
        other = next(i for i, v in enumerate(rows) if i != pivot and not (v >> q) & 1)
        rows[pivot] ^= rows[other]
    distinguished = rows[pivot]
    normalized = [
        v ^ distinguished if (v >> q) & 1 else v for i, v in enumerate(rows) if i != pivot
    ]
    assert all(not (v >> q) & 1 for v in normalized)
    assert same_space(rows, normalized + [distinguished])
    return normalized, distinguished


def inspect_code(code):
    n = code["n"]
    assert code["code_type"] == "CSS"
    rows = {}
    for side in ("X", "Z"):
        sparse = code["checks"][side]
        assert all(row == sorted(set(row)) for row in sparse)
        assert all(type(q) is int and 0 <= q < n for row in sparse for q in row)
        rows[side] = [pack(row) for row in sparse]
    assert commute(rows["X"], rows["Z"])
    ranks = {side: rank(matrix) for side, matrix in rows.items()}
    assert n - ranks["X"] - ranks["Z"] == code["k"]
    witnesses = {}
    for side, opposite in (("X", "Z"), ("Z", "X")):
        record = code["distance"][side]
        v = pack(record["witness"])
        assert v.bit_count() == len(record["witness"]) == record["value"]
        assert v.bit_length() <= n
        assert all(not dot(v, r) for r in rows[opposite])
        assert not in_span(v, rows[side])
        witnesses[side] = {
            "weight": v.bit_count(),
            "zero_syndrome": True,
            "outside_same_type_row_space": True,
            "rank_with_witness": rank(rows[side] + [v]),
            "meaning": "upper bound only",
        }
    return rows, {
        "n": n,
        "row_counts": {side: len(matrix) for side, matrix in rows.items()},
        "ranks": ranks,
        "k": n - sum(ranks.values()),
        "css_commutes": True,
        "max_check_weight": max(v.bit_count() for matrix in rows.values() for v in matrix),
        "stored_witness_checks": witnesses,
    }


def replay(source_rows, final_rows, kept, pairs, x_indices, z_indices):
    # Live rows always retain source coordinate labels and original row provenance.
    rows = {side: list(matrix) for side, matrix in source_rows.items()}
    provenance = {side: list(range(len(matrix))) for side, matrix in rows.items()}
    live = list(range(578))
    steps = []
    plan = [("X", a, r) for (a, _), r in zip(pairs, x_indices, strict=True)]
    plan += [("Z", b, r) for (_, b), r in zip(pairs, z_indices, strict=True)]
    for side, q, original_row in plan:
        opposite = "Z" if side == "X" else "X"
        before_ranks = {s: rank(matrix) for s, matrix in rows.items()}
        pivot = provenance[side].index(original_row)
        assert (rows[side][pivot] >> q) & 1
        normalized, s = normalize_at(rows[side], q, pivot)
        alternate, _ = normalize_at(rows[side], q, pivot, alternate=True)
        assert same_space(normalized, alternate)
        fan = s ^ (1 << q)
        # This is precisely the opposite-side graph condition in old(C,s),
        # after moving q to the last coordinate. No physical CNOT is needed here.
        assert all(((v >> q) & 1) == dot(v ^ (((v >> q) & 1) << q), fan) for v in rows[opposite])
        cleared = [
            provenance[side][i] for i, v in enumerate(rows[side]) if i != pivot and (v >> q) & 1
        ]
        rows[side] = normalized
        provenance[side].pop(pivot)
        rows[opposite] = [v & ~(1 << q) for v in rows[opposite]]
        old_n = len(live)
        local_q = live.index(q)
        permutation = live[:local_q] + live[local_q + 1 :] + [q]
        live.pop(local_q)
        after_ranks = {s: rank(matrix) for s, matrix in rows.items()}
        assert before_ranks[side] == after_ranks[side] + 1
        assert before_ranks[opposite] == after_ranks[opposite]
        assert len(live) - sum(after_ranks.values()) == 18
        assert commute(rows["X"], rows["Z"])
        steps.append(
            {
                "step": len(steps) + 1,
                "pivot_type": side,
                "old_n": old_n,
                "new_n": len(live),
                "source_coordinate": q,
                "current_coordinate": local_q,
                "pivot_original_row": original_row,
                "pivot_current_row": pivot,
                "pivot_support_source_labels": support(s),
                "fan_support_source_labels": support(fan),
                "same_type_rows_cleared_original_labels": cleared,
                "normal_form_coordinate_order_sha256": hashlib.sha256(
                    json.dumps(permutation, separators=(",", ":")).encode()
                ).hexdigest(),
                "ranks_before": before_ranks,
                "ranks_after": after_ranks,
                "k_after": 18,
                "graph_condition_checked_on_every_opposite_row": True,
                "alternate_pivot_same_resulting_spaces": True,
                "zero_fan_cleanup": fan == 0,
                "new_row_space_hashes_source_labels": {
                    s: space_hash(matrix) for s, matrix in rows.items()
                },
            }
        )
    assert live == kept
    assert all([puncture(v, kept) for v in rows[side]] == final_rows[side] for side in ("X", "Z"))
    return steps


def block_maps(source_rows, final_rows, kept, pairs, fans, source, final):
    """Check linear maps on kernel/stabilizer bases, never enumerate logicals."""
    final_embedded = {
        side: [pack(kept[i] for i in support(v)) for v in matrix]
        for side, matrix in final_rows.items()
    }
    deleted_mask = pack(q for pair in pairs for q in pair)

    def x_decode(v):
        assert all(((v >> a) & 1) == ((v >> b) & 1) for a, b in pairs)
        r = v & ~deleted_mask
        for (a, _), fan in zip(pairs, fans, strict=True):
            if (v >> a) & 1:
                r ^= fan
        return puncture(r, kept)

    def z_lift(v):
        r = pack(kept[i] for i in support(v))
        return r ^ pack(a for (a, _), fan in zip(pairs, fans, strict=True) if dot(r, fan))

    old_x_cycles = kernel(source_rows["Z"], 578)
    old_z_cycles = kernel(source_rows["X"], 578)
    new_x_cycles = kernel(final_rows["Z"], 566)
    new_z_cycles = kernel(final_rows["X"], 566)
    decoded_x = [x_decode(v) for v in old_x_cycles]
    decoded_z = [puncture(v, kept) for v in old_z_cycles]
    assert same_space(decoded_x, new_x_cycles)
    assert same_space(decoded_z, new_z_cycles)
    assert same_space([x_decode(v) for v in source_rows["X"]], final_rows["X"])
    assert same_space([puncture(v, kept) for v in source_rows["Z"]], final_rows["Z"])
    assert all(
        not dot(pack(kept[i] for i in support(x)), z)
        for x in new_x_cycles
        for z in source_rows["Z"]
    )
    assert all(not dot(z_lift(z), x) for z in new_z_cycles for x in source_rows["X"])
    pair_stabs = [pack(pair) for pair in pairs]
    assert same_space(
        source_rows["X"],
        final_embedded["X"] + [fan ^ pair for fan, pair in zip(fans, pair_stabs, strict=True)],
    )
    assert same_space(source_rows["Z"], [z_lift(v) for v in final_rows["Z"]] + pair_stabs)
    for side, image in (("X", decoded_x), ("Z", decoded_z)):
        assert rank(image + final_rows[side]) - rank(final_rows[side]) == 18
    # Evaluate the six fan parities on new Z stabilizers, not on logical representatives.
    parity_rank = rank(
        pack(i for i, fan in enumerate(fans) if dot(v, fan)) for v in final_embedded["Z"]
    )
    assert parity_rank == 6
    witness_maps = {}
    for label, side, v in (
        ("final_X_padded_to_source", "X", pack(kept[i] for i in final["distance"]["X"]["witness"])),
        ("final_Z_parity_lift_to_source", "Z", z_lift(pack(final["distance"]["Z"]["witness"]))),
        ("source_X_decoded_to_final", "X", x_decode(pack(source["distance"]["X"]["witness"]))),
        (
            "source_Z_punctured_to_final",
            "Z",
            puncture(pack(source["distance"]["Z"]["witness"]), kept),
        ),
    ):
        target = source_rows if label.startswith("final") else final_rows
        opposite = "Z" if side == "X" else "X"
        assert all(not dot(v, row) for row in target[opposite])
        assert not in_span(v, target[side])
        witness_maps[label] = {"support": support(v), "weight": v.bit_count(), "logical": True}
    return {
        "old_cycle_dimensions": {"X": len(old_x_cycles), "Z": len(old_z_cycles)},
        "new_cycle_dimensions": {"X": len(new_x_cycles), "Z": len(new_z_cycles)},
        "cycle_map_images_equal_new_cycle_spaces": True,
        "stabilizer_map_images_equal_new_stabilizer_spaces": True,
        "induced_logical_quotient_dimensions": {"X": 18, "Z": 18},
        "source_stabilizer_decompositions_checked": True,
        "new_z_stabilizer_fan_parity_rank": parity_rank,
        "z_parities_are_not_invariants_of_logical_classes": True,
        "stored_witness_transports": witness_maps,
        "definition": {
            "notation": "K=retained coordinates; pair i=(a_i,b_i); r_i=retained X fan",
            "X_pad": "x on K; zero on all removed coordinates",
            "X_decode": "old x on K + sum_i old_x[a_i] r_i (old X cycles have x[a_i]=x[b_i])",
            "Z_lift": "z on K; z[a_i]=dot(r_i,z); z[b_i]=0",
            "Z_project": "restrict old Z cycle to K",
            "old_X_minimum_formula": "min over new X logical x and t in F2^6 of wt(x+sum_i t_i r_i)+2 wt(t)",
            "old_Z_minimum_formula": "min over new Z logical z of wt(z)+wt((dot(r_i,z))_i)",
            "formula_status": (
                "Mathematical derivation (not formalized) in README; "
                "linear identities checked on bases, not Lean"
            ),
        },
        "no_logical_enumeration": True,
    }


def main():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))
    resource.setrlimit(resource.RLIMIT_CPU, (SECONDS_LIMIT, SECONDS_LIMIT))
    signal.alarm(SECONDS_LIMIT)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, default=REPO.parent / "qldpc-challenge")
    parser.add_argument("--output", type=Path, default=HERE / "assessment.json")
    parser.add_argument("--check", action="store_true", help="check byte-for-byte regeneration")
    args = parser.parse_args()
    assert args.output.resolve().parent == HERE, "write only inside this investigation directory"
    upstream = args.upstream.resolve()
    revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True, timeout=10
    ).strip()
    files = {
        "upstream/codes/578-18-20.json": upstream / "codes/578-18-20.json",
        "upstream/codes/566-18-20.json": upstream / "codes/566-18-20.json",
        "upstream/notes/566-18-20.md": upstream / "notes/566-18-20.md",
        "upstream/notes/722-8-20.md": upstream / "notes/722-8-20.md",
        "upstream/research/local2d/boundary_engine.py": upstream
        / "research/local2d/boundary_engine.py",
        "local/lean/QldpcVerification/QubitRemoval.lean": REPO
        / "lean/QldpcVerification/QubitRemoval.lean",
        "local/lean/QldpcVerification/QubitRemovalExamples.lean": REPO
        / "lean/QldpcVerification/QubitRemovalExamples.lean",
        "generator": Path(__file__),
    }
    raw = {name: path.read_bytes() for name, path in files.items()}
    source = json.loads(raw["upstream/codes/578-18-20.json"])
    final = json.loads(raw["upstream/codes/566-18-20.json"])
    source_rows, source_info = inspect_code(source)
    final_rows, final_info = inspect_code(final)
    assert (source["n"], final["n"]) == (578, 566)
    source_coords = source["locality"]["coordinates"]
    coordinate_index = {tuple(c): q for q, c in enumerate(source_coords)}
    assert len(coordinate_index) == len(source_coords) == 578
    kept = [coordinate_index[tuple(c)] for c in final["locality"]["coordinates"]]
    assert kept == sorted(set(kept)) and len(kept) == 566
    removed = sorted(set(range(578)) - set(kept))
    assert removed == list(range(272, 278)) + list(range(564, 570))
    pairs = list(zip(range(272, 278), range(564, 570), strict=True))
    x_indices = []
    z_indices = []
    fans = []
    for a, b in pairs:
        touch_a = [i for i, v in enumerate(source_rows["X"]) if (v >> a) & 1]
        touch_b = [i for i, v in enumerate(source_rows["X"]) if (v >> b) & 1]
        assert len(touch_a) == 1 and touch_a == touch_b
        x_indices.append(touch_a[0])
        z_indices.append(source_rows["Z"].index((1 << a) | (1 << b)))
        fans.append(source_rows["X"][touch_a[0]] ^ (1 << a) ^ (1 << b))
    assert x_indices == list(range(182, 188))
    assert z_indices == [201, 207, 213, 219, 225, 231]
    assert all(fan.bit_count() == 6 and not fan & pack(removed) for fan in fans)
    for side, removed_rows in (("X", x_indices), ("Z", z_indices)):
        assert [
            puncture(v, kept) for i, v in enumerate(source_rows[side]) if i not in removed_rows
        ] == final_rows[side]
    transitions = replay(source_rows, final_rows, kept, pairs, x_indices, z_indices)
    keep_mask = pack(kept)
    typed_results = []
    for choices in itertools.product((0, 1), repeat=6):
        dx = [pair[choice] for pair, choice in zip(pairs, choices, strict=True)]
        dz = [pair[1 - choice] for pair, choice in zip(pairs, choices, strict=True)]
        restriction_ranks = {
            side: rank(v & pack(coords) for v in source_rows[side])
            for side, coords in (("X", dx), ("Z", dz))
        }
        assert restriction_ranks == {"X": 6, "Z": 6}
        for side, coords in (("X", dx), ("Z", dz)):
            reduced = [v & keep_mask for v in shorten(source_rows[side], coords)]
            assert same_space(
                reduced, [pack(kept[i] for i in support(v)) for v in final_rows[side]]
            )
        typed_results.append({"X": dx, "Z": dz})
    maps = block_maps(source_rows, final_rows, kept, pairs, fans, source, final)
    result = {
        "schema_version": 1,
        "evidence_level": "exact Python GF(2) checks; no new kernel proof",
        "upstream_revision": revision,
        "raw_input_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in raw.items()},
        "execution": {
            "python": platform.python_version(),
            "address_space_limit_bytes": MEMORY_LIMIT,
            "cpu_seconds_limit": SECONDS_LIMIT,
            "wall_alarm_seconds": SECONDS_LIMIT,
            "standard_library_only": True,
            "lean_or_lake_jobs": 0,
            "distance_searches": 0,
            "upstream_python_imports": 0,
        },
        "source": source_info,
        "final": final_info,
        "layout": {
            "exact_numeric_coordinate_matches": True,
            "unique_source_coordinates": True,
            "inherited_order": True,
            "final_to_source": kept,
            "removed_source_coordinates": removed,
            "removed_coordinate_values": {str(q): source_coords[q] for q in removed},
        },
        "endpoint_certificate": {
            "source_x_rows_removed": x_indices,
            "source_z_rows_removed": z_indices,
            "literal_final_rows_equal_source_rows_after_row_and_column_deletion": True,
            "pairs": [
                {
                    "source_coordinates": list(pair),
                    "source_x_row": xr,
                    "source_z_pair_row": zr,
                    "retained_fan_source_labels": support(fan),
                    "retained_fan_final_labels": support(puncture(fan, kept)),
                }
                for pair, xr, zr, fan in zip(pairs, x_indices, z_indices, fans, strict=True)
            ],
            "source_punctured_ranks": {
                side: rank(puncture(v, kept) for v in matrix)
                for side, matrix in source_rows.items()
            },
            "source_deleted_coordinate_restriction_ranks": {
                side: rank(v & pack(removed) for v in matrix)
                for side, matrix in source_rows.items()
            },
        },
        "reconstructed_sequence": {
            "status": "a new deterministic certificate, not the historical accepted-move trace",
            "elementary_steps": 12,
            "x_removals": 6,
            "z_zero_fan_cleanups": 6,
            "all_steps_preserve_k_and_css": True,
            "final_generating_matrices_match_literally_in_order": True,
            "normal_form_permutation_rule": "current live coordinates except pivot, then pivot",
            "steps": transitions,
        },
        "typed_deletion_checks": {
            "status": "finite check of 64 typed partitions, not logical enumeration",
            "partitions_checked": len(typed_results),
            "all_reproduce_final_row_spaces": True,
            "description": "choose exactly one coordinate per pair as X and the other as Z",
            "partitions": typed_results,
            "alternative_pivot_checks_on_reconstructed_steps": len(transitions),
        },
        "composite_maps": maps,
        "distance_assessment": {
            "established_here": "stored witnesses give source/final dX <= 20 and dZ <= 21 only",
            "conditional_on_source_lower_bounds_and_formal_transport": {
                "dX_final": ">= dX_source",
                "dZ_final": ">= dZ_source - 6",
                "dZ_source": "between dZ_final and dZ_final + 6",
                "if_source_dX_and_dZ_at_least_20": "final dX >= 20, dZ >= 14, hence d >= 14",
            },
            "cleanup_distance_cost": 0,
            "nonzero_fan_x_steps": 6,
            "automatic_d20_preservation": False,
            "source_d20_lower_bound_supplied_by_upstream": False,
            "new_kernel_certificate_created": False,
        },
        "next_proof_obligation": (
            "Prove a physical-coordinate permutation and row-space recognition theorem for "
            "old(C,s), including CSS duality; instantiate and compose the 12 checked steps. "
            "Distance 20 then still needs a genuine source lower bound and a specific "
            "Z-side no-loss argument, or direct final lower bounds."
        ),
    }
    # Detect concurrent input edits rather than quietly reporting hashes for another input.
    assert all(path.read_bytes() == raw[name] for name, path in files.items())
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.output.read_text() == encoded, "assessment does not regenerate byte for byte"
        print(f"Verified {args.output.name}: byte-for-byte regeneration passed.")
    else:
        args.output.write_text(encoded)
        print(
            f"Wrote {args.output.name}: exact 12-step reconstruction; no distance lower bound proved."
        )


if __name__ == "__main__":
    main()
