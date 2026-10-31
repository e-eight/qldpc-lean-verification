"""Bounded weighted column generation on literal CSS logical classes.

Floating-point LP and pricing propose representatives and weights. Exported
primal and restricted-list dual certificates are checked with integer arithmetic.
The detector bases for the two CSS sectors are selected independently.
"""

import argparse
import gzip
import json
import math
import random
import time
import warnings
from collections import Counter
from fractions import Fraction
from pathlib import Path

import numpy as np
from distance566 import combination, dot, echelon, pack, reduce_vector, support
from distance566_ris import systematic_kernel
from emit_removal566 import HASHES, REVISION, read_code

BASELINE = "4461ec5e8d711cbb1cf29da5d35d0aebe987f038"
SCALE = 1_000_000


def load_json(path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt") as stream:
        return json.load(stream)


def row_solver(rows):
    basis = {}
    for i, v in enumerate(rows):
        coefficient = 1 << i
        while v:
            p = v.bit_length() - 1
            if p not in basis:
                basis[p] = (v, coefficient)
                break
            v ^= basis[p][0]
            coefficient ^= basis[p][1]
    return basis


def solve_rows(v, basis):
    coefficient = 0
    while v:
        p = v.bit_length() - 1
        if p not in basis:
            raise ValueError("Difference is outside the stabilizer span")
        v ^= basis[p][0]
        coefficient ^= basis[p][1]
    return coefficient


def integer_packing(vectors, weights, n):
    if len(vectors) != len(weights) or not vectors:
        raise ValueError("Invalid packing dimensions")
    loads = [0] * n
    for v, w in zip(vectors, weights, strict=True):
        if type(w) is not int or w < 0 or v < 0 or v.bit_length() > n:
            raise ValueError("Invalid natural weight or physical index")
        for q in support(v):
            loads[q] += w
    total = sum(weights)
    cap = max(loads, default=0)
    if total <= 0 or cap <= 0:
        raise ValueError("Empty positive packing")
    return {"totalWeight": total, "cap": cap, "bound": (total + cap - 1) // cap}


def exact_dual(vectors, prices, n, scale=SCALE):
    values = [max(0, math.ceil(float(p) * scale)) for p in prices]
    if len(values) != n:
        raise ValueError("Invalid price dimension")
    for v in vectors:
        qs = support(v)
        if not qs:
            raise ValueError("Zero logical representative")
        deficit = scale - sum(values[q] for q in qs)
        if deficit > 0:
            values[qs[0]] += deficit
    return {
        "qubit_weights": values,
        "denominator": scale,
        "upper_numerator": sum(values),
        "scope": "Only this selected representative list; no globally justified pricing",
    }


def optimize_weights(vectors, n, previous=None):
    from scipy.optimize import OptimizeWarning, linprog

    matrix = np.zeros((n, len(vectors)), dtype=float)
    for j, v in enumerate(vectors):
        matrix[support(v), j] = 1
    with warnings.catch_warnings():
        warnings.filterwarnings(
            "ignore", message="Unrecognized options detected.*", category=OptimizeWarning
        )
        result = linprog(
            -np.ones(len(vectors)),
            A_ub=matrix,
            b_ub=np.ones(n),
            bounds=(0, None),
            method="highs",
            options={"threads": 1, "parallel": False, "time_limit": 1.0},
        )
    proposals = [[1] * len(vectors)]
    if previous is not None:
        proposals.append(previous + [0] * (len(vectors) - len(previous)))
    if result.success and np.isfinite(result.x).all():
        for scale in (1000, SCALE):
            weights = [max(0, int(round(float(w) * scale))) for w in result.x]
            divisor = math.gcd(*weights)
            if divisor:
                proposals.append([w // divisor for w in weights])
        prices = np.maximum(0, -result.ineqlin.marginals)
    else:
        prices = np.ones(n)
    weights = max(
        proposals,
        key=lambda w: Fraction(
            integer_packing(vectors, w, n)["totalWeight"], integer_packing(vectors, w, n)["cap"]
        ),
    )
    arithmetic = integer_packing(vectors, weights, n)
    dual = exact_dual(vectors, prices, n)
    if (
        arithmetic["totalWeight"] * dual["denominator"]
        > arithmetic["cap"] * dual["upper_numerator"]
    ):
        raise ValueError("Exact restricted-list weak duality failed")
    return (
        weights,
        arithmetic,
        dual,
        {"status": int(result.status), "success": bool(result.success)},
    )


def independent_pairing(labels, opposite_basis):
    """Keep the light detectors; solve for independent, possibly dense witnesses."""
    k = len(labels)
    rows, tags = list(labels), [1 << i for i in range(k)]
    for q in range(k):
        pivot = next((i for i in range(q, k) if (rows[i] >> q) & 1), None)
        if pivot is None:
            raise ValueError("Detector classes do not form a basis")
        rows[q], rows[pivot] = rows[pivot], rows[q]
        tags[q], tags[pivot] = tags[pivot], tags[q]
        for i in range(k):
            if i != q and (rows[i] >> q) & 1:
                rows[i] ^= rows[q]
                tags[i] ^= tags[q]
    result = []
    for i in range(k):
        coefficients = pack(q for q in range(k) if (tags[q] >> i) & 1)
        if any(dot(coefficients, label) != (i == j) for j, label in enumerate(labels)):
            raise ValueError("Incorrect paired-witness coordinate solution")
        result.append(
            {
                "support": support(combination(opposite_basis, coefficients)),
                "old_basis_rows": support(coefficients),
            }
        )
    return result


def rank_curve(families, k=18):
    maximum = max([20, *(f["arithmetic"]["bound"] for f in families)])
    return [
        {
            "bound": d,
            "rank": len(
                echelon(
                    [
                        f["class"]
                        for f in families
                        if (d - 1) * f["arithmetic"]["cap"] < f["arithmetic"]["totalWeight"]
                    ]
                )
            ),
            "eligible_classes": sum(
                (d - 1) * f["arithmetic"]["cap"] < f["arithmetic"]["totalWeight"] for f in families
            ),
        }
        for d in range(1, maximum + 1)
    ]


def select_basis(families):
    basis, selected = {}, []
    ordered = sorted(
        families,
        key=lambda f: (
            -f["arithmetic"]["bound"],
            -Fraction(f["arithmetic"]["totalWeight"], f["arithmetic"]["cap"]),
            len(f["base_support"]),
            f["class"],
        ),
    )
    for family in ordered:
        r = reduce_vector(family["class"], basis)
        if r:
            basis[r.bit_length() - 1] = r
            selected.append(family)
            if len(selected) == 18:
                break
    return selected


class Problem:
    def __init__(self, code, side, coordinate_record, seed, pair_limit):
        self.n, self.side = code["n"], side
        self.opposite = "Z" if side == "X" else "X"
        self.rows = [pack(r) for r in code["checks"][side]]
        self.checks = [pack(r) for r in code["checks"][self.opposite]]
        self.opposite_basis = [pack(r) for r in coordinate_record[self.opposite]]
        self.old_basis = [pack(r) for r in coordinate_record[side]]
        self.solver = row_solver(self.rows)
        self.rng = random.Random(seed)
        self.matrix = np.zeros((len(self.checks), self.n), dtype=np.uint8)
        for i, r in enumerate(self.checks):
            self.matrix[i, support(r)] = 1
        pair_moves = []
        for i, a in enumerate(self.rows):
            for j in range(i):
                b = self.rows[j]
                if a & b and (a ^ b).bit_count() <= 12:
                    pair_moves.append((a ^ b, (1 << i) ^ (1 << j)))
        pair_moves.sort(key=lambda vc: (vc[0].bit_count(), vc[1]))
        self.moves = [(v, 1 << i) for i, v in enumerate(self.rows)] + pair_moves[:pair_limit]
        self.move_supports = [np.array(support(v), dtype=np.int64) for v, _ in self.moves]
        self.move_matrix = np.zeros((len(self.moves), self.n), dtype=float)
        for i, qs in enumerate(self.move_supports):
            self.move_matrix[i, qs] = 1
        self.stabilizer_matrix = np.zeros((len(self.rows), self.n), dtype=np.uint8)
        for i, r in enumerate(self.rows):
            self.stabilizer_matrix[i, support(r)] = 1

    def logical_class(self, v):
        return pack(i for i, w in enumerate(self.opposite_basis) if dot(v, w))

    def descend(self, v, coefficient, prices, max_steps=160):
        signs = np.ones(self.n)
        signs[support(v)] = -1
        costs = prices * signs
        deltas = self.move_matrix @ costs
        for _ in range(max_steps):
            i = int(np.argmin(deltas))
            if deltas[i] >= -1e-9:
                break
            qs = self.move_supports[i]
            deltas -= 2 * (self.move_matrix[:, qs] @ costs[qs])
            costs[qs] *= -1
            v ^= self.moves[i][0]
            coefficient ^= self.moves[i][1]
        return v, coefficient

    def descend_derived(self, v, coefficient, prices, moves, max_steps=96):
        """Price descent in a larger exact stabilizer neighborhood."""
        table = np.zeros((len(moves), self.n), dtype=float)
        supports = []
        for i, (mask, _) in enumerate(moves):
            qs = np.array(support(mask), dtype=np.int64)
            supports.append(qs)
            table[i, qs] = 1
        costs = np.array(prices, copy=True)
        costs[support(v)] *= -1
        deltas = table @ costs
        for _ in range(max_steps):
            i = int(np.argmin(deltas))
            if deltas[i] >= -1e-9:
                break
            qs = supports[i]
            deltas -= 2 * (table[:, qs] @ costs[qs])
            costs[qs] *= -1
            v ^= moves[i][0]
            coefficient ^= moves[i][1]
        return v, coefficient

    def information_set(self, base, prices, with_moves=False):
        """An affine section using a price-biased stabilizer information set."""
        perturb = np.array([self.rng.random() for _ in range(self.n)])
        order = np.argsort(-(prices + 0.05 * max(float(prices.max()), 0.001) * perturb))
        matrix = np.concatenate(
            [self.stabilizer_matrix[:, order], np.eye(len(self.rows), dtype=np.uint8)], axis=1
        )
        pivots, r = [], 0
        for q in range(self.n):
            available = np.flatnonzero(matrix[r:, q])
            if not len(available):
                continue
            j = r + int(available[0])
            matrix[[r, j]] = matrix[[j, r]]
            selected = matrix[:, q].astype(bool)
            selected[r] = False
            matrix[selected] ^= matrix[r]
            pivots.append(q)
            r += 1
            if r == len(self.rows):
                break
        v, coefficient = base, 0
        derived = []
        for i, q in enumerate(pivots):
            row = pack(int(order[j]) for j in np.flatnonzero(matrix[i, : self.n]))
            tag = pack(int(j) for j in np.flatnonzero(matrix[i, self.n :]))
            if with_moves:
                derived.append((row, tag))
            if (v >> int(order[q])) & 1:
                v ^= row
                coefficient ^= tag
        if with_moves:
            return v, coefficient, derived
        return v, coefficient


def preserve_witness(problem, v, directory):
    if v.bit_count() >= 20:
        return
    # This independent sparse check runs immediately, before any search continues.
    from distance566_weighted_verify import verify_witness

    record = {
        "n": problem.n,
        "detector_side": problem.side,
        "support": support(v),
        "class": problem.logical_class(v),
    }
    path = directory / f"logical-{problem.n}-{problem.side}-{v.bit_count()}-{v:x}.json"
    if path.exists():
        return
    path.write_text(json.dumps(record, indent=2) + "\n")
    verify_witness(problem.code, problem.coordinate_record, record)
    record["independent_sparse_verification"] = "pass"
    path.write_text(json.dumps(record, indent=2) + "\n")


def seed_classes(problem, light, old_families, trials, count, witness_directory):
    pool = {}
    same_class = {}

    def consider(v):
        c = problem.logical_class(v)
        if c and (c not in pool or v.bit_count() < pool[c].bit_count()):
            pool[c] = v
        if c:
            preserve_witness(problem, v, witness_directory)

    for v in problem.old_basis:
        consider(v)
    for entry in light["selected_class_basis"]:
        v = pack(entry["support"])
        if problem.logical_class(v) != entry["class"]:
            raise ValueError("Recorded light candidate has wrong class")
        consider(v)
    consider(pack(problem.code["distance"][problem.side]["witness"]))
    for entry in old_families:
        if entry["n"] == problem.n and entry["side"] == problem.side:
            c = 1 << entry["coordinate"]
            same_class[c] = [pack(r["support"]) for r in entry["family"]]
            for v in same_class[c]:
                consider(v)
    for _ in range(trials):
        order = list(range(problem.n))
        problem.rng.shuffle(order)
        for indices in systematic_kernel(problem.matrix[:, order]):
            v = pack(int(order[q]) for q in indices)
            if any(dot(v, row) for row in problem.checks):
                raise ValueError("RIS candidate syndrome failed")
            consider(v)
    ordered = sorted(pool, key=lambda c: (pool[c].bit_count(), c))
    selected = list(1 << i for i in range(18))
    # Add a light spanning basis without imposing any mutual X/Z dualization.
    basis = {}
    for c in ordered:
        r = reduce_vector(c, basis)
        if r:
            basis[r.bit_length() - 1] = r
            if c not in selected:
                selected.append(c)
    for entry in light["selected_class_basis"]:
        if len(selected) >= count:
            break
        if entry["class"] not in selected:
            selected.append(entry["class"])
    for c in ordered:
        if len(selected) >= count:
            break
        if c not in selected:
            selected.append(c)
    return selected, pool, same_class


def optimize_candidate(problem, candidate):
    vectors = list(candidate["reps"])
    weights, arithmetic, dual, status = optimize_weights(
        vectors, problem.n, candidate.get("weights")
    )
    candidate.update({"weights": weights, "arithmetic": arithmetic, "dual": dual, "solver": status})


def exported_candidate(problem, candidate):
    vectors = list(candidate["reps"])
    anchor = min(vectors, key=lambda v: (v.bit_count(), v))
    offset = candidate["reps"][anchor]
    return {
        "n": problem.n,
        "detector_side": problem.side,
        "bounded_side": problem.opposite,
        "class": candidate["class"],
        "base_support": support(anchor),
        "original_seed_weight": candidate["base"].bit_count(),
        "representatives": [
            {"support": support(v), "rows": support(candidate["reps"][v] ^ offset), "weight": w}
            for v, w in zip(vectors, candidate["weights"], strict=True)
        ],
        "arithmetic": candidate["arithmetic"],
        "restricted_dual": candidate["dual"],
        "pricing_rounds": candidate["rounds"],
        "solver": candidate["solver"],
    }


def explore(problem, light, old_families, args, budget, directory):
    started = time.monotonic()
    classes, pool, old_reps = seed_classes(
        problem,
        light,
        old_families,
        args.ris_trials if problem.n == 566 else max(8, args.ris_trials // 4),
        args.classes if problem.n == 566 else args.control_classes,
        directory / "lighter-witnesses",
    )
    candidates = []
    for c in classes:
        base = pool[c]
        reps = {base: 0}
        for v in old_reps.get(c, []):
            reps[v] = solve_rows(v ^ base, problem.solver)
        candidate = {"class": c, "base": base, "reps": reps, "rounds": 0, "stall": 0}
        if c in old_reps:
            multiplicities = Counter(old_reps[c])
            candidate["weights"] = [multiplicities[v] for v in reps]
        optimize_candidate(problem, candidate)
        candidates.append(candidate)
    initial = [exported_candidate(problem, c) for c in candidates]
    progress = [
        {
            "phase": "reweighted_initial_pools",
            "elapsed_seconds": time.monotonic() - started,
            "rank_vs_bound": rank_curve(initial),
        }
    ]
    deadline = started + budget
    limit = args.pricing_rounds if problem.n == 566 else max(4, args.pricing_rounds // 2)
    while time.monotonic() < deadline:
        families = [{"class": c["class"], "arithmetic": c["arithmetic"]} for c in candidates]
        curve = rank_curve(families)
        complete = max((r["bound"] for r in curve if r["rank"] == 18), default=0)
        goal = min(20, complete + 1)
        sufficient = echelon([c["class"] for c in candidates if c["arithmetic"]["bound"] >= goal])
        available = [
            c for c in candidates if c["rounds"] < limit and len(c["reps"]) < args.max_reps
        ]
        if not available:
            break
        candidate = min(
            available,
            key=lambda c: (
                c["rounds"] >= 3,
                not bool(reduce_vector(c["class"], sufficient)),
                c["rounds"],
                c["stall"],
                c["base"].bit_count(),
            ),
        )
        vectors = list(candidate["reps"])
        prices = (
            np.array(candidate["dual"]["qubit_weights"], dtype=float)
            / candidate["dual"]["denominator"]
        )
        # Alternate dual-first and physical-weight-regularized pricing.
        regularization = (0.0001, 0.002, 0.01, 0.03)[candidate["rounds"] % 4]
        costs = prices + regularization
        starts = sorted(vectors, key=lambda v: sum(costs[support(v)]))[:2]
        proposals = []
        for v in starts:
            coefficient = candidate["reps"][v]
            for _ in range(2 if candidate["rounds"] % 3 == 0 else 1):
                j = problem.rng.randrange(len(problem.moves))
                v ^= problem.moves[j][0]
                coefficient ^= problem.moves[j][1]
            proposals.append(problem.descend(v, coefficient, costs))
        if candidate["rounds"] % 3 == 0:
            v, coefficient, derived = problem.information_set(
                candidate["base"], costs, with_moves=True
            )
            proposals.append(problem.descend(v, coefficient, costs))
            v, coefficient = problem.descend_derived(candidate["base"], 0, costs, derived)
            proposals.append(problem.descend(v, coefficient, costs))
        if candidate["rounds"] == 0:
            proposals.append(problem.descend(candidate["base"], 0, np.ones(problem.n)))
        added = 0
        for v, coefficient in proposals:
            if v ^ candidate["base"] != combination(problem.rows, coefficient):
                raise ValueError("Pricing row-combination recovery failed")
            preserve_witness(problem, v, directory / "lighter-witnesses")
            if v not in candidate["reps"] and len(candidate["reps"]) < args.max_reps:
                candidate["reps"][v] = coefficient
                added += 1
        candidate["rounds"] += 1
        candidate["stall"] = 0 if added else candidate["stall"] + 1
        optimize_candidate(problem, candidate)
        if sum(c["rounds"] for c in candidates) % 20 == 0:
            event = {
                "phase": "pricing",
                "elapsed_seconds": time.monotonic() - started,
                "rounds": sum(c["rounds"] for c in candidates),
                "rank_vs_bound": rank_curve(
                    [{"class": c["class"], "arithmetic": c["arithmetic"]} for c in candidates]
                ),
            }
            progress.append(event)
            (directory / "progress.json").write_text(
                json.dumps({"active_problem": f"{problem.n}-{problem.side}", **event}, indent=2)
                + "\n"
            )
    families = [exported_candidate(problem, c) for c in candidates]
    selected = select_basis(families)
    coverage = {
        "detector_side": problem.side,
        "bounded_side": problem.opposite,
        "classes": [f["class"] for f in selected],
        "detectors": [f["base_support"] for f in selected],
        "paired_witnesses": independent_pairing(
            [f["class"] for f in selected], problem.opposite_basis
        ),
        "bound": min(f["arithmetic"]["bound"] for f in selected),
    }
    return {
        "n": problem.n,
        "detector_side": problem.side,
        "bounded_side": problem.opposite,
        "elapsed_seconds": time.monotonic() - started,
        "budget_seconds": budget,
        "classes_evaluated": len(classes),
        "families": families,
        "coverage": coverage,
        "rank_vs_bound": rank_curve(families),
        "progress": progress,
        "stopping_scope": "Configured time/round/list limits only; no globally justified pricing optimum",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=600)
    parser.add_argument("--seed", type=int, default=566430)
    parser.add_argument("--classes", type=int, default=64)
    parser.add_argument("--control-classes", type=int, default=40)
    parser.add_argument("--ris-trials", type=int, default=64)
    parser.add_argument("--pricing-rounds", type=int, default=24)
    parser.add_argument("--pair-moves", type=int, default=1024)
    parser.add_argument("--max-reps", type=int, default=96)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError("Use a fresh output directory")
    args.out.mkdir(parents=True)
    (args.out / "lighter-witnesses").mkdir()
    coordinates = load_json(args.baseline / "coordinates.json")["coordinates"]
    light = load_json(args.baseline / "information-sets.json")["results"]
    old = load_json(args.baseline / "packing.json.gz")["families"]
    result = {
        "baseline_commit": BASELINE,
        "challenge_revision": REVISION,
        "input_sha256": HASHES,
        "parameters": {
            k: v for k, v in vars(args).items() if k not in ("upstream", "baseline", "out")
        },
        "scope": "Exact finite numerical certificates only; existing kernel bound unchanged",
        "results": [],
    }
    for offset, (n, side) in enumerate([(566, "Z"), (566, "X"), (578, "Z"), (578, "X")]):
        code = read_code(args.upstream / f"codes/{n}-18-20.json", n)
        problem = Problem(code, side, coordinates[str(n)], args.seed + offset, args.pair_moves)
        problem.code, problem.coordinate_record = code, coordinates[str(n)]
        budget = args.seconds * (0.4 if n == 566 else 0.1)
        entry = explore(problem, light[f"{n}-{side}"], old, args, budget, args.out)
        result["results"].append(entry)
        with gzip.open(args.out / "certificates.json.gz", "wt") as stream:
            json.dump(result, stream, indent=2)
        print(
            json.dumps(
                {
                    "n": n,
                    "detector_side": side,
                    "bounded_side": problem.opposite,
                    "classes": entry["classes_evaluated"],
                    "complete_bound": entry["coverage"]["bound"],
                    "rank_at_twenty": entry["rank_vs_bound"][19]["rank"],
                    "elapsed_seconds": entry["elapsed_seconds"],
                }
            ),
            flush=True,
        )
    (args.out / "summary.json").write_text(
        json.dumps(
            {k: v for k, v in result.items() if k != "results"}
            | {
                "results": [
                    {k: v for k, v in r.items() if k not in ("families", "progress")}
                    for r in result["results"]
                ]
            },
            indent=2,
        )
        + "\n"
    )


if __name__ == "__main__":
    main()
