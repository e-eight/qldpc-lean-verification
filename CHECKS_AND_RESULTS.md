# Checks and results

The earlier checks in sections 1–9 were recorded on 2026-10-28 against the local qldpc-challenge
checkout at commit `48f2ee98` (committed 2026-09-24). They were run from this
directory with the checkout's interpreter:

    PY=../qldpc-challenge/.venv/bin/python
    $PY -I scripts/<script>.py ...

Each script runs in seconds, and none runs a distance search. Saved outputs
are in `data/`.

**Status:** the Python results remain exploratory. Section 10 gives a completed
kernel-checked Lean proof against a later checkout. These results are not
integrated into the board's verifier.

Sections 1–11 preserve historical commands and package names.
Section 12 gives the current package layout and build commands.

## 1. Data audit

- **Command:** `$PY -I scripts/audit.py`, output in `data/audit.txt`.
- **Results:** recorded in `RECOMMENDATIONS.md`, "What the repo data shows".
- **Key figures:**
  - 1,358 codes, of which 625 are certified exact. There are 645 cert files:
    356 from HiGHS and 289 from CryptoMiniSat.
  - The highest certified distance is 14.
  - 733 codes are uncertified, 332 of them with d ≤ 14.
  - 66 codes are named in correction commits, and none of them ever had a
    cert file.

## 2. Which codes could a packing certificate prove?

- **Command:** `$PY -I scripts/candidates.py`.
- **Outputs:** `data/packing_candidates.csv` (407 rows) and
  `data/candidates_summary.txt`.
- **The necessary test:** ratio = d_X·d_Z/n ≤ 1 (see `CERTIFICATES.md`,
  "Ceiling").
- **Counts:**
  - 365 uncertified codes pass. 94 of them have d ≥ 15, and 90 of those are not
    the user's.
  - Another 42 are near misses (1 < ratio ≤ 1.3), which can only get partial
    bounds. 23 of them have d ≥ 15, and 21 of those are not the user's.

The 90 non-user codes with d ≥ 15 that pass, grouped by how likely a
certificate is to work:

| Group | Count | Members | Assessment |
|---|---|---|---|
| Rotated surface and toric (all by @mathysrennela) | 17 | surface [[225,1,15]] to [[961,1,31]]; toric [[256,2,16]] to [[900,2,30]] | **Confirmed exact** (§3) |
| 2D-local BB / tile | 15 | 12 planar BB codes (k = 8–12, d = 15–20, ratio 0.57–0.85; by @dorakingx ×6, @vprusso ×3, @mathysrennela ×3); tile codes [[578,18,20]] (@npdeep) and [[572,18,20]] (@dorakingx); twisted-torus [[340,16,18]] (Liang et al., no layout) | Plausible. Straight lines are not logicals here, so representatives must be searched for |
| Small k, no layout | 16 | thirteen k = 2 two-block codes, plus [[780,4,20]], [[540,4,22]], [[476,6,17]] | **Tested** (§4): 1 exact, 14 one class short |
| High-rate, no layout | 42 | lifted-product including the mitten codes (18), GB/2BGA with k = 13–28 (10), ZSZ-LP (5), pair-partition CPM (4), check-deletion (3), quantum Tanner [[576,28,24]], [[256,110,16]] | Long shots. Much room (ratios as low as 0.37), but each of up to 264 classes needs its own packing |

The user's own entries (ceilings are the most a certificate could prove):

| Code | ratio | ceiling for d_X / d_Z | Reading |
|---|---|---|---|
| [[722,8,20]] | 0.64 | 36.1 / 31.4 | exactness not ruled out |
| [[562,18,19]] | 0.68 | 29.6 / 28.1 | exactness not ruled out |
| [[566,18,20]] | 0.74 | 27.0 / 28.3 | exactness not ruled out |
| [[563,18,20]] | 0.75 | 26.8 / 28.1 | exactness not ruled out |
| [[922,18,31]] | 1.08 | 28.8 / 29.7 | partial bounds only |
| [[968,18,32]] | 1.26 | 30.2 / 25.5 | partial bounds only |
| [[882,18,29]], [[924,18,31]] | 1.48, 1.51 | ~20 on the weaker side | partial bounds only |
| 684 family | 5.2–8.6 | 8–14 | out of reach |

## 3. Line check: surface, toric, BB and tile codes

- **Method:** `CERTIFICATES.md`, instance A.
- **Command:**
  `$PY -I scripts/line_check.py $(cat data/topological_files.txt) 392-8-15 450-8-16 679-8-20 578-18-20`.
  The file lists come from `scripts/select_codes.py topological`.
- **Output:** `data/line_results.txt`.

**Results:**
- **Exact.** All 17 rotated surface and toric codes reach line bound = claim on
  both sides. With the stored witnesses, their distances are exact, from
  d = 15 ([[225,1,15]]) to d = 31 ([[961,1,31]]).
- **No line certificate.** For planar BB [[392,8,15]], [[450,8,16]] and
  [[679,8,20]], and tile [[578,18,20]], the layout lines are not logicals, or
  do not span, so no bound comes out.

## 4. Orbit check: the 16 small-k two-block codes

- **Method:** `CERTIFICATES.md`, instances B and C.
- **Command:** `$PY -I scripts/orbit_check.py $(cat data/smallk_files.txt)`,
  output in `data/orbit_results.txt`.
- **Verification:** for all 16 codes, every translation generator and the
  duality π were checked to preserve the row spaces.
- **Group shapes:** quadricycle shapes come from the construction strings,
  except [[630,2,21]], whose shape (3,3,5,7) comes from its note in the repo.
  The rest are cyclic, G = Z_(n/2).
- **Class stabilizer:** for every k = 2 code, the translation group fixes every
  logical class (|S| = |G|).

| Code (author) | G | Witnesses commute | Result per side (d_X = d_Z here) |
|---|---|---|---|
| [[362,2,19]] (@MathysRennela; Wang–Pryadko GB list) | Z_181 | no | **EXACT, d = 19** |
| [[298,2,17]] | Z_149 | no | all classes covered, d ≥ 12. The π(X-witness) representative is lopsided (13/4); a 9/8 split would give 17 |
| [[226,2,15]] | Z_113 | yes | 1 class uncovered; covered classes ≥ 15 (= claim) |
| [[422,2,20]] | Z_211 | yes | 1 uncovered; covered ≥ 20 (= claim) |
| [[454,2,21]] | Z_227 | yes | 1 uncovered; covered ≥ 21 (= claim) |
| [[560,2,22]] | Z2×Z5×Z7×Z4 | yes | 1 uncovered; covered ≥ 24 (> claim) |
| [[672,2,24]] | Z7×Z4×Z4×Z3 | yes | 1 uncovered; covered ≥ 28 (> claim) |
| [[700,2,25]] | Z5×Z7×Z5×Z2 | yes | 1 uncovered; covered ≥ 24 |
| [[562,2,23]] | Z_281 | yes | 1 uncovered; covered ≥ 21 |
| [[630,2,21]] | Z3×Z3×Z5×Z7 | yes | 1 uncovered; covered ≥ 18 |
| [[346,2,18]] | Z_173 | yes | 1 uncovered; covered ≥ 16 |
| [[278,2,16]] | Z_139 | yes | 1 uncovered; covered ≥ 13 |
| [[262,2,15]] | Z_131 | yes | 1 uncovered; covered ≥ 11 |
| [[780,4,20]] | Z_390 | yes | 12 of 15 classes covered, ≥ 22 |
| [[540,4,22]] | Z_270 | yes | 12 of 15 covered, ≥ 15 |
| [[476,6,17]] | Z_238 | yes | 56 of 63 covered, ≥ 9 |

**Side results:**
- **Where the minimum-weight logicals live.** In [[672,2,24]] and
  [[560,2,22]], two of the three classes are proven heavier than the claim.
  So every logical of weight < 28 (resp. < 24) lies in the third class, the
  class of the stored witness on that side.
- **Why 14 codes stay one class short.** It is predicted by the duality lemma
  (`CERTIFICATES.md`, instance C). When the stored witnesses commute, π maps
  each witness into the other witness's class, so it adds nothing.

### Targets for closing the k = 2 codes (next step 1)

**What is needed.** With S = G, a representative with largest block share m
proves ⌈|G|/m⌉. Each code needs a Z-logical that anticommutes with its stored
X-witness, so that it lies in a class other than the Z-witness's class. Its
block share must be at most the target m below, so its weight is at most 2m.
π of that logical then serves as the X-side representative, so one search
closes both sides.

**Two kinds of code.**
- "One new rep": the witness's own class already reaches the claim, so only
  the missing class needs a representative.
- "Both": the witness's own class falls short too, so it also needs a
  better-balanced representative.

**Minimum weight.** By the duality lemma, representatives of the missing
classes weigh at least the covered bound.

| Code | \|G\| | Claim | Target max share m | Needs |
|---|---|---|---|---|
| [[226,2,15]] | 113 | 15 | 8 | one new rep |
| [[422,2,20]] | 211 | 20 | 11 | one new rep |
| [[454,2,21]] | 227 | 21 | 11 | one new rep |
| [[560,2,22]] | 280 | 22 | 13 | one new rep, weight 24–26 |
| [[672,2,24]] | 336 | 24 | 14 | one new rep, weight exactly 28 split 14/14 |
| [[298,2,17]] | 149 | 17 | 9 | a balanced rep in the π(X-witness) class |
| [[262,2,15]] | 131 | 15 | 9 | both |
| [[278,2,16]] | 139 | 16 | 9 | both |
| [[346,2,18]] | 173 | 18 | 10 | both |
| [[562,2,23]] | 281 | 23 | 12 | both |
| [[630,2,21]] | 315 | 21 | 15 | both |
| [[700,2,25]] | 350 | 25 | 14 | both |

**Watch for refutations.** Such a search can also find a logical lighter than
a claimed distance where the covered bound is below the claim. That is a
refutation: save it through the repo's kit as AGENTS.md requires.

## 5. Independent re-verification of the k = 2 cyclic results

- **Command:**
  `$PY -I scripts/verify_orbit_k2.py $(grep -E '/(226|262|278|298|346|362|422|454|562)-2-' data/smallk_files.txt)`.
- **Output:** `data/verify_k2_results.txt`.
- **Method:** a separate code path that uses only rank tests against the
  stabilizer row spaces, with no logical bases and no class bookkeeping. It
  checks:
  - the full shift automorphism on every row;
  - that each representative is a logical;
  - that each shift stays in its class;
  - that the two representatives lie in distinct nonzero classes;
  - the coverage arithmetic.

**Results:**
- [[362,2,19]]: d_X ≥ ⌈181/10⌉ = 19 and d_Z ≥ 19. With the weight-19 witnesses,
  **EXACT**.
- [[298,2,17]]: ≥ ⌈149/13⌉ = 12 on both sides.
- The other seven: both representatives share a class, so there is no full
  certificate.

All of this matches §4.

## 6. Positive control on solver-certified codes

- **Command:** `$PY -I scripts/orbit_check.py $(cat data/control_files.txt)`,
  output in `data/control_results.txt`. The list comes from
  `select_codes.py control`.
- **Scope:** 64 solver-certified generalized-bicycle codes with k ≤ 6.
  - 49 were skipped: the cyclic shift in standard [A | B] indexing is not an
    automorphism of those entries.
  - 15 ran.
- **Results:**
  - No bound contradicted a known distance. The built-in soundness check
    never fired.
  - None of the 15 came out exact on either side. That fits these codes: they
    are small, mostly have d² > n, or have k = 6 with small class stabilizers.
- **Takeaway:** the control supports soundness. It does not show how often the
  method succeeds.

## 7. Constrained search for the k = 2 codes

Run on 2026-10-28 at the user's request. It covered the 12 two-block k = 2
codes that §4 left open; [[362,2,19]] was already exact.

**Method** (`scripts/class_search.py`, one process per code, 12 in parallel):
1. **Precondition.** Check that every translation fixes every logical class.
   The mixing formula depends on this.
2. **Seeding.** For each nonzero X-class x, the repo's C++ constrained search
   (`gf2_fast.dem_rand_witness`, 50,000 trials) finds the lightest Z-logical
   that anticommutes with x. Each such call covers two Z-classes at a time.
3. **Main search.** Random information sets on ker(H_X). Each trial scans the
   systematic rows and all pairwise sums, and keeps every nontrivial Z-logical
   up to a weight cap, one per (class, block split).
4. **Running evaluation.** The search evaluates the certificate exactly as it
   goes: the best single or mixed orbit value per class, then the median over
   classes (`CERTIFICATES.md`). It stops once the certificate closes, or after
   600 s.
5. **Refutations.** Any logical lighter than a claim would be re-validated by
   `research/audits/leader_audit.validate_witness` and written to
   `data/refutations/` before anything else. None was found, so that directory
   does not exist.

**Commands:**

    $PY -I scripts/class_search.py <code> --seconds 600 --trials 10000000 --seed 11 --seed-trials 50000
    $PY -I scripts/verify_orbit_k2.py --reps-dir data/reps $(cat data/k2_files.txt)

**Outputs:**
- `data/reps/<code>.json`: certificate representatives and the archive of all
  (class, split) representatives found;
- `data/search_logs/<code>.log`;
- `data/verify_k2_search_results.txt`.

**Results.** Every bound below was re-derived by the independent rank-test
path (`verify_orbit_k2.py`), and the two paths agree exactly. Class values are
listed lowest first, and the bound is the ceiling of the middle one.

| Code | Claim | Certified bound | Status | Search | Class values |
|---|---|---|---|---|---|
| [[226,2,15]] | 15 | 15 | **EXACT** | seeding only, 5 s | 0, 14.12, 14.12 |
| [[262,2,15]] | 15 | 15 | **EXACT** | 854 trials, 20 s | 11.91, 14.56, 15.23 (mixed) |
| [[362,2,19]] | 19 | 19 | **EXACT** (§4) | none needed | 0, 18.10, 18.10 |
| [[422,2,20]] | 20 | 20 | **EXACT** | seeding only, 14 s | 0, 19.18, 19.18 |
| [[562,2,23]] | 23 | 21 | open | 20,256 trials, 600 s | 12.77, 20.07, 21.62 |
| [[346,2,18]] | 18 | 17 | open | 21,201 trials, 600 s | 15.73, 16.57, 17.30 |
| [[560,2,22]] | 22 | 18 | open | 10,303 trials, 600 s | 14.00, 17.50, 23.33 |
| [[630,2,21]] | 21 | 18 | open | 6,577 trials, 600 s | 17.50, 17.50, 21.00 |
| [[700,2,25]] | 25 | 18 | open | 14,156 trials, 600 s | 17.50, 17.50, 23.33 |
| [[672,2,24]] | 24 | 17 | open | 8,848 trials, 600 s | 16.80, 16.80, 28.00 |
| [[454,2,21]] | 21 | 16 | open | 27,592 trials, 600 s | 13.35, 15.13, 20.64 |
| [[278,2,16]] | 16 | 13 | open | 26,214 trials, 600 s | 9.93, 12.64, 15.44 |
| [[298,2,17]] | 17 | 12 | open | 32,275 trials, 600 s | 11.46, 11.46, 16.56 |

**Summary:**
- **Exact distances.** 4 of the 13 codes are exact, all above the board's
  solver ceiling of d = 14.
- **Lower bounds.** The other 9 now have certified lower bounds of 12 to 21.
  Before this they had none.
- **No refutation.** For each pair of classes, the lightest logical the seeding
  found weighs at least the claimed distance.

**Why the open codes stall.** Their missing classes contain only lopsided
logicals.
- Example: in [[454,2,21]], every representative found in class `10` has at
  least 17 qubits in block A, and every one in class `11` at least 15 in
  block B.
- By the block-share ceiling in `CERTIFICATES.md`, if that holds for all
  logicals of those classes, no packing family of any kind can certify more
  than d ≥ 16 for this code. This is observed, not proven.
- So more search is unlikely to close these codes. Exact certification for
  them needs a different method; the bounds above are what packing gives.

**Search-method notes.**
- A 30 s calibration run on [[454,2,21]] gave the same per-class picture for
  two different seeds.
- The search loads earlier runs' representatives (after re-checking them)
  before it starts, so reruns accumulate.

## 8. Lean pilot: [[225,1,15]] proved exact

On 2026-10-28, with elan installed by the user, the project `lean/QldpcCert` was
set up on Mathlib `v4.36.0-rc2`, using the prebuilt cache (`lake exe cache
get`), so nothing was built from source.

**The theorem.** `Surface225.distance : code.DistX 15 ∧ code.DistZ 15`, where
`code` is built from the board entry's own check matrices. The build succeeds,
and the instance file elaborates in about 13 s.

**How it is proved.** The general lemmas in `Certificates.lean` are proved
once, for every code:
- double counting;
- rank lower bounds from pivot certificates;
- rank–nullity;
- the k = 1 packing theorem.

The instance supplies the data: 15 disjoint line logicals per side and pivot
certificates of rank 112 for H_X and H_Z. All finite facts are checked by
`native_decide`.

**Trust.** `#print axioms` shows:
- the general theorem rests only on propext, Classical.choice and Quot.sound;
- the instance adds 19 `native_decide` evaluations (Lean's compiler) and has
  no `sorryAx`.

The trusted base is therefore:
- Lean's kernel and compiler;
- the 55-line `Spec.lean`;
- the generated data file matching the board's JSON.

**Commands:**

    $PY -I scripts/gen_lean_instance.py 225-1-15 Surface225 lean/QldpcCert/QldpcCert/Surface225Data.lean
    cd lean/QldpcCert && PATH="$HOME/.elan/bin:$PATH" lake build

**Next.**
- Move the finite checks into the kernel, using bitmask checkers with
  correctness proofs, so the compiler leaves the trusted base.
- Reuse the same template for [[961,1,31]].
- Prove a general-k packing theorem, for the toric and generalized-bicycle
  results.

## 9. Moving the finite checks into the kernel (historical pause)

The goal is to remove the 19 `native_decide` axioms from §8, so that
`Surface225.distance` rests on Lean's kernel alone. It was paused on
2026-10-28 because this workstation is memory-limited. The user will provide
other compute.

**Done:**
- `QldpcCert/Bits.lean` compiles. It is a verified bitmask checker library:
  - `commCheck`, `kerCheck`, `dotBit`, `pivotCheck` (with `combine`),
    `disjointCheck`, `popBelow` and `allOf`;
  - for each checker, a theorem turning `= true` into the Mathlib fact;
  - the fast parity `fold`, proved correct.
- `QldpcCert/Surface225.lean` was rewritten to discharge every fact with
  `decide +kernel`. The data file is regenerated as `List Nat`.

**Not done:** building that file. It is no longer imported by the package
root, so a plain `lake build` stays light.

**Measured, against the [[225,1,15]] data:**
- **The parity fold had an exponential blow-up in the kernel.** The
  accumulator `c ^^^ (c >>> s)` is passed down unevaluated and contains `c`
  twice, so 8 levels mean 2⁸ re-evaluations. A dot product cost about 5 ms.
  - Forcing the accumulator to a numeral at each step,
    `Nat.casesOn c (k 0) (fun p => k (p + 1))`, cut the 32-row commutation
    check from 20 s to 2.8 s.
  - Not yet merged into `Bits.lean`. The merge needs a small lemma,
    `strict c k = k c`, proved by `cases c <;> rfl`.
- **Beyond about 32 rows the check grows much faster than linearly.** 64 rows
  ran past 150 s. An earlier full attempt reached 2.6 GB RSS. Memory growth or
  swapping on this box is the suspected cause; not yet diagnosed.
- **Smaller observations:**
  - in the kernel, `c >>> 200` took about 2–4 ms, versus 0.3 ms for
    `c / 2 ^ 200`;
  - core `List.all` versus the custom `allOf` made no difference;
  - the iteration itself is cheap (4 ms over 112 elements).

**Next, on the bigger machine:**
1. Merge the strict fold.
2. Measure memory and time for the full commutation check (12,544 dot
   products), the pivot checks and the line checks.
3. If it is still heavy, reduce the work. For example, check commutation
   through column masks: an X-row's syndrome is the XOR of the H_Z columns on
   its support, so about 448 XORs instead of 12,544 dot products. That needs a
   lemma tying column masks to row masks.

A working compiler-trusted build is a one-word change: replace
`decide +kernel` with `native_decide` in `Surface225.lean`. The checkers are
plain `Bool` functions, so this works, and it trusts the compiler as §8 did.

## 10. Kernel-only instance completed on the Slurm cluster

Completed on 2026-10-28 local time, 2026-10-29 UTC, on an authorized Slurm cluster.
Connection and scheduler details are retained only in the ignored local configuration and raw records.

`Surface225.distance` now proves `code.DistX 15 ∧ code.DistZ 15` with all finite
checks evaluated by Lean's kernel. Its axiom report is exactly:

    'Surface225.distance' depends on axioms: [propext, Classical.choice, Quot.sound]

There is no `native_decide` axiom and no `sorryAx`. The CSS specification and
the correspondence between the JSON and generated matrices remain review obligations.

### What changed

`Bits.lean` now forces numeric accumulators, uses arithmetic bit tests, and
provides structurally recursive bitwise operations with equivalence proofs.
These changes alone did not make the full commutation check practical.
A run with strict, well-founded bitwise operations reached its 30-minute limit
in run `kernel-bitwise-timeout` before that check finished.

The successful approach uses the sparse supports of the original check matrices.
`Sparse.lean` checks every row support against every coordinate of its bitmask.
It then computes dot products by counting supported bits modulo two.
Its soundness proofs turn these checks into matrix commutation and kernel membership.
The final traversal processes supports directly rather than repeatedly indexing their list.

`SparseRank.lean` checks the supports of selected matrix columns against the
verified row supports. It verifies the same pivot identities `(T H)[i,p_j] = [i=j]`
through those columns. This avoids reconstructing large transformed rows.
The original transform matrices and pivots remain in `Surface225Data.lean`.

The general packing theorem and `Spec.lean` did not change.
`Surface225Support.lean` contains the additional generated data.
All support, commutation, rank, logical, weight, and disjointness checks are
kernel evaluations. `KernelAudit.lean` guards the exact axiom list.

### Successful run and reproduction

Cluster run `kernel-pilot` completed with exit status `0:0`.
It requested two CPUs and 16 GB of memory. The pinned versions remain
Lean `v4.36.0-rc2` and Mathlib commit `9d581dfff2e41de989072ea63abf3daf69311520`.
The complete log, including source hashes and the axiom report, is
`data/kernel-evaluation/kernel-build.log`.
Follow-up run `kernel-audit` also passed the default package build and
`KernelAudit.lean`. Its log is `data/kernel-evaluation/kernel-audit.log`.

| Measurement | Result |
|---|---|
| Instance kernel evaluation, wall time | 240.50 seconds |
| Instance kernel evaluation, user CPU time | 229.56 seconds |
| Peak resident memory from `/usr/bin/time -v` | 4,145,924 KiB, about 3.95 GiB |
| Swaps reported by `/usr/bin/time -v` | 0 |
| Complete Slurm job, including library build and axiom report | 4 minutes 47 seconds |

The measured run fits a 16 GB allocation. A local build was not benchmarked.
This local session lacked the installed toolchain and Mathlib cache described
in the earlier notes. The remote installation and cache location is retained in the local configuration.

From the Lean package directory, the instance command was:

    lake env lean -DmaxRecDepth=100000 -DmaxHeartbeats=0 -Dprofiler=true -Dprofiler.threshold=1000 -o .lake/build/lib/lean/QldpcCert/Surface225.olean QldpcCert/Surface225.lean

`archive/QldpcCert/kernel.sbatch` runs the library build, instance check, and axiom audit.
It expects the pinned Lean installation at `tools/lean/` beneath the submission directory.
The local configuration supplies any required certificate bundle.
Set `QLDPC_FETCH_CACHE=0` only when that cache is complete.

The source entry came from sibling checkout `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.
The SHA-256 of `codes/225-1-15.json` was
`7a180b0f143d672013952e2f24fa12664e20fe7b03f993994076194e4b28bebe`.
Regenerating both Lean data files produced identical outputs.
The earlier board-wide counts were not recomputed during this continuation.
The challenge repository and its board certification status were not modified.

## 11. QECLean adapter, Python cleanup, and overlap theorem

The QECLean proof now passes for the original `codes/225-1-15.json`.
The source checkout is `8c87413d16b78cdd934b7b7a8592cddc81ae6eed`.
The JSON SHA256 remains `7a180b0f143d672013952e2f24fa12664e20fe7b03f993994076194e4b28bebe`.

`lean/QecBridge` pins Lean 4.30.0-rc2 and QECLean commit
`fed020a7e6be12825196cbee7bbc1ba56554158c`.
Its Mathlib commit is `a3fde5017d59fa3cef8d4d24999f6b9b71b89a3b`.
The earlier Lean 4.36 proof remains separate.
The new package reuses its specification and generated sparse input.

`QecBridge.Surface225.parameters` proves both stabilizer ranks equal 112,
that the rank formula gives one encoded qubit, and that both CSS distances equal 15.
Lean matches all 224 submitted rows to QECLean's canonical construction.
The qubit map sends vertex `(x,y)` to submitted index `(14-x)*15+y`.
Generic transport lemmas preserve dot products, kernels, row spaces, and Hamming weight.
QECLean's rank and distance theorems then apply to these actual input matrices.
The new proof does not depend on the old instance's distance theorem.

Run from `lean/QecBridge`:

```bash
lake exe cache get
LEAN_NUM_THREADS=2 lake build
lake env lean QecBridge/KernelAudit.lean
```

The full adapter target builds, including the concrete instance.
The guarded audits accept only the three standard axioms.
The imported upstream sources emit style warnings, but the adapter sources emit none.
Logs and source hashes are in `data/qeclean-evaluation/`.

Warm local rechecks, after compiling dependencies, gave these measurements:

| Module | Wall time | Maximum child-process RSS |
|---|---:|---:|
| `Surface225Match` | 11.498 s | 4,553,416 KiB |
| `Surface225` | 3.929 s | 3,919,672 KiB |

A Python wrapper used `time.perf_counter()` and Linux `resource.getrusage(RUSAGE_CHILDREN)`.
It ran each measurement in a fresh process and recorded the exit code.
These are per-module rechecks, not cold-build or aggregate-memory measurements.
Dependency setup is excluded.

Cluster provisioning run `dependency-provisioning` failed during cache download.
The home-directory file count reached about 516,000 against a 500,000 hard limit.
The allocation used about 5.2 GiB and did not reach its 32 GiB memory limit.
Removing this task's incomplete toolchain and package cache reduced the file count to about 470,000.
The original successful kernel-proof workspace remains intact.
The new Slurm script puts caches under its project root.
Future staging belongs in the configured local scratch workspace.

The Python environment now uses `pyproject.toml`, `uv.lock`, and Ruff.
The default Python minor version is 3.13.
The optional C++ accelerator builds inside this project's `.build/` directory.
The build reads the sibling source without modifying `verify/`.

```bash
uv sync --locked
uv run --locked ruff check .
uv run --locked ruff format --check .
uv run --locked pytest -q
uv run --locked --group search python scripts/build_fast_backend.py
uv run --locked python scripts/verify_orbit_k2.py --reps-dir data/reps 262-2-15 422-2-20
```

Ruff and all nine tests pass.
The tests reproduce the original generated Lean data byte for byte.
They also exercise malformed support rejection, exact weighted arithmetic,
integer ceilings, the k=2 median rule, and failure of single-class coverage.
The two saved orbit checks still report bounds 15 and 20 on both sides, matching their witnesses.
These orbit results remain Python certificate checks rather than Lean instance proofs.
A Python workflow now runs lint, formatting, and tests against the pinned sibling checkout.

After the cleanup, `QecBridge/Overlap.lean` adds the first reusable next-step results.
It proves weighted support counting and X/Z bounds for arbitrary logical dimension.
Natural multiplicities represent rational weights after clearing denominators.
The bound uses the strict threshold `(D-1)*cap < total` and assumes complete detector coverage.
It proves that pairing stays constant when representatives differ by the appropriate boundary.
Finite coverage certificates and a concrete higher-k application remain unfinished.
The new generic capstones are included in the guarded axiom audit.
The mathematical overlap and disjointness bounds are prior work, as cited in `RECOMMENDATIONS.md`.

## 12. Main Lean package consolidated

The QECLean-based package now lives directly in `lean/`.
Its package and namespace are `QldpcVerification`.
The former `QecBridge` package and separate `QldpcInput` library are retired.

The independent Lean 4.36 proof moved to `archive/QldpcCert`.
Every proof source, its manifest, and its toolchain file retain the hashes in the original kernel record.
The archived proof sources were not modified during consolidation.
Earlier evaluation records retain their theorem names and proof-source paths.
Published logs omit operational identifiers, and exact copies remain local.

The main package imports no archived modules.
Its `Input/MatrixSpec.lean` defines the submitted matrix claims.
Its generated `Input/Surface225Support.lean` contains only the submitted X and Z rows.
The standard-library generator emits those rows and the QECLean face labels together.
The old pivot and packing certificates remain in the archive.
The overlap theorems continue to use QECLean's `HomologicalCode` directly.

Run from `lean/`:

```bash
lake exe cache get
LEAN_NUM_THREADS=2 lake build
lake env lean QldpcVerification/KernelAudit.lean
```

The project build outputs were cleared before the new build.
The pinned dependency cache was retained.
The package build and all five guarded axiom audits pass.
The concrete theorem is `QldpcVerification.Surface225.parameters`.
The guards still require only `propext`, `Classical.choice`, and `Quot.sound`.
The current records are in `data/lean-evaluation/`.

Ruff and all nine Python tests pass with the updated paths.
Regeneration reproduces the active input modules and the archived certificate data.
The Slurm submission helper is `scripts/cluster/submit.sh`.
It uses `scripts/cluster/verify.sbatch` by default.
The archived Slurm script is `archive/QldpcCert/kernel.sbatch`.

## 13. Finite coverage and the first higher-k Lean proof

On 2026-10-29, `QldpcVerification.Bicycle262.parameters` completed the submitted `262-2-15` proof.
It proves two encoded qubits and both exact CSS distances of 15.
The source JSON SHA256 is `d74c3384fcda674ed724b9ffebfbf16ef029001aa7b303d51a37cc204b25c153`.

`Coverage.lean` proves a reusable finite coverage theorem for any logical dimension.
An identity pairing matrix between detectors and dual witnesses makes the coordinate map onto.
A rank bound then identifies its kernel with the boundary space.
Every nontrivial logical pairs oddly with a detector.
Equal coordinates also identify the same logical class.

`Input/SparseCertificates.lean` connects executable checks to the mathematical matrix claims.
The concrete proof checks commutation, rank lower bounds, detector and witness kernels, identity pairings, and representative class coordinates.
It also checks every weighted per-qubit cap and both stored weight-15 logical witnesses.
The two families on each side have `(total, cap)` values `(3930,258)` and `(131,9)`.
Both satisfy `14*cap < total`.
The proof checks expanded cyclic representatives and assumes no translation theorem.

The local finite-check module completed in 571 seconds.
A sampled local RSS reached 7,340,968 KiB, which is an observation rather than a measured peak.
The local capstone and ten guarded axiom audits passed before the additional surface work.
The audit requires only `propext`, `Classical.choice`, and `Quot.sound`.

Independent cluster run `packing-finite-checks` replayed `Input.Bicycle262Checks` successfully in scratch storage.
It used two CPUs and 32 GiB of reserved memory.
The measured build took 13:08.16 and reached 6,212,504 KiB of maximum process RSS.
The complete allocation took 20:07 and reported 13,074,464 KiB through Slurm, including provisioning and cache work.
The build and allocation measurements have different scopes.
The preserved log is `data/packing-evaluation/bicycle262-checks-cluster.log`.

A local attempt to recognize the larger surface matrices exhausted memory, and the OS killed the Emacs session.
The remaining large evaluations moved to detached Slurm jobs.
The revised surface generator emits an explicit inverse row map instead of a finite-set completeness search.
Lean checks its right-inverse equations and every submitted support equality.
Detachment alone does not enforce a memory limit.
Any further local evaluation needs an enforced memory limit as well.

All thirteen Python tests pass.
They reproduce the bicycle data and finite checker propositions, the additional surface inputs, and the earlier archived input.
They also reject dependent detectors and retain the earlier arithmetic and malformed-input controls.
Ruff lint and formatting pass.
Six Lean negative controls reject malformed commutation, pairings, columns, pivots, weighted caps, and class assignments.
The JSON parser and numerical certificate search remain outside the formal proof.

## 14. Shared surface adapter and full audit

The shared theorem `QldpcVerification.RotatedSurfaceMatch.parameters` transfers the QECLean surface family to submitted matrices.
It accepts an explicit qubit equivalence, row support equalities, and complete row maps on both CSS sides.
The canonical rank and distance theorems then give the submitted code's parameters.
Its weight-transfer proofs are generic in the odd board size.

The submitted `529-1-23` and `961-1-31` instances now pass this adapter.
Their parameter theorems prove one encoded qubit and both exact distances of 23 and 31, respectively.
The generator emits the submitted supports, canonical face labels, and explicit inverse row lookup tables.
Lean proves both right-inverse equations and every original support equality.
It does not infer equivalence from the code names or claimed parameters.

Cluster run `packing-cold-build` began a full replay from the Mathlib cache.
It was deliberately stopped to avoid repeating cold QECLean compilation.
The replacement job reused the local compiled QECLean cache.
Both dependency checkouts were unmodified at commit `fed020a7e6be12825196cbee7bbc1ba56554158c` before transfer.
This replay is not an independent cold rebuild of QECLean.
The earlier `packing-finite-checks` run independently checked the bicycle's finite certificate module on the cluster.

Cluster run `packing-full-replay` completed the full package build and all thirteen guarded axiom audits.
It used two CPUs and 48 GiB of reserved memory.
The timed build took 4:58.47 and reached 6,752,660 KiB of maximum process RSS.
The complete allocation took 5:35 and Slurm reported 11,764,172 KiB.
The surface recognition modules took 35 seconds for 529 qubits and 107 seconds for 961 qubits in this warm replay.
These measurements include filesystem and loading costs and are not cold-build benchmarks.

Every audited capstone depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The completed results include the original surface proof, the weighted bicycle proof, the coverage theorem, and both additional surface proofs.
All thirty recorded proof, manifest, and toolchain hashes match the successful cluster workspace.
All ten historical archive hashes and its audit source hash remain unchanged.
The logs, hashes, input identities, and scheduler accounting are in `data/packing-evaluation/`.

The next mathematical target is the bicycle construction-to-lattice bridge for `562-2-23`.
Its preliminary shortest-vector calculation remains numerical evidence until that bridge and the finite exclusion receive Lean proofs.

## 15. The lattice proof for `562-2-23`

On 2026-10-29, `QldpcVerification.Bicycle562.parameters` completed the submitted `562-2-23` proof.
It proves two encoded qubits and both exact distances of 23.
The separate `rankX` and `rankZ` theorems prove both ranks equal 280.

The original check rows match two edge-incidence graphs on `ZMod 281`.
Their horizontal and vertical steps are `(7,145)` and `(145,7)` on the two CSS sides.
Cyclic translation reduces commutation to 281 kernel-checked base cases.
A generic incidence-rank theorem and the inverse `241*7 = 1 mod 281` prove the rank lower bounds structurally.
Paired block logicals and the existing coverage theorem establish the encoded dimension and exact ranks.
The final proof uses no numerical pivot certificate or orbit packing.

The new graph theorem extracts a detected closed trail from a binary cycle.
Its signed displacement gives a nonzero integer relation with L1 norm at most the cycle weight.
The finite lattice theorem excludes nonzero solutions of `7*u + 145*v = 0 mod 281` with norm at most 22.
It checks `(9,-14)` as a norm-23 relation.
Both original weight-23 logical witnesses pass the kernel and nontriviality checks, so the lower bounds are exact.

The generic bridge requires nonzero direction parity.
The concrete coverage certificate discharges that requirement for this instance.
A general equivalence theorem for every weight-four bicycle code remains outside this milestone.
Other logical-coordinate systems and boundary operations need separate proofs.

The cluster SSH session expired before this work, and a reconnect was requested.
Small proof development and the final replay used detached systemd services with hard cgroup memory limits.
The first combined finite check stopped at its own 5 GiB limit.
Replacing numerical rank evaluation with the structural proof made the final run feasible locally.

The complete sequential package rebuild and all twenty-two guarded axiom checks passed in 280.09 seconds.
The final service used `MemoryMax=5G`, `MemorySwapMax=512M`, one CPU of aggregate bandwidth, and a 1200-second runtime limit.
Maximum child-process RSS was 8,331,048 KiB and includes shared mappings.
The cgroup journal reports a 5 GiB charged-memory peak and a 318 MiB swap peak.
These metrics have different scopes and describe a warm replay.
The nine focused bicycle guards also pass.
The coding-theory capstones use only Lean's three standard axioms, and the closed lattice witness uses none.

The Python suite now contains fifteen tests, including exact input regeneration and rejection of a corrupted bicycle row.
The input JSON parser and the Python rank preflight remain outside the formal proof.
Logs, source hashes, input identity, commands, and resource accounting are in `data/bicycle-evaluation/`.
The project now verifies five submitted instances across two construction families.
The next action is to take stock with the user before another mathematical target starts.

## 16. Cluster operations moved to local configuration

Cluster connection details, scheduler accounts, partitions, site paths, and exact operational records now live under ignored `.local/` storage.
The generic template is `scripts/cluster/config.example.env`.
The submission helper reads `.local/cluster.env`, with an optional `QLDPC_CLUSTER_CONFIG` override.
It passes the local account and partition to Slurm and routes raw output to `.local/cluster/logs/`.
Both the active and archived batch scripts use this configuration.

Published evaluation logs are explicitly sanitized copies.
Descriptive run labels replace scheduler job IDs, and operational fields are omitted from published JSON records.
Exact copies and their identifier mapping remain in the ignored local record directory.
Proof-source hashes, theorem statements, outcomes, and scientific measurements are preserved.
Published log digests were refreshed, and original log digests remain identified in the publication metadata.

The Python suite now has nineteen passing tests.
Four configuration tests use a fake scheduler and make no network calls or real submissions.
Shell syntax, Ruff lint, Ruff formatting, local Git-ignore rules, record hashes, and unchanged Lean proof-source hashes were also checked.
No Lean proof changed during this housekeeping step.

## 17. Tooling fixes after commit review

A subagent review of commit `b7056b3` found three tooling bugs.
The search loaded the sibling accelerator before the local build because the audit helper changed Python's import path.
The cluster script applied its certificate bundle after the first download.
The orbit generator inferred incorrect Lean imports from absolute paths and paths relative to `lean/`.

The search now loads the accelerator before the audit helper.
The cluster script exports the configured certificate bundle before downloading Lean.
The generator resolves imported modules relative to this project's `lean/` directory.
For output outside that directory, `--data-module` specifies the eventual Lean module.
Without that option, the generator rejects an unknown module location before writing either output.

New regression tests reproduced all three bugs before the fixes and pass afterward.
They use competing fake accelerators and a fake download command, with no search, network access, or cluster submission.
The generator tests reproduce the committed data and checker files byte for byte from three path forms.
They also cover an explicit module outside the package and rejection before writing files.
The complete Python suite now contains twenty-seven passing tests.
Ruff and shell syntax checks pass.
The recorded Lean proof sources retain their hashes, and no Lean rebuild was needed for these tooling changes.

## 18. Winding coordinates and an even-length bicycle regression

[Arnault, Gaborit, and Saussay](https://arxiv.org/html/2507.21237v1) provide the mathematical guide for extending the bicycle lattice argument.
The new `Lattice/Winding.lean` proves an integer potential-and-carry identity for every positive cyclic length.
It proves that zero-displacement closed walks have zero winding labels.
Complete logical coverage then makes their binary chains boundaries.
The lattice lower bound accepts these labels instead of requiring nonzero raw direction parity.

The submitted `562-2-23` matrices now use period-aware winding labels on both CSS sides.
Their existing coverage transfers through a proved odd-period identity.
The ranks remain 280 and 280, and both distances remain exactly 23.

`EvenBicycle16` defines `GB(1+x,1+x^3,8)` directly.
It proves two encoded qubits, both ranks 7, and both distances exactly 4.
Lean also proves that a nontrivial eight-edge logical has zero raw block parities but a nonzero winding coordinate.
Both sides have zero-displacement-to-stabilizer theorems.
This regression is separate from the challenge's `16-2-4` JSON, so the submitted-instance count remains five.

The compiled outputs for all five changed or new modules were cleared before the sequential source rebuild.
The dependency caches and other project outputs were retained.
The complete package build and all 33 main guarded axiom checks pass.
The 12 focused winding guards and 9 focused bicycle guards also pass.
Every new guarded result uses only Lean's three standard axioms.

The detached run took 38.52 seconds with a 5 GiB memory cap, 128 MiB swap cap, one CPU, and a 300-second runtime limit.
Maximum child-process RSS was 3,862,012 KiB, while the journal reports a rounded charged-memory peak of 672.4 MiB.
These measurements have different scopes and exclude a cold dependency build.
No cluster job was submitted.
All 27 Python tests, Ruff checks, and shell syntax checks pass.
The archived proof retains its original source and audit hashes.

Current logs, source hashes, exact commands, and scope are in `data/winding-evaluation/`.
The bridge still requires checked incidence recognition, complete detector coverage, and a lattice separation bound.
Parametric construction of the coverage certificates and arbitrary binomial normalization remain the next family-level work.
The paper's separate planar filling argument is not formalized here.

## 19. Parametric bicycle coverage, normalization, and three applications

A subagent reviewed commit `de930ad92c5ee2a4246f91db577a336b74afccd7` before this work and found no substantive mistake.
The reviewer identified a generalization hazard: the naive dual carry and vertical-parity coordinates become dependent when the normalized step is even.
The family proof avoids that hazard through a proved axis swap and vertex inversion.
A Lean regression exhibits a nontrivial weight-three logical missed by those naive coordinates in `GB(1+x,1+x^2,8)`.

`Bicycle/Normalized.lean` defines `GB(1+x,1+x^a,m)` for every positive cyclic length `m` and every natural `a`.
Horizontal and mixed closed walks supply paired winding witnesses.
Structural incidence rank and the square-face relation prove complete logical coverage, both ranks `m-1`, and two encoded qubits.
The same coverage is exposed for the QECLean homological code.
The two distance bounds require only integer lattice separation for `u+a*v = 0 mod m`.
There is no parity restriction on `m` or `a`.

`Bicycle/Normalization.lean` proves normalization by independent monomial shifts and cyclic multiplication by a unit.
It transfers the submitted matrices' ranks, logical predicates, and weight bounds.
The mathematical interface accepts arbitrary surjective row labels.
The current generator recognizes two cyclic blocks in the stored row order, with four distinct positions per row and a unit first binomial difference.
It emits finite four-point row checks, stored witness checks, and a finite lattice exclusion.
Lean checks every obligation without a numerical rank certificate or per-instance coverage certificate.
Connected pairs with neither individual difference a unit remain outside this normalization adapter.

| Application | Normalized `(m,a)` | Ranks X and Z | Exact parameters |
| --- | --- | --- | --- |
| `Bicycle362` | `(181,19)` | 180, 180 | `[[362,2,19]]` |
| `Bicycle262Lattice` | `(131,20)` | 130, 130 | `[[262,2,15]]` |
| `Bicycle562Family` | `(281,101)` | 280, 280 | `[[562,2,23]]` |
| `BicycleEven16Family` | `(8,3)` | 7, 7 | `[[16,2,4]]` |
| `BicycleEvenStep16` | `(8,2)` | 7, 7 | `[[16,2,3]]` |

The 362-qubit proof is a new submitted instance.
The 262-qubit lattice proof agrees with the earlier independent weighted packing proof.
The 562-qubit proof uses the shared family coverage instead of its earlier instance certificate.
Lean proves that the family route for the even-step-three example uses exactly the earlier `EvenBicycle16` matrices.
The project now verifies six submitted instances and two separate construction regressions.
No equivalence with the challenge's `16-2-4` entry is claimed.

The compiled outputs for twenty-eight changed or new build targets were cleared before the sequential source rebuild.
Other project outputs and dependency caches were retained.
The package root builds, and all four guarded audits pass: 67 main targets, 34 family targets, 12 winding targets, and 9 bicycle targets.
Every new guarded result uses only `propext`, `Classical.choice`, and `Quot.sound`.
The earlier closed norm-23 witness remains axiom-free.

The detached run took 224.21 seconds under a 5 GiB memory cap, a 128 MiB swap cap, one CPU of bandwidth, and a 600-second runtime limit.
Maximum child-process RSS was 4,970,568 KiB, including shared mappings.
The journal reports a rounded charged-memory peak of 1.8 GiB and 221.292 seconds of CPU time.
These measurements have different scopes and exclude a cold dependency build.
No cluster job was submitted.
All 40 Python tests pass, as do Ruff and shell syntax checks.
The archived proof retains its original source and audit hashes.

Current logs, exact replay commands, source hashes, and scope are in `data/family-evaluation/`.
The remaining normalization and boundary extensions are listed in `RECOMMENDATIONS.md`.

## 20. Thirteen additional bicycle proofs and joint connectivity

A scan of the recorded challenge checkout found sixteen entries matching the current cyclic two-block row convention.
All sixteen have a unit first binomial difference.
The existing generator and family theorem accepted the thirteen remaining entries without changes.
Each has both exact ranks, two encoded qubits, and both exact distances.

| Submitted input | Normalized `(m,a)` | Both ranks | Both distances |
| --- | --- | --- | --- |
| `4-2-2` | `(2,1)` | 1 | 2 |
| `58-2-7` | `(29,8)` | 28 | 7 |
| `82-2-9` | `(41,9)` | 40 | 9 |
| `100-2-10` | `(50,9)` | 49 | 10 |
| `110-2-10` | `(55,10)` | 54 | 10 |
| `122-2-11` | `(61,11)` | 60 | 11 |
| `170-2-13` | `(85,13)` | 84 | 13 |
| `226-2-15` | `(113,15)` | 112 | 15 |
| `278-2-16` | `(139,30)` | 138 | 16 |
| `298-2-17` | `(149,34)` | 148 | 17 |
| `346-2-18` | `(173,51)` | 172 | 18 |
| `422-2-20` | `(211,20)` | 210 | 20 |
| `454-2-21` | `(227,61)` | 226 | 21 |

The submitted-instance inventory is now nineteen: sixteen bicycle inputs and three surface inputs.
The two earlier exact-distance construction regressions remain separate.
The scan does not classify every row ordering or possible bicycle representation.
All thirteen new source files match the challenge revision pinned in Python CI.
Regeneration tests reproduce the fifty-two additional generated Lean files byte for byte.

`Lattice/Connectivity.lean` proves exact rank for a connected incidence matrix.
It also proves that functions invariant under both cyclic steps are constant when `Nat.gcd (Nat.gcd s t) m = 1`.
The proof uses integer coefficients whose combination of the two steps is one modulo `m`.
Neither individual step needs to be invertible.

`Bicycle/Connected.lean` defines the general two-step incidence and square-face matrices.
It proves commutation, both ranks `m-1`, two encoded qubits, and dimension two for QECLean's first homology.
The general model recovers the existing normalized matrices when the first step is one.
The steps 2 and 3 at cyclic length 6 pass the rank and dimension theorem despite both being nonunits.
The steps 2 and 4 at length 6 admit a nonconstant invariant function, which tests the connectivity hypothesis.
Logical coverage and distance for jointly generating nonunit pairs remain the next mathematical milestone.
The submitted-input generator retains its unit-first restriction.

The instance batch built fifty-two new modules and the changed root sequentially.
Earlier project modules and dependency caches were retained.
The batch and five audits passed in 358.46 seconds under a 5 GiB memory cap and a 128 MiB swap cap.
Maximum child-process RSS was 4,722,368 KiB.
The journal reports a rounded charged-memory peak of 1.6 GiB and 352.969 seconds of CPU time.
The final integration rebuilt the two connectivity modules and the root from cleared outputs, then passed all six audits in 37.69 seconds.
Maximum child-process RSS was 3,832,408 KiB.
The journal reports a rounded charged-memory peak of 632.6 MiB and 37.477 seconds of CPU time.
The main audit contains 118 unique guarded targets.
The focused audits contain 39 batch targets, 12 connectivity targets, 34 family targets, 12 winding targets, and 9 bicycle targets.
These focused counts overlap with the main audit.
All new results use only Lean's standard axioms.
All 53 Python tests, Ruff checks, and shell syntax checks pass.
The archived proof retains its original source and audit hashes.
No cluster job was submitted.

Exact commands, both source identities, logs, input hashes, and resource measurements are in `data/bicycle-batch-evaluation/`.
The earlier family records retain their original source hashes and measurement scopes.

## 21. Complete coverage and distance bounds for jointly generating steps

`Bicycle/PeriodBasis.lean` constructs adapted winding data when `Nat.gcd (Nat.gcd s t) m = 1`.
For a positive common integer factor `g`, the reduced steps `a=s/g` and `b=t/g` admit Bézout coefficients with `a*p+b*q=1`.
The factor `g` is invertible modulo `m`.
The potential uses the corresponding cyclic reindexing, while the walk retains its original edges.
The zero-gcd case forces `m=1` and has a separate valid basis.

The labels record the period carry and the transverse quantity `q*u-p*v` modulo two.
`Bicycle/SignedPaths.lean` constructs walks with any signed integer displacement.
The closed walks with displacements `(m*p,m*q)` and `(b,-a)` have coordinate pairs `(1,0)` and `(0,1)`.
`Bicycle/JointCoverage.lean` combines that identity pairing with the structural rank bound to prove complete logical coverage.
It also exposes the coverage certificate for QECLean's homological code.
Every zero-displacement closed walk is a boundary.

Both CSS sides satisfy the lattice lower bound under joint coprimality.
The bound uses the original congruence `s*u+t*v = 0 mod m` and L1 norm `|u|+|v|`.
The coordinate construction does not replace physical edges by longer paths in the distance calculation.
`Bicycle/JointMatch.lean` transfers ranks, logical predicates, and both bounds to recognized matrix pairs.
Its parameter theorem combines a lattice separation bound with exact-weight logical witnesses.
`Lattice/JointFiniteBound.lean` proves universal integer bounds from finite exclusions with either pair of step coefficients.

| Construction regression | Both ranks | Encoded dimension | Both exact distances |
| --- | --- | --- | --- |
| `(m,s,t)=(6,2,3)` | 5 | 2 | 2 |
| `(m,s,t)=(15,6,10)` | 14 | 2 | 3 |
| Degenerate `(m,s,t)=(1,0,0)` | 0 | 2 | 1 |

The first two examples have nonunit individual steps.
The second also has a common integer factor of two, which tests the scaled potential.
The third tests the zero-gcd branch and the one-vertex model.
Lean proves that a nontrivial weight-five logical in the twelve-qubit example has both naive carry and vertical-parity coordinates zero.
The adapted coordinate proof avoids this failure.
These examples are separate from submitted challenge entries, so the submitted-instance count remains nineteen.

Compiled outputs for the six new modules and the root were cleared before the sequential source rebuild.
Other project outputs and external dependency caches were retained.
The build and all seven guarded audits pass.
The main audit contains 141 unique targets, with 23 focused joint-step targets.
The other focused audits retain their earlier target sets.
Every new guarded result uses only `propext`, `Classical.choice`, and `Quot.sound`.

The detached run took 65.34 seconds under a 5 GiB memory cap, a 128 MiB swap cap, one CPU of bandwidth, and a 300-second runtime limit.
Maximum child-process RSS was 4,064,732 KiB.
The journal reports a rounded charged-memory peak of 886.2 MiB and 64.346 seconds of CPU time.
These measurements have different scopes and exclude a cold dependency build.
No cluster job was submitted.
All 53 Python tests, Ruff checks, and shell syntax checks pass.
The archived proof retains its original source and audit hashes.

Current source identities, logs, commands, and scope are in `data/joint-evaluation/`.
The next mathematical extension is disconnected component decomposition.
The existing Python emitter still requires a unit first difference.

## 22. Disconnected component decomposition and the four-logical-qubit target

For `c=gcd(s,t,m)` and positive `m`, Lean proves a decomposition into `c` identical connected cyclic components.
The reduced cyclic length is `m/c`, and the reduced steps are `s/c,t/c`.
`Bicycle/CyclicComponents.lean` constructs the vertex and qubit bijections and proves both block-matrix identities.
`Bicycle/GcdComponents.lean` proves that the reduced steps jointly generate and derives both ranks `m-c` and encoded dimension `2c`.
The gcd coverage certificate applies to every positive original cyclic length, including zero-step cases.

`Components.lean` proves block-matrix kernel and row-space formulas and arbitrary-k product coverage.
Taking `c` copies of a certificate with `k` coordinates gives a complete certificate with `c*k` coordinates.
`CoverageTransport.lean` transfers these coordinates through a qubit equivalence.
The factorized bicycle model also exposes complete coverage for QECLean's homological code.
No enumeration of nonzero logical classes is needed.

`ComponentDistance.lean` proves exact distance equivalence for a nonempty product of identical components.
A global nontrivial logical has a nontrivial component restriction whose weight is no larger.
A component witness extends by zero with its weight unchanged.
`Bicycle/ComponentParameters.lean` transfers exact equality to both matrix-level CSS distances.
The lattice lower bounds and the rank/parameter interface also transfer from the connected family.

`BicycleComponents24` defines `GB(1+x^4,1+x^6,12)` directly through canonical matrices.
Its block identities prove that it is two copies of the previously verified `GB(1+x^2,1+x^3,6)` construction.
It reuses both exact component distances and proves both ranks 10, four encoded qubits, and both distances exactly 2.
The capstone is `BicycleComponents24.parameters`, with exact parameters `[[24,4,2]]`.
Lean proves complete four-coordinate detection and failure of global block parity on a nontrivial logical.
The single-component recovery and zero-step structural regressions also pass.
The construction is separate from submitted challenge entries, so the submitted-instance count remains nineteen.

An independent Python calculation checked all 24 block-row identities and enumerated both 14-dimensional kernels modulo stabilizers.
It confirms ranks 10 and 10, encoded dimension 4, and both exact distances 2.
This numerical cross-check is separate from the Lean proof.

Compiled outputs for eight new modules and the changed root were cleared before the sequential source rebuild.
Other project outputs and external dependency caches were retained.
The build and all eight guarded audits pass.
The main audit contains 181 unique targets, with forty focused component targets.
Every new guarded result uses only Lean's standard axioms.
The detached run took 76.34 seconds under a 5 GiB memory cap, a 128 MiB swap cap, one CPU of bandwidth, and a 300-second runtime limit.
Maximum child-process RSS was 3,895,816 KiB.
The journal reports a rounded charged-memory peak of 697.6 MiB and 75.510 seconds of CPU time.
These measurements have different scopes and exclude a cold dependency build.
No cluster job was submitted.
All 53 Python tests, Ruff checks, and shell syntax checks pass.
The archived proof retains its original source and audit hashes.

Current source identities, commands, resource records, and scope are in `data/components-evaluation/`.
The remaining boundary and input-recognition work is listed in `RECOMMENDATIONS.md`.

## 23. Independent component review and prior-work assessment

An independent reviewer checked commit `143bf89bd3edb3fe873cc0ab73a3fc8cbd829073` and found no actionable correctness issues.
The review covered all eight new proof modules, the audit additions, and the changed documentation.
It checked arbitrary-k coverage, nonempty-product distance, gcd reduction including zero steps, physical Hamming weights, and both matrix identities for `[[24,4,2]]`.
Separate bounded Python calculations checked 5,524 parameter cases and 200,200 block-row identities.
Exhaustive small-kernel calculations confirmed the concrete distances and the block-parity counterexample.
These numerical checks are independent evidence, outside the Lean proof.

A separate detached replay cleared the same eight module outputs and root output, then rebuilt them sequentially and ran all eight guarded audits.
The replay passed in 76.99 seconds, with maximum child-process RSS of 3,893,852 KiB.
It retained the 5 GiB memory cap, 128 MiB swap cap, one CPU of bandwidth, one Lean thread, and 300-second runtime limit.
The main audit still has 181 unique targets, with forty focused component targets.
All 143 recorded source, manifest, and toolchain files and the three published log hashes matched the milestone record.
The replay reused other project outputs and dependency caches; it was not a cold build.
The historical measurements in `data/components-evaluation/` remain unchanged.

The parallel literature search found explicit prior statements for the component decomposition and distance in Wang–Pryadko (2022), Statement 4.
Panteleev–Kalachev (2021), Proposition 1, supplies the general GB rank and dimension formula specialized here.
Audoux–Couvreur, Proposition 1.10, supplies the general direct-sum homology and distance result.
The arbitrary-k certificate construction has standard dual-basis foundations.
Exact citations, hypothesis distinctions, and guidance for the boundary work are in [RECOMMENDATIONS.md](RECOMMENDATIONS.md#component-decomposition-and-logical-coordinates).
No mathematical novelty or first-formalization claim follows from this search.
Documentation now names `BicycleComponents24.ranks` separately from its parameter theorem.
No Lean source changed during this review.

## Caveats and known limitations

- **Python trust.** Numerical scripts use the sibling `verify/gf2.py` for ranks and logical bases.
  The completed Lean proofs independently accept their certificate obligations.
- **Quadricycle indexing.** The group shapes are inferred from construction
  strings. A wrong guess would fail the automorphism check rather than
  produce a bound.
- **Soundness check scope.** The check built into `orbit_check.py` only
  compares bounds against the stored witnesses.
- **Line check.** The line families are only tried for rows, columns and
  diagonals. Other families of disjoint logicals are not explored.
- **Data age.** The numbers reflect the local checkout. Pull and re-run before
  relying on them.
