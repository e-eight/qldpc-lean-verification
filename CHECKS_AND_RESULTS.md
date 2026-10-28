# Checks and results

All checks below were run on 2026-10-28 against the local qldpc-challenge
checkout at commit `48f2ee98` (committed 2026-09-24). They were run from this
directory with the checkout's interpreter:

    PY=../qldpc-challenge/.venv/bin/python
    $PY -I scripts/<script>.py ...

Each script runs in seconds, and none runs a distance search. Saved outputs
are in `data/`.

**Status:** everything here is exploratory. These scripts are not the board's
verifier, and the board still shows every code below as an upper bound.

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

## 9. Moving the finite checks into the kernel (in progress, paused)

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

## Caveats and known limitations

- **Trust.** The scripts rely on the repo's `verify/gf2.py` for ranks and
  logical bases. The independent path in §5 avoids the logical bases.
- **Quadricycle indexing.** The group shapes are inferred from construction
  strings. A wrong guess would fail the automorphism check rather than
  produce a bound.
- **Soundness check scope.** The check built into `orbit_check.py` only
  compares bounds against the stored witnesses.
- **Line check.** The line families are only tried for rows, columns and
  diagonals. Other families of disjoint logicals are not explored.
- **Data age.** The numbers reflect the local checkout. Pull and re-run before
  relying on them.
