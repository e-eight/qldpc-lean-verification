# Assessment and recommendations

Written 2026-10-28. Numbers come from `scripts/audit.py` and
`scripts/candidates.py` run against the local qldpc-challenge checkout at commit
`48f2ee98` (committed 2026-09-24); the saved outputs are in `data/`.

## Bottom line

- **Lean can prove every claim about these codes except the lower-bound half of
  the distance claim.** For a typical d ≤ 14 code, a Lean proof of d ≥ D has to
  contain the same exhaustive search that exact certification already runs. So
  replaying a solver's proof in Lean upgrades trust, not reach.
- **Lean cannot turn the RIS deep checks (1M+ trials) into proofs.** Those
  trials are evidence, and nothing makes them a proof at d ≈ 20 to 70.
- **The exception is structure.** When a code's logicals pack well (surface
  and toric codes, some group codes), a polynomial-size counting certificate
  proves the lower bound outright, far past the solvers' reach. That is the
  most promising direction found, and Lean is a natural checker for it.

## What the repo data shows

- **Board size.** 1,358 codes:
  - 625 certified exact (a cert file with `d_exact` for a current code);
  - 733 witness-backed upper bounds only.
- **The exact tier is solver verdicts, not proofs.** There are 645 cert files,
  and none stores a proof trace:
  - 356 come from scipy/HiGHS (312 MILP + 44 "cutoff IP"). This is a
    floating-point solver whose infeasibility claims cannot be checked.
  - 289 come from CryptoMiniSat (204 from 5.14.7 + 85 from 5.14).
- **The exact envelope stops at d = 14**: [[332,6,14]], [[259,12,14]] and
  [[140,6,14]].
  - Median CryptoMiniSat time (both sides summed) is about 1 s or less up to
    d = 9.
  - At d = 12 / 13 / 14 the medians are 251 s / 119 s / 2,033 s. The slowest is
    2,983 s ([[140,6,14]]).
  - Between d = 10 and d = 14 the median grows about 2.6× per unit of d. The
    samples are small and n and k are confounded.
  - Naively extrapolated: about a week per code at d = 20, centuries at d = 30.
  - The user's own MILP attempt on [[360,12,24]] timed out on every generator
    (repo fieldnote `2026-09-18-bilayer-weight8-leader-audit.md`).
- **No exact certificate has ever been refuted.** 66 codes are named in
  correction commits, and none of them ever had a cert file. Every correction
  so far was an upper bound that the search had not yet tightened:
  [[684,20,72]] → 48, and [[968,18,33]] → 32 after a 300M-trial GPU run.
- **Uncertified codes by distance:** d ≤ 10: 223; d 11–14: 109; d 15–20: 180;
  d 21–40: 146; d > 40: 75.
  - The 332 with d ≤ 14 are within the solvers' reach.
  - Some are tiny ([[8,3,2]], [[12,2,4]]); certification was simply never run
    on them.

## What Lean can do, in three tiers

| Tier | Proves | Reach | Cost |
|---|---|---|---|
| 1. Structure | commutation, exact k, check weight, d ≤ witness, locality class | all codes | probably seconds to minutes per code; unmeasured |
| 2. Exact d via SAT proofs | d = claim | d ≤ 14 in practice: the 625 certified plus up to 332 uncertified | at least the solve time (up to ~50 min) plus proof overhead |
| 3. Packing certificates | d ≥ L, often d = claim | codes whose logicals pack well; needs d_X·d_Z ≤ n | polynomial; seconds |

### Tier 1: structure

State the theorems against a short Mathlib spec:
- k = dim(ker H_Z / rowspace H_X);
- d_X = minimum weight over ker H_Z \ rowspace H_X.

Python emits small certificates for Lean to check:
- **k ≥ claim:** k X-logicals paired one-to-one with k Z-logicals. The repo
  already asks for paired logicals in transversal-gate claims (`circuit.logicals`).
- **k ≤ claim:** rank lower bounds for H_X and H_Z, via echelon certificates.
- **Witness is not a stabilizer:** one opposite-type logical u with ⟨u, w⟩ = 1.
  No rank computation is needed.
- **Speed:** store rows as bit-packed `Nat`. Lean's kernel has big-integer
  xor/and/shift, so these checks should run in the kernel without trusting the
  compiler. That's roughly 10^5–10^6 big-integer operations per code at
  n ≈ 1000, still to be measured.

On its own this adds little: the Python verifier already checks these
properties, and no correction ever involved them. What it buys:
- numpy and the C++ `gf2_fast` extension leave the trusted base;
- "k" and "d" get a formal definition;
- it is the foundation for tiers 2 and 3.

### Tier 2: proof-carrying exact distances

- **Once:** prove the SAT encoding sound (no solution implies d ≥ D). That
  covers the selector clause, whose pairing direction `verify/sat_certify.py`
  says was once wrong; the cardinality counter; and the lex-leader symmetry
  breaking.
- **Per code:** check the solver's UNSAT proof with Lean core's verified LRAT
  checker. lrat-catcher streams those proofs into Lean theorems.
- **Solver choice:** CryptoMiniSat can emit standard clausal proofs of its
  Gauss-Jordan (XOR) reasoning via TBUDDY. Plain CDCL without XOR reasoning is
  weak on parity constraints and may be much slower.
- **Trust:** proofs this large are checked by running the verified checker as
  compiled code, which puts the Lean compiler in the trusted base, as
  `bv_decide` does.
- **Redo:** the 356 HiGHS results would have to be redone.

### Tier 3: packing certificates (see `CERTIFICATES.md`)

- **Idea:** every nontrivial X-logical anticommutes with some Z-logical. So a
  low-overlap family of same-class Z-logicals forces weight on every X-logical
  that anticommutes with that class.
- **Cost:** checking takes polynomial time, and it never searches over
  low-weight vectors.
- **Ceiling:** n/d_Z for d_X, so exactness needs d_X·d_Z ≤ n.
- **Results so far:**
  - all 17 uncertified surface and toric codes with d ≥ 15 are exact;
  - 4 generalized-bicycle codes are exact: [[226,2,15]], [[262,2,15]],
    [[362,2,19]] and [[422,2,20]];
  - the other 9 two-block codes with k = 2 have certified lower bounds of 12
    to 21 (`CHECKS_AND_RESULTS.md` §7). Their remaining gaps look structural:
    the missing classes contain only lopsided logicals;
  - the 3 codes with k = 4 or 6 are partially covered and were not searched.
- **Candidates:** 94 uncertified codes with d ≥ 15 pass the necessary test, 90
  of them not the user's. See `CHECKS_AND_RESULTS.md`.

## Recommended plan, in order

1. **Lean spec and tier-1 checker.** Time kernel checking on [[968,18,32]]
   (the largest of the user's codes) and on one small code. No Lean toolchain
   was installed as of 2026-10-28.
2. **First Lean distance theorems: the 18 packing certificates.**
   - The proof is a double-counting lemma plus per-instance linear-algebra
     checks, all small.
   - That would put exact d = 31 on the board ([[961,1,31]]), well past any
     solver certificate there.
3. **Close the k = 2 orbit certificates.** Done 2026-10-28 (§7 of
   `CHECKS_AND_RESULTS.md`): 3 more codes became exact, the other 9 got lower
   bounds, and no refutations turned up.
4. **Tier-2 pilot.** Run CryptoMiniSat with TBUDDY (or CaDiCaL LRAT), feed the
   proofs to lrat-catcher, and get Lean theorems for two codes with known
   answers: [[100,20,8]] (about 0 s to solve) and [[144,16,10]] (about 15 min).
   Measure the overhead.
5. **Packing search for 2D-local BB and tile codes, including the user's.**
   Those codes pass the necessary test, with ratios 0.57–0.85. Straight lines
   of the layout are not logicals there, so same-class representatives with
   low overlap have to be found.
6. **Upstream.** If steps 2–3 hold up, propose a "packing certificate" tier to
   the maintainers as a GitHub issue. The certificate data is small: the
   representatives, the group generators, and the coverage arithmetic.

## Corrections made during the session

1. **The first formula used one weighting for all classes.** It is capped at
   about (2^(k−1)/(2^k − 1))·n/d_Z, roughly half the ceiling once k ≥ 2,
   because each Z-logical anticommutes with only about half of the classes.
   The fix is one family per class in a spanning set, which restores the n/d_Z
   ceiling. `CERTIFICATES.md` states the corrected version.
2. **"High-rate codes without a layout are hopeless" overgeneralized.** The
   necessary condition is d_X·d_Z ≤ n, roughly d ≲ √n, and many high-rate
   lifted-product and balanced-product codes meet it. What rules out the
   user's 684 family is d far above √n. For expander-like codes the necessary
   condition holds; what is less likely is finding good packings.
3. **The SAT-time extrapolation is crude.** Treat it as an order of magnitude
   only.

## External references (checked 2026-10-28)

- **Lean `bv_decide`** uses proof by reflection: the compiled LRAT check enters
  as an axiom, so the Lean compiler is in the trusted base. Sources: Lean docs
  for `Lean.Elab.Tactic.BVDecide`, and the Lean reference "Validating a Lean
  Proof".
- **lrat-catcher.** S. Szeider, "Streaming LRAT Certificates into Lean
  Theorems", arXiv:2607.00815. It runs Lean core's verified LRAT checker by
  reflection, streams certificates without storing them, and can resume an
  interrupted check. It imported 174 TB of certificates in a scaling experiment.
- **CryptoMiniSat proofs.** M. Soos and R. E. Bryant, "Proof Generation for CDCL
  Solvers Using Gauss-Jordan Elimination", arXiv:2304.04292: CryptoMiniSat with
  TBUDDY emits clausal unsatisfiability proofs for its Gauss-Jordan reasoning.
  Not yet checked: which proof modes current CryptoMiniSat builds support.
- **XLRUP and cake_xlrup.** The CryptoMiniSat README says it emits XLRUP
  proofs checkable by the CakeML-verified `cake_xlrup` (meelgroup/frat-xor).
  See Y. K. Tan et al., "Formally Certified Approximate Model Counting", CAV
  2024. That checker is verified, but its output is not a Lean theorem.
- **Prior work.** A quick search found no Lean formalization of specific
  quantum-code distances. The search was not exhaustive.
