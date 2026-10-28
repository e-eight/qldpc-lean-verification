# Lean-based verification of qldpc-challenge codes: working notes

Started 2026-10-28 by Soham Pal (`@e-eight`), working with Claude. The question:
can Lean, or another proof-carrying method, verify the codes on the
qldpc-challenge board, especially their distances? Could that reduce the
reliance on expensive RIS "deep checks" (1M+ trials)?

This directory is a working record for later sessions. It is not part of the
board. The repo is next door at `../qldpc-challenge`, and nothing here should
be copied into it without the user's say-so.

## Where things stand (2026-10-28)

- **Lean can verify everything about a code except the hard half of the
  distance claim**, that no lighter logical exists. For that half, checking a
  solver's proof in Lean adds trust but not reach. Exact certification on the
  board stops at d = 14.
- **The board's 625 "certified exact" entries are solver verdicts, not
  proofs.** None of the 645 cert files stores a proof trace. 356 come from
  scipy/HiGHS (floating-point MILP), 289 from CryptoMiniSat.
- **A cheap, proof-friendly lower-bound certificate exists for some codes:**
  packings of opposite-type logicals (`CERTIFICATES.md`). In exploratory
  checks, 21 codes beyond the d = 14 envelope came out exact:
  - 17 rotated surface and toric codes, d = 15 to 31;
  - 4 generalized-bicycle codes: [[226,2,15]], [[262,2,15]], [[362,2,19]] and
    [[422,2,20]].
- **Certified lower bounds for 9 more k = 2 codes**, from the constrained
  search (`CHECKS_AND_RESULTS.md` §7):
  - the bounds range from d ≥ 12 to d ≥ 21;
  - no refutation was found;
  - the remaining gaps look structural: the missing classes contain only
    lopsided logicals.
- **Lean pilot: the first distance theorem is proved.** `lean/QldpcCert` is a
  Lean project pinned to Mathlib `v4.36.0-rc2`, using the prebuilt Mathlib
  cache (7.3 GB under `.lake/`).
  - `Surface225.distance` proves that the board's [[225,1,15]] has d_X = d_Z =
    15 exactly.
  - It rests on Lean's kernel, plus the compiler for 19 `native_decide` checks
    (`CHECKS_AND_RESULTS.md` §8).
  - The specification is 55 lines, in `QldpcCert/Spec.lean`.
- **None of this is a certification yet.** The board still shows all of these
  codes as upper bounds.

## Files

| Path | Contents |
|---|---|
| `RECOMMENDATIONS.md` | The assessment, the recommended plan (including the Lean pilot), and the corrections made along the way |
| `CERTIFICATES.md` | The packing certificates: statement, soundness proof, ceiling, the three instances used, and what a trusted checker must verify |
| `CHECKS_AND_RESULTS.md` | Every check that was run, with commands, results, controls and caveats |
| `scripts/` | The scripts behind every number. All run in seconds except `class_search.py`, the only search, which has a time budget |
| `data/` | Their saved outputs. `data/reps/` holds the search's certificate representatives |
| `lean/QldpcCert/` | The Lean pilot (Mathlib project). `scripts/gen_lean_instance.py` generates its instance data from the board's JSON |

## How to resume

1. Read `RECOMMENDATIONS.md`, then "Open next steps" below.
2. Check whether the repo has moved. All numbers were computed against the
   local checkout at commit `48f2ee98` (committed 2026-09-24), and the live
   board may differ. Pull, then re-run the scripts from this directory:
   `../qldpc-challenge/.venv/bin/python -I scripts/audit.py` (full list in
   `CHECKS_AND_RESULTS.md`). Set `QLDPC_REPO` if the checkout lives elsewhere.
3. Before quoting a count, compare it with the saved `data/` outputs.

## Open next steps

1. **Lean pilot (in progress; [[225,1,15]] done).**
   - Move the finite checks from `native_decide` into the kernel. This is
     paused (`CHECKS_AND_RESULTS.md` §9): the verified checkers compile, but
     kernel evaluation is too memory-heavy for this workstation. Continue on
     the compute the user provides, and do not build `Surface225` locally.
   - Do [[961,1,31]] with the same template.
   - Prove a general-k packing theorem, for the toric and GB certificates.
   - Then SAT to LRAT to Lean on [[100,20,8]] and [[144,16,10]].
2. **The 9 open k = 2 codes.** The constrained search has run (§7). Their
   remaining gaps look structural, so closing them needs a method other than
   packing. The k = 4 and k = 6 codes have not been searched. Any further
   search needs the user's go-ahead, and any logical lighter than a claim is a
   refutation: save it with the repo's own tools (see the rules below).
3. **Packing search for 2D-local BB and tile codes** (including the user's).
   Straight lines of the layout are not logicals there, so representatives
   have to be found.
4. **Propose a packing-certificate tier to the maintainers** as a GitHub issue.
   CONTRIBUTING.md asks for new certification approaches that way.

## Rules carried over from the repo and the user

- `verify/` in the repo is the board's trust anchor and is hash-pinned in CI.
  Do not edit it; changes there are a maintainer decision.
- Never discard a low-weight logical that a search finds (AGENTS.md). Save it
  through `research/kit/submit.make_submission` and `save_submission`.
- The user asked that heavy computations be proposed before they are run.
