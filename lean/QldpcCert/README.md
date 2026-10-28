# QldpcCert: Lean proofs of qLDPC code distances

The Lean pilot from `../../RECOMMENDATIONS.md`. Mathlib is pinned at
`v4.36.0-rc2` (toolchain `leanprover/lean4:v4.36.0-rc2`) and uses the prebuilt
Mathlib cache.

## Build

    export PATH="$HOME/.elan/bin:$PATH"
    lake build                 # everything, about 15 s once the cache is in place
    lake env lean <file>.lean  # check one file

## Files

| File | Role |
|---|---|
| `QldpcCert/Spec.lean` | **The statement to trust.** CSS code over 𝔽₂, nontrivial logicals, `DistX d`, `DistZ d` |
| `QldpcCert/Certificates.lean` | General lemmas, proved once for every code: kernel ⟂ row space, double counting, rank lower bounds from pivot certificates, rank–nullity, the k = 1 packing theorem, and the X↔Z swap |
| `QldpcCert/Surface225Data.lean` | Generated from `codes/225-1-15.json` by `../../scripts/gen_lean_instance.py`: bitmask data and certificates |
| `QldpcCert/Surface225.lean` | `Surface225.distance : code.DistX 15 ∧ code.DistZ 15` |

## What `Surface225.distance` rests on

`#print axioms Surface225.distance` lists Lean's three standard axioms and the
`native_decide` evaluations, with no `sorryAx`. The general theorem
`CSSCode.distX_ge_of_packing` uses only the three standard axioms.

So the trusted base is:
- Lean's kernel;
- Lean's compiler, for the 19 finite checks run by `native_decide` (the same
  trade `bv_decide` makes);
- `Spec.lean`;
- the generated data file matching the board's JSON. Regenerate and diff to
  check this.

Next: move the finite checks into the kernel, using bitmask checkers with
correctness proofs, so the compiler leaves the trusted base.
