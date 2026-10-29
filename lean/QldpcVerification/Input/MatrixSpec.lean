import Mathlib.Algebra.Field.ZMod
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Specification: CSS codes over 𝔽₂ and their distances

This file is the statement a reader has to trust. Everything else in the package
is proof, checked by Lean.

* A CSS code on `n` qubits is a pair of check matrices `HX`, `HZ` over `ZMod 2`
  with `HX * HZᵀ = 0`.
* An X-type logical is a vector `x` with `HZ *ᵥ x = 0`. It is trivial when it lies
  in the row space of `HX`, i.e. it is a product of X checks.
* `C.DistX d` says that the least weight of a nontrivial X-type logical is exactly
  `d`. `DistZ` mirrors it.

Weight is Mathlib's `hammingNorm`: the number of nonzero coordinates.
-/

namespace QldpcVerification.Input

/-- Vectors on `n` qubits over 𝔽₂. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- A CSS code: X checks `HX`, Z checks `HZ`, and the commutation condition. -/
structure CSSCode (n mX mZ : ℕ) where
  HX : Matrix (Fin mX) (Fin n) (ZMod 2)
  HZ : Matrix (Fin mZ) (Fin n) (ZMod 2)
  comm : HX * HZ.transpose = 0

namespace CSSCode

variable {n mX mZ : ℕ} (C : CSSCode n mX mZ)

/-- X stabilizers: the row space of `HX`. -/
def xStab : Submodule (ZMod 2) (Vec n) := Submodule.span (ZMod 2) (Set.range C.HX)

/-- Z stabilizers: the row space of `HZ`. -/
def zStab : Submodule (ZMod 2) (Vec n) := Submodule.span (ZMod 2) (Set.range C.HZ)

/-- `x` is a nontrivial X-type logical: it commutes with every Z check and is not a
product of X checks. -/
def IsXLogical (x : Vec n) : Prop := C.HZ.mulVec x = 0 ∧ x ∉ C.xStab

/-- `z` is a nontrivial Z-type logical. -/
def IsZLogical (z : Vec n) : Prop := C.HX.mulVec z = 0 ∧ z ∉ C.zStab

/-- The X distance is exactly `d`. -/
def DistX (d : ℕ) : Prop :=
  (∃ x, C.IsXLogical x ∧ hammingNorm x = d) ∧ ∀ x, C.IsXLogical x → d ≤ hammingNorm x

/-- The Z distance is exactly `d`. -/
def DistZ (d : ℕ) : Prop :=
  (∃ z, C.IsZLogical z ∧ hammingNorm z = d) ∧ ∀ z, C.IsZLogical z → d ≤ hammingNorm z

end CSSCode

end QldpcVerification.Input
