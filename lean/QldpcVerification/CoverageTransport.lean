import QldpcVerification.Coverage
import QldpcVerification.Transport

/-! Transport complete logical coordinates along a weight-preserving qubit equivalence. -/

namespace QldpcVerification

open Matrix Module

variable {Q V : Type} [Fintype Q] [Fintype V]

def submodulePullEquiv (e : V ≃ Q)
    {S : Submodule (ZMod 2) (V → ZMod 2)} {T : Submodule (ZMod 2) (Q → ZMod 2)}
    (h : ∀ x, pull e x ∈ S ↔ x ∈ T) : T ≃ₗ[ZMod 2] S where
  toFun x := ⟨pull e x, (h x).mpr x.property⟩
  invFun x := ⟨(pull e).symm x, (h _).mp (by simpa using x.property)⟩
  left_inv x := by apply Subtype.ext; exact (pull e).symm_apply_apply x
  right_inv x := by apply Subtype.ext; exact (pull e).apply_symm_apply x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def CoverageCertificate.reindex
    {S B : Submodule (ZMod 2) (V → ZMod 2)} {T U : Submodule (ZMod 2) (Q → ZMod 2)} {k : ℕ}
    (C : CoverageCertificate S B k) (e : V ≃ Q)
    (hS : ∀ x, pull e x ∈ S ↔ x ∈ T) (hB : ∀ x, pull e x ∈ B ↔ x ∈ U) :
    CoverageCertificate T U k where
  boundary_le x hx := (hS x).mp (C.boundary_le ((hB x).mpr hx))
  detectors i := (pull e).symm (C.detectors i)
  witnesses i := (pull e).symm (C.witnesses i)
  witness_mem i := (hS _).mp (by simpa using C.witness_mem i)
  boundary_zero x hx i := by
    rw [← pull_dot e]
    simp only [LinearEquiv.apply_symm_apply]
    exact C.boundary_zero _ ((hB x).mpr hx) i
  paired i j := by
    rw [← pull_dot e]
    simpa only [LinearEquiv.apply_symm_apply] using C.paired i j
  dimension_bound := by
    rw [(submodulePullEquiv e hS).finrank_eq, (submodulePullEquiv e hB).finrank_eq]
    exact C.dimension_bound

end QldpcVerification
