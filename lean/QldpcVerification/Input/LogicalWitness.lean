import QldpcVerification.Input.Homological

/-! Opposite-cycle pairings certify that stored logical witnesses are nontrivial. -/

namespace QldpcVerification.Input.CSSCode

open Matrix
open Quantum.Stabilizer.Homological

variable {n mX mZ : ℕ} (C : CSSCode n mX mZ)

theorem x_logical_of_pair (x z : Vec n)
    (hx : C.HZ.mulVec x = 0) (hz : C.HX.mulVec z = 0) (hp : x ⬝ᵥ z = 1) :
    C.IsXLogical x := by
  refine ⟨hx, ?_⟩
  intro hb
  have hb' : x ∈ C.homological.boundaries := by rwa [C.boundaries_eq]
  have hz' : z ∈ C.homological.dualCycles := by
    change C.homological.dualBoundary z = 0
    rwa [C.dualBoundary_eq]
  have h0 := QldpcVerification.Homological.boundary_pairs_zero _ hb' hz'
  exact one_ne_zero (hp.symm.trans h0)

theorem z_logical_of_pair (z x : Vec n)
    (hz : C.HX.mulVec z = 0) (hx : C.HZ.mulVec x = 0) (hp : z ⬝ᵥ x = 1) :
    C.IsZLogical z := by
  refine ⟨hz, ?_⟩
  intro hb
  have hb' : z ∈ C.homological.dualBoundaries := by rwa [C.dualBoundaries_eq]
  have h0 := QldpcVerification.Homological.dual_boundary_pairs_zero _ hb' hx
  exact one_ne_zero (hp.symm.trans h0)

end QldpcVerification.Input.CSSCode
