import QldpcVerification.BicycleEven16Family
import QldpcVerification.BicycleEvenStep16
import QldpcVerification.EvenBicycle16

/-! Regressions for even cyclic length and even second step. -/

namespace QldpcVerification.Bicycle.Regressions

open Matrix Input Input.Sparse Lattice

private theorem code_eq_of_matrices {n mX mZ : ℕ} (C D : CSSCode n mX mZ)
    (hx : C.HX = D.HX) (hz : C.HZ = D.HZ) : C = D := by
  cases C
  cases D
  cases hx
  cases hz
  rfl

/-- The normalized family regression really uses the earlier even example's
matrices, rather than just sharing its n, k, and d. -/
theorem previous_even_code_eq : BicycleEven16Family.code = EvenBicycle16.code := by
  apply code_eq_of_matrices
  · decide +kernel
  · decide +kernel

def badDualTarget (q : Fin 16) : ZMod 8 :=
  EvenBicycle16.source q - if EvenBicycle16.horizontal q then 2 else 1

def badDualLift : WindingData EvenBicycle16.source badDualTarget EvenBicycle16.horizontal :=
  cyclicWindingData EvenBicycle16.source badDualTarget EvenBicycle16.horizontal (-2) (-1) (by
    intro q
    cases h : EvenBicycle16.horizontal q <;> simp [badDualTarget, h])

def badDualDetector (i : Fin 2) (q : Fin 16) : ZMod 2 :=
  if i = 0 then (badDualLift.label q).1 else (badDualLift.label q).2

/-- Reusing (carry, vertical parity) on dual steps (-2,-1) misses this
nontrivial weight-three logical. The family uses the proved axis swap instead. -/
theorem even_step_old_coordinates_fail :
    BicycleEvenStep16.code.IsXLogical (vec 16 BicycleEvenStep16Data.wx) ∧
      ∀ i, vec 16 BicycleEvenStep16Data.wx ⬝ᵥ badDualDetector i = 0 := by
  refine ⟨BicycleEvenStep16Model.wx_logical, ?_⟩
  decide +kernel

end QldpcVerification.Bicycle.Regressions
