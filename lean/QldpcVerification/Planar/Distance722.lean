import QldpcVerification.Planar.ChargeCompleteness722
import QldpcVerification.Planar.PhysicalBands

/-! Analytic sector lower bounds for the explicit rectangular 722 model. -/
namespace QldpcVerification.Planar.Distance722

open Commutation CycleSpaces722

/-- Every one of the nine disjoint row pairs meets every nontrivial X support. -/
theorem x_band_nonempty (w : V) (hc : HZ.mulVec w = 0) (hb : w ∉ xStab)
    (i : Fin 9) : ∃ q : Q, w q ≠ 0 ∧
      (q.2.1.val = 2 * i.val ∨ q.2.1.val = 2 * i.val + 1) := by
  classical
  by_contra hempty
  have hz (b : Bool) (r : Fin 19)
      (hr : r.val = 2 * i.val ∨ r.val = 2 * i.val + 1) (j : Fin 19) :
      w (b, (r, j)) = 0 := by
    by_contra hn
    exact hempty ⟨(b, (r, j)), hn, hr⟩
  have hi := i.isLt
  let r₀ : Fin 19 := ⟨2 * i.val, by omega⟩
  let r₁ : Fin 19 := ⟨2 * i.val + 1, by omega⟩
  have h₀ : 2 * i.val + 2 - 2 = r₀.val := by dsimp [r₀]; omega
  have h₁ : 2 * i.val + 2 - 1 = r₁.val := by dsimp [r₁]
  apply ChargeCompleteness722.x_detects w hc hb
  apply CutCharge.row_cut_gap _ _ (k := 2 * i.val + 2) (by omega) (by omega)
    (SyndromeMatrix722.x_cycle_coeff w hc)
  · simpa only [h₀] using StabilizerCharge722.blockEncode_row_zero w false r₀
      (hz false r₀ (Or.inl rfl))
  · simpa only [h₁] using StabilizerCharge722.blockEncode_row_zero w false r₁
      (hz false r₁ (Or.inr rfl))
  · simpa only [h₀] using StabilizerCharge722.blockEncode_row_zero w true r₀
      (hz true r₀ (Or.inl rfl))
  · simpa only [h₁] using StabilizerCharge722.blockEncode_row_zero w true r₁
      (hz true r₁ (Or.inr rfl))

theorem x_lower (w : V) (hc : HZ.mulVec w = 0) (hb : w ∉ xStab) :
    9 ≤ hammingNorm w :=
  PhysicalBands.row_weight_ge_nine w (x_band_nonempty w hc hb)

/-- The nine disjoint reflected column pairs meet every nontrivial Z support. -/
theorem z_band_nonempty (w : V) (hc : HX.mulVec w = 0) (hb : w ∉ zStab)
    (i : Fin 9) : ∃ q : Q, SyndromeMatrix722.reflectPhysical w q ≠ 0 ∧
      (q.2.2.val = 2 * i.val ∨ q.2.2.val = 2 * i.val + 1) := by
  classical
  by_contra hempty
  have hz (b : Bool) (c : Fin 19)
      (hcol : c.val = 2 * i.val ∨ c.val = 2 * i.val + 1) (r : Fin 19) :
      SyndromeMatrix722.reflectPhysical w (b, (r, c)) = 0 := by
    by_contra hn
    exact hempty ⟨(b, (r, c)), hn, hcol⟩
  have hi := i.isLt
  let c₀ : Fin 19 := ⟨2 * i.val, by omega⟩
  let c₁ : Fin 19 := ⟨2 * i.val + 1, by omega⟩
  have h₀ : 2 * i.val + 2 - 2 = c₀.val := by dsimp [c₀]; omega
  have h₁ : 2 * i.val + 2 - 1 = c₁.val := by dsimp [c₁]
  apply ChargeCompleteness722.z_detects w hc hb
  apply CutCharge.column_cut_gap _ _ (k := 2 * i.val + 2) (by omega) (by omega)
    (SyndromeMatrix722.z_cycle_coeff w hc)
  · simpa only [h₀] using StabilizerCharge722.blockEncode_column_zero
      (SyndromeMatrix722.reflectPhysical w) false c₀ (hz false c₀ (Or.inl rfl))
  · simpa only [h₁] using StabilizerCharge722.blockEncode_column_zero
      (SyndromeMatrix722.reflectPhysical w) false c₁ (hz false c₁ (Or.inr rfl))
  · simpa only [h₀] using StabilizerCharge722.blockEncode_column_zero
      (SyndromeMatrix722.reflectPhysical w) true c₀ (hz true c₀ (Or.inl rfl))
  · simpa only [h₁] using StabilizerCharge722.blockEncode_column_zero
      (SyndromeMatrix722.reflectPhysical w) true c₁ (hz true c₁ (Or.inr rfl))

theorem z_lower (w : V) (hc : HX.mulVec w = 0) (hb : w ∉ zStab) :
    9 ≤ hammingNorm w := by
  have he := PhysicalBands.column_weight_ge_nine (SyndromeMatrix722.reflectPhysical w)
    (z_band_nonempty w hc hb)
  simpa only [SyndromeMatrix722.reflectPhysical_weight] using he

end QldpcVerification.Planar.Distance722
