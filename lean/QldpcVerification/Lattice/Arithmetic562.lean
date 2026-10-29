import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! The lattice for the submitted weight-four bicycle code has shortest L1 norm 23. -/

namespace QldpcVerification.Lattice.Arithmetic562

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finite_exclusion : ∀ a b : Fin 45,
    let u : ℤ := a.val - 22
    let v : ℤ := b.val - 22
    u.natAbs + v.natAbs ≤ 22 → (7 * u + 145 * v) % 281 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem norm_ge_23 {u v : ℤ} (hc : (7 * u + 145 * v) % 281 = 0)
    (hn : u ≠ 0 ∨ v ≠ 0) : 23 ≤ u.natAbs + v.natAbs := by
  by_contra h
  have hs : u.natAbs + v.natAbs ≤ 22 := by omega
  have hub : -(22 : ℤ) ≤ u ∧ u ≤ 22 := by omega
  have hvb : -(22 : ℤ) ≤ v ∧ v ≤ 22 := by omega
  let a : Fin 45 := ⟨(u + 22).toNat, by omega⟩
  let b : Fin 45 := ⟨(v + 22).toNat, by omega⟩
  have ha : (a.val : ℤ) - 22 = u := by dsimp [a]; omega
  have hb : (b.val : ℤ) - 22 = v := by dsimp [b]; omega
  have hh := finite_exclusion a b
  dsimp only at hh
  rw [ha, hb] at hh
  obtain ⟨rfl, rfl⟩ := hh hs hc
  simp at hn

theorem norm_ge_23_of_cast {u v : ℤ}
    (hc : (7 : ZMod 281) * (u : ZMod 281) + 145 * (v : ZMod 281) = 0)
    (hn : u ≠ 0 ∨ v ≠ 0) : 23 ≤ u.natAbs + v.natAbs := by
  apply norm_ge_23 (hn := hn)
  have h : ((7 * u + 145 * v : ℤ) : ZMod 281) = 0 := by simpa using hc
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

theorem shortest_vector_witness :
    (7 * (9 : ℤ) + 145 * (-14)) % 281 = 0 ∧ (9 : ℤ).natAbs + (-14 : ℤ).natAbs = 23 := by
  decide +kernel

end QldpcVerification.Lattice.Arithmetic562
