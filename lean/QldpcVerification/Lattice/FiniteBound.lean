import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! A finite L1 exclusion window certifies an arbitrary-integer lattice bound. -/

namespace QldpcVerification.Lattice

theorem norm_ge_of_finite_exclusion (m a D : ℕ) (hD : 0 < D)
    (hf : ∀ i j : Fin (2 * (D - 1) + 1),
      let u : ℤ := i.val - (D - 1 : ℕ)
      let v : ℤ := j.val - (D - 1 : ℕ)
      u.natAbs + v.natAbs ≤ D - 1 → (u + (a : ℤ) * v) % m = 0 → u = 0 ∧ v = 0)
    (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0) :
    D ≤ u.natAbs + v.natAbs := by
  by_contra h
  have hs : u.natAbs + v.natAbs ≤ D - 1 := by omega
  let i : Fin (2 * (D - 1) + 1) := ⟨(u + (D - 1 : ℕ)).toNat, by omega⟩
  let j : Fin (2 * (D - 1) + 1) := ⟨(v + (D - 1 : ℕ)).toNat, by omega⟩
  have hi : (i.val : ℤ) - (D - 1 : ℕ) = u := by dsimp [i]; omega
  have hj : (j.val : ℤ) - (D - 1 : ℕ) = v := by dsimp [j]; omega
  have he : (u + (a : ℤ) * v) % m = 0 := by
    apply Int.emod_eq_zero_of_dvd
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa using hc
  have hh := hf i j
  dsimp only at hh
  rw [hi, hj] at hh
  obtain ⟨rfl, rfl⟩ := hh hs he
  simp at hn

end QldpcVerification.Lattice
