import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 2v = 0 mod 8`.
The two basis vectors are (-2, 1), (-2, -3); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.BicycleEvenStep16Arithmetic

def basis : BasisSeparation.BasisData 8 2 3 where
  p₁ := -2
  p₂ := 1
  q₁ := -2
  q₂ := -3
  pPeriod := 0
  qPeriod := -1
  p_relation := by norm_num
  q_relation := by norm_num
  quotient_det := by norm_num
  p_margin := by norm_num
  q_margin := by norm_num
  p_norm := by norm_num
  q_norm := by norm_num
  add_norm := by norm_num
  sub_norm := by norm_num

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 8) * (u : ZMod 8) + 2 * (v : ZMod 8) = 0) :
    3 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 8) * (u : ZMod 8) + 2 * (v : ZMod 8) = 0 ∧
      u.natAbs + v.natAbs = 3 := by
  refine ⟨-2, 1, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (8 : ℤ) ∣ (-2 : ℤ) + 2 * (1 : ℤ) := ⟨0, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-2 : ℤ) + 2 * (1 : ℤ)) 8).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 5,
    let u : ℤ := (i.val : ℤ) - 2
    let v : ℤ := (j.val : ℤ) - 2
    u.natAbs + v.natAbs ≤ 2 → (u + 2 * v) % 8 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 2 ≠ 0 ∨ (j.val : ℤ) - 2 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.BicycleEvenStep16Arithmetic
