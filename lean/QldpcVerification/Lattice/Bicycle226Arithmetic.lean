import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 15v = 0 mod 113`.
The two basis vectors are (-7, 8), (-8, -7); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle226Arithmetic

def basis : BasisSeparation.BasisData 113 15 15 where
  p₁ := -7
  p₂ := 8
  q₁ := -8
  q₂ := -7
  pPeriod := 1
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
    (hc : (1 : ZMod 113) * (u : ZMod 113) + 15 * (v : ZMod 113) = 0) :
    15 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 113) * (u : ZMod 113) + 15 * (v : ZMod 113) = 0 ∧
      u.natAbs + v.natAbs = 15 := by
  refine ⟨-7, 8, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (113 : ℤ) ∣ (-7 : ℤ) + 15 * (8 : ℤ) := ⟨1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-7 : ℤ) + 15 * (8 : ℤ)) 113).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 29,
    let u : ℤ := (i.val : ℤ) - 14
    let v : ℤ := (j.val : ℤ) - 14
    u.natAbs + v.natAbs ≤ 14 → (u + 15 * v) % 113 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 14 ≠ 0 ∨ (j.val : ℤ) - 14 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle226Arithmetic
