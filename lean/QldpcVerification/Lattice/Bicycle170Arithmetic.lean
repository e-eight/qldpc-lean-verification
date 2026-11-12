import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 13v = 0 mod 85`.
The two basis vectors are (-6, 7), (-7, -6); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle170Arithmetic

def basis : BasisSeparation.BasisData 85 13 13 where
  p₁ := -6
  p₂ := 7
  q₁ := -7
  q₂ := -6
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
    (hc : (1 : ZMod 85) * (u : ZMod 85) + 13 * (v : ZMod 85) = 0) :
    13 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 85) * (u : ZMod 85) + 13 * (v : ZMod 85) = 0 ∧
      u.natAbs + v.natAbs = 13 := by
  refine ⟨-6, 7, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (85 : ℤ) ∣ (-6 : ℤ) + 13 * (7 : ℤ) := ⟨1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-6 : ℤ) + 13 * (7 : ℤ)) 85).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 25,
    let u : ℤ := (i.val : ℤ) - 12
    let v : ℤ := (j.val : ℤ) - 12
    u.natAbs + v.natAbs ≤ 12 → (u + 13 * v) % 85 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 12 ≠ 0 ∨ (j.val : ℤ) - 12 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle170Arithmetic
