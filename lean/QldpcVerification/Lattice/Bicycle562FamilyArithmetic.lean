import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 101v = 0 mod 281`.
The two basis vectors are (9, -14), (13, 11); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle562FamilyArithmetic

def basis : BasisSeparation.BasisData 281 101 23 where
  p₁ := 9
  p₂ := -14
  q₁ := 13
  q₂ := 11
  pPeriod := -5
  qPeriod := 4
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
    (hc : (1 : ZMod 281) * (u : ZMod 281) + 101 * (v : ZMod 281) = 0) :
    23 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 281) * (u : ZMod 281) + 101 * (v : ZMod 281) = 0 ∧
      u.natAbs + v.natAbs = 23 := by
  refine ⟨9, -14, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (281 : ℤ) ∣ (9 : ℤ) + 101 * (-14 : ℤ) := ⟨-5, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((9 : ℤ) + 101 * (-14 : ℤ)) 281).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 45,
    let u : ℤ := (i.val : ℤ) - 22
    let v : ℤ := (j.val : ℤ) - 22
    u.natAbs + v.natAbs ≤ 22 → (u + 101 * v) % 281 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 22 ≠ 0 ∨ (j.val : ℤ) - 22 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle562FamilyArithmetic
