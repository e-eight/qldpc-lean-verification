import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 9v = 0 mod 41`.
The two basis vectors are (-4, 5), (-5, -4); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle82Arithmetic

def basis : BasisSeparation.BasisData 41 9 9 where
  p₁ := -4
  p₂ := 5
  q₁ := -5
  q₂ := -4
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
    (hc : (1 : ZMod 41) * (u : ZMod 41) + 9 * (v : ZMod 41) = 0) :
    9 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 41) * (u : ZMod 41) + 9 * (v : ZMod 41) = 0 ∧
      u.natAbs + v.natAbs = 9 := by
  refine ⟨-4, 5, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (41 : ℤ) ∣ (-4 : ℤ) + 9 * (5 : ℤ) := ⟨1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-4 : ℤ) + 9 * (5 : ℤ)) 41).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 17,
    let u : ℤ := (i.val : ℤ) - 8
    let v : ℤ := (j.val : ℤ) - 8
    u.natAbs + v.natAbs ≤ 8 → (u + 9 * v) % 41 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 8 ≠ 0 ∨ (j.val : ℤ) - 8 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle82Arithmetic
