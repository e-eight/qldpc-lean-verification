import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 30v = 0 mod 139`.
The two basis vectors are (-8, -9), (11, -5); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle278Arithmetic

def basis : BasisSeparation.BasisData 139 30 16 where
  p₁ := -8
  p₂ := -9
  q₁ := 11
  q₂ := -5
  pPeriod := -2
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
    (hc : (1 : ZMod 139) * (u : ZMod 139) + 30 * (v : ZMod 139) = 0) :
    16 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 139) * (u : ZMod 139) + 30 * (v : ZMod 139) = 0 ∧
      u.natAbs + v.natAbs = 16 := by
  refine ⟨11, -5, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (139 : ℤ) ∣ (11 : ℤ) + 30 * (-5 : ℤ) := ⟨-1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((11 : ℤ) + 30 * (-5 : ℤ)) 139).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 31,
    let u : ℤ := (i.val : ℤ) - 15
    let v : ℤ := (j.val : ℤ) - 15
    u.natAbs + v.natAbs ≤ 15 → (u + 30 * v) % 139 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 15 ≠ 0 ∨ (j.val : ℤ) - 15 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle278Arithmetic
