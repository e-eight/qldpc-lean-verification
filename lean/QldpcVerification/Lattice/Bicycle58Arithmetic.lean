import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 8v = 0 mod 29`.
The two basis vectors are (-3, 4), (-5, -3); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle58Arithmetic

def basis : BasisSeparation.BasisData 29 8 7 where
  p₁ := -3
  p₂ := 4
  q₁ := -5
  q₂ := -3
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
    (hc : (1 : ZMod 29) * (u : ZMod 29) + 8 * (v : ZMod 29) = 0) :
    7 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 29) * (u : ZMod 29) + 8 * (v : ZMod 29) = 0 ∧
      u.natAbs + v.natAbs = 7 := by
  refine ⟨-3, 4, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (29 : ℤ) ∣ (-3 : ℤ) + 8 * (4 : ℤ) := ⟨1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-3 : ℤ) + 8 * (4 : ℤ)) 29).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 13,
    let u : ℤ := (i.val : ℤ) - 6
    let v : ℤ := (j.val : ℤ) - 6
    u.natAbs + v.natAbs ≤ 6 → (u + 8 * v) % 29 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 6 ≠ 0 ∨ (j.val : ℤ) - 6 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle58Arithmetic
