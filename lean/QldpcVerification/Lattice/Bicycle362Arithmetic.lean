import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 19v = 0 mod 181`.
The two basis vectors are (-9, 10), (-10, -9); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle362Arithmetic

def basis : BasisSeparation.BasisData 181 19 19 where
  p₁ := -9
  p₂ := 10
  q₁ := -10
  q₂ := -9
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
    (hc : (1 : ZMod 181) * (u : ZMod 181) + 19 * (v : ZMod 181) = 0) :
    19 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 181) * (u : ZMod 181) + 19 * (v : ZMod 181) = 0 ∧
      u.natAbs + v.natAbs = 19 := by
  refine ⟨-9, 10, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (181 : ℤ) ∣ (-9 : ℤ) + 19 * (10 : ℤ) := ⟨1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-9 : ℤ) + 19 * (10 : ℤ)) 181).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 37,
    let u : ℤ := (i.val : ℤ) - 18
    let v : ℤ := (j.val : ℤ) - 18
    u.natAbs + v.natAbs ≤ 18 → (u + 19 * v) % 181 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 18 ≠ 0 ∨ (j.val : ℤ) - 18 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle362Arithmetic
