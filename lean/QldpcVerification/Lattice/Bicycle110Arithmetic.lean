import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 10v = 0 mod 55`.
The two basis vectors are (5, 5), (-5, 6); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle110Arithmetic

def basis : BasisSeparation.BasisData 55 10 10 where
  p₁ := 5
  p₂ := 5
  q₁ := -5
  q₂ := 6
  pPeriod := 1
  qPeriod := 1
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
    (hc : (1 : ZMod 55) * (u : ZMod 55) + 10 * (v : ZMod 55) = 0) :
    10 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 55) * (u : ZMod 55) + 10 * (v : ZMod 55) = 0 ∧
      u.natAbs + v.natAbs = 10 := by
  refine ⟨5, 5, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (55 : ℤ) ∣ (5 : ℤ) + 10 * (5 : ℤ) := ⟨1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((5 : ℤ) + 10 * (5 : ℤ)) 55).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 19,
    let u : ℤ := (i.val : ℤ) - 9
    let v : ℤ := (j.val : ℤ) - 9
    u.natAbs + v.natAbs ≤ 9 → (u + 10 * v) % 55 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 9 ≠ 0 ∨ (j.val : ℤ) - 9 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle110Arithmetic
