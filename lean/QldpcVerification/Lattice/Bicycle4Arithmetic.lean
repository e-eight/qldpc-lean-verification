import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 1v = 0 mod 2`.
The two basis vectors are (-1, 1), (-1, -1); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle4Arithmetic

def basis : BasisSeparation.BasisData 2 1 2 where
  p₁ := -1
  p₂ := 1
  q₁ := -1
  q₂ := -1
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
    (hc : (1 : ZMod 2) * (u : ZMod 2) + 1 * (v : ZMod 2) = 0) :
    2 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 2) * (u : ZMod 2) + 1 * (v : ZMod 2) = 0 ∧
      u.natAbs + v.natAbs = 2 := by
  refine ⟨-1, 1, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (2 : ℤ) ∣ (-1 : ℤ) + 1 * (1 : ℤ) := ⟨0, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-1 : ℤ) + 1 * (1 : ℤ)) 2).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 3,
    let u : ℤ := (i.val : ℤ) - 1
    let v : ℤ := (j.val : ℤ) - 1
    u.natAbs + v.natAbs ≤ 1 → (u + 1 * v) % 2 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 1 ≠ 0 ∨ (j.val : ℤ) - 1 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle4Arithmetic
