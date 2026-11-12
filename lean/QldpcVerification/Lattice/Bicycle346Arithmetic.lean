import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 51v = 0 mod 173`.
The two basis vectors are (-11, 7), (-9, -10); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle346Arithmetic

def basis : BasisSeparation.BasisData 173 51 18 where
  p₁ := -11
  p₂ := 7
  q₁ := -9
  q₂ := -10
  pPeriod := 2
  qPeriod := -3
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
    (hc : (1 : ZMod 173) * (u : ZMod 173) + 51 * (v : ZMod 173) = 0) :
    18 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 173) * (u : ZMod 173) + 51 * (v : ZMod 173) = 0 ∧
      u.natAbs + v.natAbs = 18 := by
  refine ⟨-11, 7, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (173 : ℤ) ∣ (-11 : ℤ) + 51 * (7 : ℤ) := ⟨2, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-11 : ℤ) + 51 * (7 : ℤ)) 173).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 35,
    let u : ℤ := (i.val : ℤ) - 17
    let v : ℤ := (j.val : ℤ) - 17
    u.natAbs + v.natAbs ≤ 17 → (u + 51 * v) % 173 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 17 ≠ 0 ∨ (j.val : ℤ) - 17 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle346Arithmetic
