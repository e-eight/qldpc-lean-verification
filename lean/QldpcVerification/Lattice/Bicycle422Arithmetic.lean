import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 20v = 0 mod 211`.
The two basis vectors are (-9, 11), (-11, -10); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle422Arithmetic

def basis : BasisSeparation.BasisData 211 20 20 where
  p₁ := -9
  p₂ := 11
  q₁ := -11
  q₂ := -10
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
    (hc : (1 : ZMod 211) * (u : ZMod 211) + 20 * (v : ZMod 211) = 0) :
    20 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 211) * (u : ZMod 211) + 20 * (v : ZMod 211) = 0 ∧
      u.natAbs + v.natAbs = 20 := by
  refine ⟨-9, 11, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (211 : ℤ) ∣ (-9 : ℤ) + 20 * (11 : ℤ) := ⟨1, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-9 : ℤ) + 20 * (11 : ℤ)) 211).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 39,
    let u : ℤ := (i.val : ℤ) - 19
    let v : ℤ := (j.val : ℤ) - 19
    u.natAbs + v.natAbs ≤ 19 → (u + 20 * v) % 211 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 19 ≠ 0 ∨ (j.val : ℤ) - 19 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle422Arithmetic
