import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + 61v = 0 mod 227`.
The two basis vectors are (-10, -11), (7, -15); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.Bicycle454Arithmetic

def basis : BasisSeparation.BasisData 227 61 21 where
  p₁ := -10
  p₂ := -11
  q₁ := 7
  q₂ := -15
  pPeriod := -3
  qPeriod := -4
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
    (hc : (1 : ZMod 227) * (u : ZMod 227) + 61 * (v : ZMod 227) = 0) :
    21 ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod 227) * (u : ZMod 227) + 61 * (v : ZMod 227) = 0 ∧
      u.natAbs + v.natAbs = 21 := by
  refine ⟨-10, -11, ?_, ?_, ?_⟩
  · norm_num
  · have hd : (227 : ℤ) ∣ (-10 : ℤ) + 61 * (-11 : ℤ) := ⟨-3, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((-10 : ℤ) + 61 * (-11 : ℤ)) 227).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin 41,
    let u : ℤ := (i.val : ℤ) - 20
    let v : ℤ := (j.val : ℤ) - 20
    u.natAbs + v.natAbs ≤ 20 → (u + 61 * v) % 227 = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - 20 ≠ 0 ∨ (j.val : ℤ) - 20 ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.Bicycle454Arithmetic
