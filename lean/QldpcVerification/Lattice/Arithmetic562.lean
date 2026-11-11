import QldpcVerification.Lattice.Analytic562

/-! The lattice for the submitted weight-four bicycle code has shortest L1 norm 23.
The distance bound uses symbolic basis arithmetic. `finite_exclusion` is retained
as a symbolic corollary for compatibility, without enumerating its finite window. -/

namespace QldpcVerification.Lattice.Arithmetic562

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem finite_exclusion : ∀ a b : Fin 45,
    let u : ℤ := a.val - 22
    let v : ℤ := b.val - 22
    u.natAbs + v.natAbs ≤ 22 → (7 * u + 145 * v) % 281 = 0 → u = 0 ∧ v = 0 := by
  intro a b
  dsimp only
  intro hs hc
  by_contra hn
  have hn' : (a.val : ℤ) - 22 ≠ 0 ∨ (b.val : ℤ) - 22 ≠ 0 := by tauto
  have hbound := Analytic562.norm_ge_23 (Int.dvd_of_emod_eq_zero hc) hn'
  omega

theorem norm_ge_23 {u v : ℤ} (hc : (7 * u + 145 * v) % 281 = 0)
    (hn : u ≠ 0 ∨ v ≠ 0) : 23 ≤ u.natAbs + v.natAbs :=
  Analytic562.norm_ge_23 (Int.dvd_of_emod_eq_zero hc) hn

theorem norm_ge_23_of_cast {u v : ℤ}
    (hc : (7 : ZMod 281) * (u : ZMod 281) + 145 * (v : ZMod 281) = 0)
    (hn : u ≠ 0 ∨ v ≠ 0) : 23 ≤ u.natAbs + v.natAbs := by
  apply norm_ge_23 (hn := hn)
  have h : ((7 * u + 145 * v : ℤ) : ZMod 281) = 0 := by simpa using hc
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

theorem shortest_vector_witness :
    (7 * (9 : ℤ) + 145 * (-14)) % 281 = 0 ∧ (9 : ℤ).natAbs + (-14 : ℤ).natAbs = 23 := by
  decide +kernel

end QldpcVerification.Lattice.Arithmetic562
