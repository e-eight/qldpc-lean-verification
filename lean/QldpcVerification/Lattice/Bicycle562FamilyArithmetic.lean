import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle562FamilyArithmetic

theorem finite_exclusion : ∀ i j : Fin 45,
    let u : ℤ := (i.val : ℤ) - 22
    let v : ℤ := (j.val : ℤ) - 22
    u.natAbs + v.natAbs ≤ 22 → (u + 101 * v) % 281 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 281) * (u : ZMod 281) + 101 * (v : ZMod 281) = 0) :
    23 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 281 101 23 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle562FamilyArithmetic
