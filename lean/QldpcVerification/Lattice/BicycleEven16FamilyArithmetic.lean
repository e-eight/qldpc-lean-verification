import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.BicycleEven16FamilyArithmetic

theorem finite_exclusion : ∀ i j : Fin 7,
    let u : ℤ := (i.val : ℤ) - 3
    let v : ℤ := (j.val : ℤ) - 3
    u.natAbs + v.natAbs ≤ 3 → (u + 3 * v) % 8 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 8) * (u : ZMod 8) + 3 * (v : ZMod 8) = 0) :
    4 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 8 3 4 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.BicycleEven16FamilyArithmetic
