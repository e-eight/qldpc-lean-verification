import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.BicycleEvenStep16Arithmetic

theorem finite_exclusion : ∀ i j : Fin 5,
    let u : ℤ := (i.val : ℤ) - 2
    let v : ℤ := (j.val : ℤ) - 2
    u.natAbs + v.natAbs ≤ 2 → (u + 2 * v) % 8 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 8) * (u : ZMod 8) + 2 * (v : ZMod 8) = 0) :
    3 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 8 2 3 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.BicycleEvenStep16Arithmetic
