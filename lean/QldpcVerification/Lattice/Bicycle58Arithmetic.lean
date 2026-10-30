import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle58Arithmetic

theorem finite_exclusion : ∀ i j : Fin 13,
    let u : ℤ := (i.val : ℤ) - 6
    let v : ℤ := (j.val : ℤ) - 6
    u.natAbs + v.natAbs ≤ 6 → (u + 8 * v) % 29 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 29) * (u : ZMod 29) + 8 * (v : ZMod 29) = 0) :
    7 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 29 8 7 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle58Arithmetic
