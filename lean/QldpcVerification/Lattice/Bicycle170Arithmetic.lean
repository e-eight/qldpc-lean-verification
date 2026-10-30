import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle170Arithmetic

theorem finite_exclusion : ∀ i j : Fin 25,
    let u : ℤ := (i.val : ℤ) - 12
    let v : ℤ := (j.val : ℤ) - 12
    u.natAbs + v.natAbs ≤ 12 → (u + 13 * v) % 85 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 85) * (u : ZMod 85) + 13 * (v : ZMod 85) = 0) :
    13 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 85 13 13 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle170Arithmetic
