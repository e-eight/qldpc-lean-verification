import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle226Arithmetic

theorem finite_exclusion : ∀ i j : Fin 29,
    let u : ℤ := (i.val : ℤ) - 14
    let v : ℤ := (j.val : ℤ) - 14
    u.natAbs + v.natAbs ≤ 14 → (u + 15 * v) % 113 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 113) * (u : ZMod 113) + 15 * (v : ZMod 113) = 0) :
    15 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 113 15 15 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle226Arithmetic
