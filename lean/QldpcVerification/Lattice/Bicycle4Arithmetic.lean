import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle4Arithmetic

theorem finite_exclusion : ∀ i j : Fin 3,
    let u : ℤ := (i.val : ℤ) - 1
    let v : ℤ := (j.val : ℤ) - 1
    u.natAbs + v.natAbs ≤ 1 → (u + 1 * v) % 2 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 2) * (u : ZMod 2) + 1 * (v : ZMod 2) = 0) :
    2 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 2 1 2 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle4Arithmetic
