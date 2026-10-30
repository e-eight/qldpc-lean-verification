import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle82Arithmetic

theorem finite_exclusion : ∀ i j : Fin 17,
    let u : ℤ := (i.val : ℤ) - 8
    let v : ℤ := (j.val : ℤ) - 8
    u.natAbs + v.natAbs ≤ 8 → (u + 9 * v) % 41 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 41) * (u : ZMod 41) + 9 * (v : ZMod 41) = 0) :
    9 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 41 9 9 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle82Arithmetic
