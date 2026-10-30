import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle100Arithmetic

theorem finite_exclusion : ∀ i j : Fin 19,
    let u : ℤ := (i.val : ℤ) - 9
    let v : ℤ := (j.val : ℤ) - 9
    u.natAbs + v.natAbs ≤ 9 → (u + 9 * v) % 50 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 50) * (u : ZMod 50) + 9 * (v : ZMod 50) = 0) :
    10 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 50 9 10 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle100Arithmetic
