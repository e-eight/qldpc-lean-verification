import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle362Arithmetic

theorem finite_exclusion : ∀ i j : Fin 37,
    let u : ℤ := (i.val : ℤ) - 18
    let v : ℤ := (j.val : ℤ) - 18
    u.natAbs + v.natAbs ≤ 18 → (u + 19 * v) % 181 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 181) * (u : ZMod 181) + 19 * (v : ZMod 181) = 0) :
    19 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 181 19 19 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle362Arithmetic
