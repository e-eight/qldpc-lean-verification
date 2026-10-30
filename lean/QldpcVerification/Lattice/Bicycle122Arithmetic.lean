import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle122Arithmetic

theorem finite_exclusion : ∀ i j : Fin 21,
    let u : ℤ := (i.val : ℤ) - 10
    let v : ℤ := (j.val : ℤ) - 10
    u.natAbs + v.natAbs ≤ 10 → (u + 11 * v) % 61 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 61) * (u : ZMod 61) + 11 * (v : ZMod 61) = 0) :
    11 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 61 11 11 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle122Arithmetic
