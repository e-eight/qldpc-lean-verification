import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle346Arithmetic

theorem finite_exclusion : ∀ i j : Fin 35,
    let u : ℤ := (i.val : ℤ) - 17
    let v : ℤ := (j.val : ℤ) - 17
    u.natAbs + v.natAbs ≤ 17 → (u + 51 * v) % 173 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 173) * (u : ZMod 173) + 51 * (v : ZMod 173) = 0) :
    18 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 173 51 18 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle346Arithmetic
