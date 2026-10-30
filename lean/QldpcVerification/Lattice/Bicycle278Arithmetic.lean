import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle278Arithmetic

theorem finite_exclusion : ∀ i j : Fin 31,
    let u : ℤ := (i.val : ℤ) - 15
    let v : ℤ := (j.val : ℤ) - 15
    u.natAbs + v.natAbs ≤ 15 → (u + 30 * v) % 139 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 139) * (u : ZMod 139) + 30 * (v : ZMod 139) = 0) :
    16 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 139 30 16 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle278Arithmetic
