import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle422Arithmetic

theorem finite_exclusion : ∀ i j : Fin 39,
    let u : ℤ := (i.val : ℤ) - 19
    let v : ℤ := (j.val : ℤ) - 19
    u.natAbs + v.natAbs ≤ 19 → (u + 20 * v) % 211 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 211) * (u : ZMod 211) + 20 * (v : ZMod 211) = 0) :
    20 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 211 20 20 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle422Arithmetic
