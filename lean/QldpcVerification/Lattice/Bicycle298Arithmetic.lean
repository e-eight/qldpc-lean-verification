import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle298Arithmetic

theorem finite_exclusion : ∀ i j : Fin 33,
    let u : ℤ := (i.val : ℤ) - 16
    let v : ℤ := (j.val : ℤ) - 16
    u.natAbs + v.natAbs ≤ 16 → (u + 34 * v) % 149 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 149) * (u : ZMod 149) + 34 * (v : ZMod 149) = 0) :
    17 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 149 34 17 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle298Arithmetic
