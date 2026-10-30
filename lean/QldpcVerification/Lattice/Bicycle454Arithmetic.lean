import QldpcVerification.Lattice.FiniteBound

namespace QldpcVerification.Lattice.Bicycle454Arithmetic

theorem finite_exclusion : ∀ i j : Fin 41,
    let u : ℤ := (i.val : ℤ) - 20
    let v : ℤ := (j.val : ℤ) - 20
    u.natAbs + v.natAbs ≤ 20 → (u + 61 * v) % 227 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 227) * (u : ZMod 227) + 61 * (v : ZMod 227) = 0) :
    21 ≤ u.natAbs + v.natAbs :=
  QldpcVerification.Lattice.norm_ge_of_finite_exclusion 227 61 21 (by decide)
    finite_exclusion u v hn hc

end QldpcVerification.Lattice.Bicycle454Arithmetic
