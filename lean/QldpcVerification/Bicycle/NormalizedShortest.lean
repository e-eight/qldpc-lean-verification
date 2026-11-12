import QldpcVerification.Bicycle.Normalization
import QldpcVerification.Bicycle.ShortestVector

/-! The normalized submitted-matrix interface uses the symbolic shortest-relation
construction for both physical logical witnesses. -/

namespace QldpcVerification.Bicycle.Match

open Module

variable {m a n mX mZ : ℕ} [NeZero m] (M : Bicycle.Match m a n mX mZ)

/-- View the normalized steps as the jointly generating pair `(1,a)`. -/
def connected : Connected.Match m 1 a n mX mZ where
  HX := M.HX
  HZ := M.HZ
  qubits := M.qubits
  xRow := M.xRow
  zRow := M.zRow
  x_surjective := M.x_surjective
  z_surjective := M.z_surjective
  x_rows i := by rw [Connected.normalized_H]; exact M.x_rows i
  z_rows i := by rw [Connected.normalized_F]; exact M.z_rows i

@[simp] theorem connected_code : M.connected.code = M.code := rfl

/-- Exact parameters from a lattice lower bound and one minimizing integer pair.
The generic cycle construction supplies both physical upper witnesses. -/
theorem parameters_of_shortest (D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (hwitness : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
      (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0 ∧
        u.natAbs + v.natAbs = D) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2) ∧
      M.code.DistX D ∧ M.code.DistZ D := by
  exact M.connected.parameters_of_shortest D (by simp)
    (by simpa only [Nat.cast_one] using hbound)
    (by simpa only [Nat.cast_one] using hwitness)

/-- Every recognized normalized code has its lattice minimum as both distances. -/
theorem parameters_minimum :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2) ∧
      M.code.DistX (Connected.minimumNorm (m := m) 1 a) ∧
      M.code.DistZ (Connected.minimumNorm (m := m) 1 a) :=
  M.connected.parameters_minimum (by simp)

end QldpcVerification.Bicycle.Match
