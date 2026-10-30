import QldpcVerification.Bicycle.JointCoverage
import QldpcVerification.Input.MatrixSpec

/-! Matrix recognition and exact-distance transfer for arbitrary jointly generating steps. -/

namespace QldpcVerification.Bicycle.Connected

open Matrix Module Input

/-- Recognition of a submitted matrix pair as a jointly generating bicycle family member. -/
structure Match (m s t n mX mZ : ℕ) [NeZero m] where
  HX : Matrix (Fin mX) (Fin n) (ZMod 2)
  HZ : Matrix (Fin mZ) (Fin n) (ZMod 2)
  qubits : Normalized.Edge m ≃ Fin n
  xRow : Fin mX → ZMod m
  zRow : Fin mZ → ZMod m
  x_surjective : Function.Surjective xRow
  z_surjective : Function.Surjective zRow
  x_rows : ∀ i, pull qubits (HX i) = H s t (xRow i)
  z_rows : ∀ i, pull qubits (HZ i) = F s t (zRow i)

namespace Match

variable {m s t n mX mZ : ℕ} [NeZero m] (M : Match m s t n mX mZ)

def code : CSSCode n mX mZ where
  HX := M.HX
  HZ := M.HZ
  comm := by
    ext i j
    change M.HX i ⬝ᵥ M.HZ j = 0
    rw [← pull_dot M.qubits, M.x_rows, M.z_rows]
    exact congrFun (face_cycle s t (M.zRow j)) (M.xRow i)

theorem rankX (hc : Nat.gcd (Nat.gcd s t) m = 1) : finrank (ZMod 2) M.code.xStab = m - 1 := by
  have h : Submodule.map (pull M.qubits).toLinearMap M.code.xStab =
      Submodule.span (ZMod 2) (Set.range (H s t)) :=
    rowspace_pull M.qubits M.HX (H s t) M.xRow M.x_surjective M.x_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.xStab, h]
  exact (ranks s t hc).1

theorem rankZ (hc : Nat.gcd (Nat.gcd s t) m = 1) : finrank (ZMod 2) M.code.zStab = m - 1 := by
  have h : Submodule.map (pull M.qubits).toLinearMap M.code.zStab =
      Submodule.span (ZMod 2) (Set.range (F s t)) :=
    rowspace_pull M.qubits M.HZ (F s t) M.zRow M.z_surjective M.z_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.zStab, h]
  exact (ranks s t hc).2

theorem encoded_qubits (hc : Nat.gcd (Nat.gcd s t) m = 1) : n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2 := by
  have hn : n = m + m := by simpa [Normalized.Edge, ZMod.card] using (Fintype.card_congr M.qubits).symm
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [M.rankX hc, M.rankZ hc, hn]
  omega

theorem x_logical_iff (x : Vec n) :
    M.code.IsXLogical x ↔ (F s t).mulVec (pull M.qubits x) = 0 ∧
      pull M.qubits x ∉ Submodule.span (ZMod 2) (Set.range (H s t)) := by
  change (M.HZ.mulVec x = 0 ∧ x ∉ Submodule.span (ZMod 2) (Set.range M.HX)) ↔ _
  rw [kernel_pull_iff M.qubits M.HZ _ M.zRow M.z_surjective M.z_rows]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff M.qubits M.HX _ M.xRow M.x_surjective M.x_rows x)).symm

theorem z_logical_iff (x : Vec n) :
    M.code.IsZLogical x ↔ pull M.qubits x ∈ cycles s t ∧
      pull M.qubits x ∉ boundaries s t := by
  change (M.HX.mulVec x = 0 ∧ x ∉ Submodule.span (ZMod 2) (Set.range M.HZ)) ↔ _
  change _ ↔ ((H s t).mulVec (pull M.qubits x) = 0 ∧ _)
  rw [kernel_pull_iff M.qubits M.HX _ M.xRow M.x_surjective M.x_rows]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff M.qubits M.HZ _ M.zRow M.z_surjective M.z_rows x)).symm

theorem lowerX (D : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Vec n) (hx : M.code.IsXLogical x) : D ≤ hammingNorm x := by
  obtain ⟨hcycle, hb⟩ := (M.x_logical_iff x).mp hx
  simpa only [pull_weight] using dual_lower s t D hc hbound (pull M.qubits x) hcycle hb

theorem lowerZ (D : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Vec n) (hx : M.code.IsZLogical x) : D ≤ hammingNorm x := by
  obtain ⟨hcycle, hb⟩ := (M.z_logical_iff x).mp hx
  simpa only [pull_weight] using lower s t D hc hbound (pull M.qubits x) hcycle hb

theorem parameters (D : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (hx : ∃ x, M.code.IsXLogical x ∧ hammingNorm x = D)
    (hz : ∃ z, M.code.IsZLogical z ∧ hammingNorm z = D) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2) ∧
      M.code.DistX D ∧ M.code.DistZ D :=
  ⟨M.encoded_qubits hc, ⟨hx, M.lowerX D hc hbound⟩, ⟨hz, M.lowerZ D hc hbound⟩⟩

end Match

/-- Canonical finite matrix indexing for construction regressions and family applications. -/
def canonicalMatch (m s t : ℕ) [NeZero m] : Match m s t (m + m) m m where
  HX i q := H s t ((ZMod.finEquiv m) i) (Normalized.qubits.symm q)
  HZ i q := F s t ((ZMod.finEquiv m) i) (Normalized.qubits.symm q)
  qubits := Normalized.qubits
  xRow := ZMod.finEquiv m
  zRow := ZMod.finEquiv m
  x_surjective := (ZMod.finEquiv m).surjective
  z_surjective := (ZMod.finEquiv m).surjective
  x_rows i := by ext e; simp [pull]
  z_rows i := by ext e; simp [pull]

end QldpcVerification.Bicycle.Connected
