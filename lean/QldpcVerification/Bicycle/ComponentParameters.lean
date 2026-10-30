import QldpcVerification.Bicycle.ComponentBounds
import QldpcVerification.Bicycle.JointMatch
import QldpcVerification.ComponentDistance

/-! Exact matrix parameters and component-distance equivalences. -/

namespace QldpcVerification.Bicycle.Decomposition

open Matrix Module Input

variable (c l : ℕ) [NeZero c] [NeZero l]

theorem distance_iff (a b D : ℕ) :
    Components.Distance (Connected.cycles (m := c * l) (c * a) (c * b))
      (Connected.boundaries (c * a) (c * b)) D ↔
    Components.Distance (Connected.cycles (m := l) a b) (Connected.boundaries a b) D := by
  rw [Components.distance_reindex_iff (edges c l) (cycles_iff c l a b) (boundaries_iff c l a b)]
  exact Components.distance_product_iff _ _ D

theorem dual_distance_iff (a b D : ℕ) :
    Components.Distance (LinearMap.ker (Connected.F (m := c * l) (c * a) (c * b)).mulVecLin)
      (Submodule.span (ZMod 2) (Set.range (Connected.H (c * a) (c * b)))) D ↔
    Components.Distance (LinearMap.ker (Connected.F (m := l) a b).mulVecLin)
      (Submodule.span (ZMod 2) (Set.range (Connected.H a b))) D := by
  rw [Components.distance_reindex_iff (edges c l) (dual_cycles_iff c l a b) (dual_boundaries_iff c l a b)]
  exact Components.distance_product_iff _ _ D

namespace MatrixMatch

variable {c l} {a b n mX mZ : ℕ} (M : Connected.Match (c * l) (c * a) (c * b) n mX mZ)

theorem rankX (hc : Nat.gcd (Nat.gcd a b) l = 1) : finrank (ZMod 2) M.code.xStab = c * (l - 1) := by
  have h := rowspace_pull M.qubits M.HX (Connected.H (c * a) (c * b))
    M.xRow M.x_surjective M.x_rows
  change Submodule.map (pull M.qubits).toLinearMap M.code.xStab = _ at h
  rw [← (pull M.qubits).finrank_map_eq M.code.xStab, h]
  exact (ranks c l a b hc).1

theorem rankZ (hc : Nat.gcd (Nat.gcd a b) l = 1) : finrank (ZMod 2) M.code.zStab = c * (l - 1) := by
  have h := rowspace_pull M.qubits M.HZ (Connected.F (c * a) (c * b))
    M.zRow M.z_surjective M.z_rows
  change Submodule.map (pull M.qubits).toLinearMap M.code.zStab = _ at h
  rw [← (pull M.qubits).finrank_map_eq M.code.zStab, h]
  exact (ranks c l a b hc).2

theorem encoded_qubits (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = c * 2 := by
  have hn : n = c * l + c * l := by
    simpa [Normalized.Edge, ZMod.card] using (Fintype.card_congr M.qubits).symm
  rw [rankX M hc, rankZ M hc, hn, Nat.mul_sub_left_distrib, Nat.mul_one]
  have hl : c ≤ c * l := Nat.le_mul_of_pos_right c (Nat.pos_of_ne_zero (NeZero.ne l))
  omega

theorem lowerX (D : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (a : ZMod l) * (u : ZMod l) + (b : ZMod l) * (v : ZMod l) = 0 → D ≤ u.natAbs + v.natAbs)
    (x : Vec n) (hx : M.code.IsXLogical x) : D ≤ hammingNorm x := by
  obtain ⟨hs, hb⟩ := (M.x_logical_iff x).mp hx
  simpa only [pull_weight] using dual_lower c l a b D hc hbound (pull M.qubits x) hs hb

theorem lowerZ (D : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (a : ZMod l) * (u : ZMod l) + (b : ZMod l) * (v : ZMod l) = 0 → D ≤ u.natAbs + v.natAbs)
    (x : Vec n) (hx : M.code.IsZLogical x) : D ≤ hammingNorm x := by
  obtain ⟨hs, hb⟩ := (M.z_logical_iff x).mp hx
  simpa only [pull_weight] using lower c l a b D hc hbound (pull M.qubits x) hs hb

theorem parameters (D : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (a : ZMod l) * (u : ZMod l) + (b : ZMod l) * (v : ZMod l) = 0 → D ≤ u.natAbs + v.natAbs)
    (hx : ∃ x, M.code.IsXLogical x ∧ hammingNorm x = D)
    (hz : ∃ z, M.code.IsZLogical z ∧ hammingNorm z = D) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = c * 2) ∧
      M.code.DistX D ∧ M.code.DistZ D :=
  ⟨encoded_qubits M hc, ⟨hx, lowerX M D hc hbound⟩, ⟨hz, lowerZ M D hc hbound⟩⟩

end MatrixMatch
end QldpcVerification.Bicycle.Decomposition

namespace QldpcVerification.Bicycle.Connected.Match

open Matrix Module Input

variable {m s t n mX mZ : ℕ} [NeZero m] (M : Match m s t n mX mZ)

theorem x_distance_iff (D : ℕ) : M.code.DistX D ↔
    Components.Distance (LinearMap.ker (F (m := m) s t).mulVecLin)
      (Submodule.span (ZMod 2) (Set.range (H (m := m) s t))) D := by
  have h := Components.distance_reindex_iff M.qubits
    (S := LinearMap.ker (F (m := m) s t).mulVecLin)
    (B := Submodule.span (ZMod 2) (Set.range (H (m := m) s t)))
    (T := LinearMap.ker M.HZ.mulVecLin) (U := M.code.xStab)
    (fun x => kernel_pull_iff M.qubits M.HZ (F s t) M.zRow M.z_surjective M.z_rows x)
    (fun x => rowspace_pull_iff M.qubits M.HX (H s t) M.xRow M.x_surjective M.x_rows x) D
  simpa only [Components.Distance, CSSCode.DistX, CSSCode.IsXLogical, CSSCode.xStab,
    LinearMap.mem_ker, and_assoc, and_imp] using h

theorem z_distance_iff (D : ℕ) : M.code.DistZ D ↔
    Components.Distance (cycles (m := m) s t) (boundaries (m := m) s t) D := by
  have h := Components.distance_reindex_iff M.qubits
    (S := cycles (m := m) s t) (B := boundaries (m := m) s t)
    (T := LinearMap.ker M.HX.mulVecLin) (U := M.code.zStab)
    (fun x => kernel_pull_iff M.qubits M.HX (H s t) M.xRow M.x_surjective M.x_rows x)
    (fun x => rowspace_pull_iff M.qubits M.HZ (F s t) M.zRow M.z_surjective M.z_rows x) D
  simpa only [Components.Distance, CSSCode.DistZ, CSSCode.IsZLogical, CSSCode.zStab,
    cycles, boundaries, LinearMap.mem_ker, and_assoc, and_imp] using h

end QldpcVerification.Bicycle.Connected.Match

namespace QldpcVerification.Bicycle.Decomposition

variable {c l a b n mX mZ q rX rZ : ℕ} [NeZero c] [NeZero l]

theorem matrix_distanceX_iff
    (M : Connected.Match (c * l) (c * a) (c * b) n mX mZ)
    (N : Connected.Match l a b q rX rZ) (D : ℕ) : M.code.DistX D ↔ N.code.DistX D := by
  rw [M.x_distance_iff, N.x_distance_iff]
  exact dual_distance_iff c l a b D

theorem matrix_distanceZ_iff
    (M : Connected.Match (c * l) (c * a) (c * b) n mX mZ)
    (N : Connected.Match l a b q rX rZ) (D : ℕ) : M.code.DistZ D ↔ N.code.DistZ D := by
  rw [M.z_distance_iff, N.z_distance_iff]
  exact distance_iff c l a b D

end QldpcVerification.Bicycle.Decomposition
