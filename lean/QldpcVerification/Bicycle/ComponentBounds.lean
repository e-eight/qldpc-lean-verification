import QldpcVerification.Bicycle.CyclicComponents
import QldpcVerification.CoverageTransport

/-! Coverage, ranks, and distance bounds for a cyclic code split into equal connected components. -/

namespace QldpcVerification.Bicycle.Decomposition

open Matrix Module

variable (c l : ℕ) [NeZero c] [NeZero l]

theorem h_rows (a b : ℕ) (v : ZMod (c * l)) :
    pull (edges c l) (Connected.H (c * a) (c * b) v) =
      Components.block (Connected.H a b) ((vertices c l).symm v) := by
  have h := pull_H c l a b ((vertices c l).symm v)
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem f_rows (a b : ℕ) (v : ZMod (c * l)) :
    pull (edges c l) (Connected.F (c * a) (c * b) v) =
      Components.block (Connected.F a b) ((vertices c l).symm v) := by
  have h := pull_F c l a b ((vertices c l).symm v)
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem cycles_iff (a b : ℕ) (x : Connected.Edge (c * l) → ZMod 2) :
    pull (edges c l) x ∈ Components.product (Connected.cycles (m := l) a b) ↔
      x ∈ Connected.cycles (c * a) (c * b) := by
  change pull (edges c l) x ∈ Components.product (LinearMap.ker (Connected.H a b).mulVecLin) ↔ _
  rw [← Components.kernel_block]
  exact kernel_pull_iff (edges c l) _ _ (vertices c l).symm
    (vertices c l).symm.surjective (h_rows c l a b) x

theorem dual_cycles_iff (a b : ℕ) (x : Connected.Edge (c * l) → ZMod 2) :
    pull (edges c l) x ∈ Components.product (LinearMap.ker (Connected.F (m := l) a b).mulVecLin) ↔
      (Connected.F (c * a) (c * b)).mulVec x = 0 := by
  rw [← Components.kernel_block]
  exact kernel_pull_iff (edges c l) _ _ (vertices c l).symm
    (vertices c l).symm.surjective (f_rows c l a b) x

theorem boundaries_iff (a b : ℕ) (x : Connected.Edge (c * l) → ZMod 2) :
    pull (edges c l) x ∈ Components.product (Connected.boundaries (m := l) a b) ↔
      x ∈ Connected.boundaries (c * a) (c * b) := by
  change pull (edges c l) x ∈ Components.product
    (Submodule.span (ZMod 2) (Set.range (Connected.F a b))) ↔ _
  rw [← Components.rowspace_block]
  exact rowspace_pull_iff (edges c l) _ _ (vertices c l).symm
    (vertices c l).symm.surjective (f_rows c l a b) x

theorem dual_boundaries_iff (a b : ℕ) (x : Connected.Edge (c * l) → ZMod 2) :
    pull (edges c l) x ∈ Components.product
      (Submodule.span (ZMod 2) (Set.range (Connected.H (m := l) a b))) ↔
      x ∈ Submodule.span (ZMod 2) (Set.range (Connected.H (c * a) (c * b))) := by
  rw [← Components.rowspace_block]
  exact rowspace_pull_iff (edges c l) _ _ (vertices c l).symm
    (vertices c l).symm.surjective (h_rows c l a b) x

theorem ranks (a b : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (Connected.H (m := c * l) (c * a) (c * b)))) =
      c * (l - 1) ∧
    finrank (ZMod 2) (Connected.boundaries (m := c * l) (c * a) (c * b)) = c * (l - 1) := by
  constructor
  · have h := rowspace_pull (edges c l) (Connected.H (c * a) (c * b))
      (Components.block (Connected.H a b)) (vertices c l).symm
      (vertices c l).symm.surjective (h_rows c l a b)
    rw [Components.rowspace_block] at h
    rw [← (pull (edges c l)).finrank_map_eq _, h, Components.product_finrank, Fintype.card_fin]
    rw [(Connected.ranks a b hc).1]
  · have h := rowspace_pull (edges c l) (Connected.F (c * a) (c * b))
      (Components.block (Connected.F a b)) (vertices c l).symm
      (vertices c l).symm.surjective (f_rows c l a b)
    rw [Components.rowspace_block] at h
    change finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (Connected.F _ _))) = _
    rw [← (pull (edges c l)).finrank_map_eq _, h, Components.product_finrank, Fintype.card_fin]
    rw [(Connected.ranks a b hc).2]

theorem encoded_qubits (a b : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    (c * l + c * l) -
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (Connected.H (m := c * l) (c * a) (c * b)))) -
      finrank (ZMod 2) (Connected.boundaries (m := c * l) (c * a) (c * b)) = c * 2 := by
  obtain ⟨hx, hz⟩ := ranks c l a b hc
  rw [hx, hz, Nat.mul_sub_left_distrib, Nat.mul_one]
  have hl : c ≤ c * l := Nat.le_mul_of_pos_right c (Nat.pos_of_ne_zero (NeZero.ne l))
  omega

noncomputable def coverage (a b : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    CoverageCertificate (Connected.cycles (m := c * l) (c * a) (c * b))
      (Connected.boundaries (c * a) (c * b)) (c * 2) :=
  (Components.coverage (c := c) (Connected.coverage a b hc)).reindex
    (edges c l) (cycles_iff c l a b) (boundaries_iff c l a b)

noncomputable def complex_coverage (a b : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    CoverageCertificate (Connected.complex (m := c * l) (c * a) (c * b)).cycles
      (Connected.complex (c * a) (c * b)).boundaries (c * 2) := by
  rw [Connected.complex_cycles, Connected.complex_boundaries]
  exact coverage c l a b hc

theorem lower (a b D : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (a : ZMod l) * (u : ZMod l) + (b : ZMod l) * (v : ZMod l) = 0 → D ≤ u.natAbs + v.natAbs)
    (x : Connected.Edge (c * l) → ZMod 2)
    (hx : x ∈ Connected.cycles (c * a) (c * b))
    (hb : x ∉ Connected.boundaries (c * a) (c * b)) : D ≤ hammingNorm x := by
  have hs := (cycles_iff c l a b x).mpr hx
  have hn : pull (edges c l) x ∉ Components.product (Connected.boundaries a b) :=
    fun h => hb ((boundaries_iff c l a b x).mp h)
  simpa only [pull_weight] using
    Components.lower D (Connected.lower a b D hc hbound) (pull (edges c l) x) hs hn

theorem dual_lower (a b D : ℕ) (hc : Nat.gcd (Nat.gcd a b) l = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (a : ZMod l) * (u : ZMod l) + (b : ZMod l) * (v : ZMod l) = 0 → D ≤ u.natAbs + v.natAbs)
    (x : Connected.Edge (c * l) → ZMod 2)
    (hx : (Connected.F (c * a) (c * b)).mulVec x = 0)
    (hb : x ∉ Submodule.span (ZMod 2) (Set.range (Connected.H (c * a) (c * b)))) :
    D ≤ hammingNorm x := by
  have hs := (dual_cycles_iff c l a b x).mpr hx
  have hn : pull (edges c l) x ∉ Components.product
      (Submodule.span (ZMod 2) (Set.range (Connected.H a b))) :=
    fun h => hb ((dual_boundaries_iff c l a b x).mp h)
  simpa only [pull_weight] using Components.lower D
    (Connected.dual_lower a b D hc hbound) (pull (edges c l) x) hs hn

noncomputable def lift (i : Fin c) (x : Connected.Edge l → ZMod 2) : Connected.Edge (c * l) → ZMod 2 :=
  (pull (edges c l)).symm (Components.extend i x)

theorem lift_weight (i : Fin c) (x : Connected.Edge l → ZMod 2) :
    hammingNorm (lift c l i x) = hammingNorm x := by
  rw [← pull_weight (edges c l)]
  simp [lift, Components.extend_weight]

theorem lift_logical (a b : ℕ) (i : Fin c) (x : Connected.Edge l → ZMod 2)
    (hx : x ∈ Connected.cycles a b) (hb : x ∉ Connected.boundaries a b) :
    lift c l i x ∈ Connected.cycles (c * a) (c * b) ∧
      lift c l i x ∉ Connected.boundaries (c * a) (c * b) := by
  have hs := Components.extend_nonboundary i x hx hb
  constructor
  · apply (cycles_iff c l a b _).mp
    simpa [lift] using hs.1
  · intro h
    apply hs.2
    simpa [lift] using (boundaries_iff c l a b _).mpr h

end QldpcVerification.Bicycle.Decomposition
