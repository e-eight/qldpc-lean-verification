import QldpcVerification.Bicycle.Normalized
import QldpcVerification.Input.MatrixSpec
import Mathlib.Algebra.Group.Units.Equiv

/-! Binomial monomial shifts and multiplication by a cyclic unit are qubit
permutations. They transfer normalized family ranks and distance bounds to
submitted matrices without per-instance coverage or rank certificates.
-/

namespace QldpcVerification.Bicycle

open Matrix Module Input

namespace Normalization

open Normalized

variable {m : ℕ} [NeZero m]

def affine (u : (ZMod m)ˣ) (c : ZMod m) : ZMod m ≃ ZMod m :=
  u.mulLeft.trans (Equiv.addLeft c)

omit [NeZero m] in
@[simp] theorem affine_apply (u : (ZMod m)ˣ) (c v : ZMod m) :
    affine u c v = c + (u : ZMod m) * v := rfl

def reindex (u : (ZMod m)ˣ) (r s : ZMod m) : Edge m ≃ Edge m :=
  Equiv.sumCongr (affine u r) (affine u s)

def rawH (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) : Edge m → ZMod 2 :=
  Pi.single (.inl (v + r)) 1 + Pi.single (.inl (v + r - u)) 1 +
    Pi.single (.inr (v + s)) 1 + Pi.single (.inr (v + s - (u : ZMod m) * (a : ZMod m))) 1

def rawF (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) : Edge m → ZMod 2 :=
  Pi.single (.inl (v - s)) 1 + Pi.single (.inr (v - r + u)) 1 +
    Pi.single (.inl (v - s + (u : ZMod m) * (a : ZMod m))) 1 + Pi.single (.inr (v - r)) 1

theorem pull_single_image {Q R : Type} (e : Q ≃ R) [DecidableEq Q] [DecidableEq R]
    (q : Q) : pull e (Pi.single (e q) (1 : ZMod 2)) = Pi.single q 1 := by
  funext v
  simp [pull, Pi.single_apply, e.apply_eq_iff_eq]

omit [NeZero m] in
theorem pull_rawH (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) :
    pull (reindex u r s) (rawH u r s a (affine u 0 v)) = H a v := by
  rw [rawH, H_explicit]
  simp only [affine_apply, zero_add]
  have h0 : Sum.inl ((u : ZMod m) * v + r) = reindex u r s (.inl v) := by
    simp [reindex, affine]; ring
  have h1 : Sum.inl ((u : ZMod m) * v + r - u) = reindex u r s (.inl (v - 1)) := by
    simp [reindex, affine]; ring
  have h2 : Sum.inr ((u : ZMod m) * v + s) = reindex u r s (.inr v) := by
    simp [reindex, affine]; ring
  have h3 : Sum.inr ((u : ZMod m) * v + s - (u : ZMod m) * (a : ZMod m)) =
      reindex u r s (.inr (v - (a : ZMod m))) := by
    simp [reindex, affine]; ring
  rw [h0, h1, h2, h3]
  simp only [map_add, pull_single_image]

theorem pull_rawF (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) :
    pull (reindex u r s) (rawF u r s a (affine u (r + s) v)) = F a v := by
  rw [rawF, face_explicit]
  simp only [affine_apply]
  have h0 : Sum.inl (r + s + (u : ZMod m) * v - s) = reindex u r s (.inl v) := by
    simp [reindex, affine]; ring
  have h1 : Sum.inr (r + s + (u : ZMod m) * v - r + u) = reindex u r s (.inr (v + 1)) := by
    simp [reindex, affine]; ring
  have h2 : Sum.inl (r + s + (u : ZMod m) * v - s + (u : ZMod m) * (a : ZMod m)) =
      reindex u r s (.inl (v + (a : ZMod m))) := by
    simp [reindex, affine]; ring
  have h3 : Sum.inr (r + s + (u : ZMod m) * v - r) = reindex u r s (.inr v) := by
    simp [reindex, affine]; ring
  rw [h0, h1, h2, h3]
  simp only [map_add, pull_single_image]

end Normalization

/-- Recognition of a submitted matrix pair as one normalized bicycle family member. -/
structure Match (m a n mX mZ : ℕ) [NeZero m] where
  HX : Matrix (Fin mX) (Fin n) (ZMod 2)
  HZ : Matrix (Fin mZ) (Fin n) (ZMod 2)
  qubits : Normalized.Edge m ≃ Fin n
  xRow : Fin mX → ZMod m
  zRow : Fin mZ → ZMod m
  x_surjective : Function.Surjective xRow
  z_surjective : Function.Surjective zRow
  x_rows : ∀ i, pull qubits (HX i) = Normalized.H a (xRow i)
  z_rows : ∀ i, pull qubits (HZ i) = Normalized.F a (zRow i)

namespace Match

variable {m a n mX mZ : ℕ} [NeZero m] (M : Match m a n mX mZ)

def code : CSSCode n mX mZ where
  HX := M.HX
  HZ := M.HZ
  comm := by
    ext i j
    change M.HX i ⬝ᵥ M.HZ j = 0
    rw [← pull_dot M.qubits, M.x_rows, M.z_rows]
    exact congrFun (Normalized.face_cycle a (M.zRow j)) (M.xRow i)

theorem rankX : finrank (ZMod 2) M.code.xStab = m - 1 := by
  have h : Submodule.map (pull M.qubits).toLinearMap M.code.xStab =
      Submodule.span (ZMod 2) (Set.range (Normalized.H a)) :=
    rowspace_pull M.qubits M.HX (Normalized.H a) M.xRow M.x_surjective M.x_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.xStab, h]
  exact (Normalized.ranks a).1

theorem rankZ : finrank (ZMod 2) M.code.zStab = m - 1 := by
  have h : Submodule.map (pull M.qubits).toLinearMap M.code.zStab =
      Submodule.span (ZMod 2) (Set.range (Normalized.F a)) :=
    rowspace_pull M.qubits M.HZ (Normalized.F a) M.zRow M.z_surjective M.z_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.zStab, h]
  exact (Normalized.ranks a).2

theorem encoded_qubits : n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2 := by
  have hn : n = m + m := by simpa [Normalized.Edge, ZMod.card] using (Fintype.card_congr M.qubits).symm
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [rankX, rankZ, hn]
  omega

theorem x_logical_iff (x : Vec n) :
    M.code.IsXLogical x ↔ (Normalized.F a).mulVec (pull M.qubits x) = 0 ∧
      pull M.qubits x ∉ Submodule.span (ZMod 2) (Set.range (Normalized.H a)) := by
  change (M.HZ.mulVec x = 0 ∧ x ∉ Submodule.span (ZMod 2) (Set.range M.HX)) ↔ _
  rw [kernel_pull_iff M.qubits M.HZ _ M.zRow M.z_surjective M.z_rows]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff M.qubits M.HX _ M.xRow M.x_surjective M.x_rows x)).symm

theorem z_logical_iff (x : Vec n) :
    M.code.IsZLogical x ↔ pull M.qubits x ∈ Normalized.cycles a ∧
      pull M.qubits x ∉ Normalized.boundaries a := by
  change (M.HX.mulVec x = 0 ∧ x ∉ Submodule.span (ZMod 2) (Set.range M.HZ)) ↔ _
  change _ ↔ ((Normalized.H a).mulVec (pull M.qubits x) = 0 ∧ _)
  rw [kernel_pull_iff M.qubits M.HX _ M.xRow M.x_surjective M.x_rows]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff M.qubits M.HZ _ M.zRow M.z_surjective M.z_rows x)).symm

theorem lowerX (D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Vec n) (hx : M.code.IsXLogical x) : D ≤ hammingNorm x := by
  obtain ⟨hc, hb⟩ := (M.x_logical_iff x).mp hx
  simpa only [pull_weight] using Normalized.dual_lower a D hbound (pull M.qubits x) hc hb

theorem lowerZ (D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Vec n) (hx : M.code.IsZLogical x) : D ≤ hammingNorm x := by
  obtain ⟨hc, hb⟩ := (M.z_logical_iff x).mp hx
  simpa only [pull_weight] using Normalized.lower a D hbound (pull M.qubits x) hc hb

theorem parameters (D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (hx : ∃ x, M.code.IsXLogical x ∧ hammingNorm x = D)
    (hz : ∃ z, M.code.IsZLogical z ∧ hammingNorm z = D) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2) ∧
      M.code.DistX D ∧ M.code.DistZ D :=
  ⟨M.encoded_qubits, ⟨hx, M.lowerX D hbound⟩, ⟨hz, M.lowerZ D hbound⟩⟩

end Match

/-- Normalize arbitrary monomial offsets and a unit first step, preserving the
original matrices and their row ordering. -/
def matchBinomial {m a n mX mZ : ℕ} [NeZero m]
    (u : (ZMod m)ˣ) (r s : ZMod m)
    (HX : Matrix (Fin mX) (Fin n) (ZMod 2)) (HZ : Matrix (Fin mZ) (Fin n) (ZMod 2))
    (qubits : Normalized.Edge m ≃ Fin n)
    (xRow : Fin mX → ZMod m) (zRow : Fin mZ → ZMod m)
    (hx : Function.Surjective xRow) (hz : Function.Surjective zRow)
    (hX : ∀ i, pull qubits (HX i) = Normalization.rawH u r s a (xRow i))
    (hZ : ∀ i, pull qubits (HZ i) = Normalization.rawF u r s a (zRow i)) :
    Match m a n mX mZ where
  HX := HX
  HZ := HZ
  qubits := (Normalization.reindex u r s).trans qubits
  xRow i := (Normalization.affine u 0).symm (xRow i)
  zRow i := (Normalization.affine u (r + s)).symm (zRow i)
  x_surjective := (Normalization.affine u 0).symm.surjective.comp hx
  z_surjective := (Normalization.affine u (r + s)).symm.surjective.comp hz
  x_rows i := by
    change pull (Normalization.reindex u r s) (pull qubits (HX i)) = _
    rw [hX]
    have h := Normalization.pull_rawH u r s a ((Normalization.affine u 0).symm (xRow i))
    rw [Equiv.apply_symm_apply] at h
    exact h
  z_rows i := by
    change pull (Normalization.reindex u r s) (pull qubits (HZ i)) = _
    rw [hZ]
    have h := Normalization.pull_rawF u r s a ((Normalization.affine u (r + s)).symm (zRow i))
    rw [Equiv.apply_symm_apply] at h
    exact h

end QldpcVerification.Bicycle
