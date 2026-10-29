import QldpcVerification.Transport
import QldpcVerification.Input.MatrixSpec
import QEC.Stabilizer.Codes.RotatedSurface.Distance

/-! A reusable recognition certificate transfers the entire rotated surface family. -/

namespace QldpcVerification

open Matrix Module Input
open Quantum.Stabilizer.Lattice.RotatedSurface
open Quantum.StabilizerGroup.RotatedSurfaceCodeN
open Quantum.Stabilizer.Homological.HomologicalCode

structure RotatedSurfaceMatch (L n mX mZ : ℕ) where
  HX : Matrix (Fin mX) (Fin n) (ZMod 2)
  HZ : Matrix (Fin mZ) (Fin n) (ZMod 2)
  qubits : VtxIdx L ≃ Fin n
  xFace : Fin mX → XFaceIdx L
  zFace : Fin mZ → ZFaceIdx L
  x_surjective : Function.Surjective xFace
  z_surjective : Function.Surjective zFace
  x_rows : ∀ i, pull qubits (HX i) = stabXMatrix L (xFace i)
  z_rows : ∀ i, pull qubits (HZ i) = stabZMatrix L (zFace i)

namespace RotatedSurfaceMatch

variable {L n mX mZ : ℕ} [Fact (Odd L)] [Fact (3 ≤ L)]
variable (M : RotatedSurfaceMatch L n mX mZ)

theorem canonical_comm (xf : XFaceIdx L) (zf : ZFaceIdx L) :
    stabXMatrix L xf ⬝ᵥ stabZMatrix L zf = 0 := by
  have hs : rscBoundary2 L (Pi.single xf 1) = stabXMatrix L xf := by
    ext v
    exact boundary2_singleFace_apply L xf v
  have h := congrFun (rscBoundary_comp_zero_apply L (Pi.single xf 1)) zf
  rw [hs, rscBoundary1_eq_mulVecLin] at h
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

def code : CSSCode n mX mZ where
  HX := M.HX
  HZ := M.HZ
  comm := by
    ext i j
    change M.HX i ⬝ᵥ M.HZ j = 0
    rw [← pull_dot M.qubits, M.x_rows, M.z_rows]
    exact canonical_comm _ _

theorem boundaries_eq_rowspace :
    (rotatedSurfaceHomologicalCode L).boundaries =
      Submodule.span (ZMod 2) (Set.range (stabXMatrix L)) := by
  change LinearMap.range (rscBoundary2 L) = _
  rw [rscBoundary2_eq_transpose_mulVecLin, Matrix.range_mulVecLin]
  rfl

theorem dualBoundaries_eq_rowspace :
    (rotatedSurfaceHomologicalCode L).dualBoundaries =
      Submodule.span (ZMod 2) (Set.range (stabZMatrix L)) := by
  change LinearMap.range (rotatedSurfaceHomologicalCode L).cutMap = _
  rw [cutMap_eq_rscZCutMap, rscZCutMap_eq_transpose_mulVecLin]
  erw [Matrix.range_mulVecLin]
  rfl

theorem rankX : finrank (ZMod 2) M.code.xStab = Fintype.card (XFaceIdx L) := by
  have hm : Submodule.map (pull M.qubits).toLinearMap M.code.xStab =
      (rotatedSurfaceHomologicalCode L).boundaries := by
    rw [boundaries_eq_rowspace]
    exact rowspace_pull M.qubits M.HX _ M.xFace M.x_surjective M.x_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.xStab, hm]
  exact rsc_rank_boundary2

theorem rankZ : finrank (ZMod 2) M.code.zStab = Fintype.card (ZFaceIdx L) := by
  have hm : Submodule.map (pull M.qubits).toLinearMap M.code.zStab =
      (rotatedSurfaceHomologicalCode L).dualBoundaries := by
    rw [dualBoundaries_eq_rowspace]
    exact rowspace_pull M.qubits M.HZ _ M.zFace M.z_surjective M.z_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.zStab, hm]
  change finrank (ZMod 2) (LinearMap.range (rotatedSurfaceHomologicalCode L).cutMap) = _
  rw [cutMap_eq_rscZCutMap]
  exact rsc_rank_zCutMap

theorem encoded_qubits : n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 1 := by
  have hn : n = L * L := by
    have h := Fintype.card_congr M.qubits
    simpa using h.symm
  have hp : 0 < n := by
    rw [hn]
    have hL : 0 < L := by have h : 3 ≤ L := Fact.out; omega
    exact Nat.mul_pos hL hL
  rw [M.rankX, M.rankZ]
  have hc := card_ZFaceIdx_add_card_XFaceIdx (L := L)
  omega

theorem x_logical_iff (x : Vec n) :
    M.code.IsXLogical x ↔
      pull M.qubits x ∈ (rotatedSurfaceHomologicalCode L).cycles ∧
      pull M.qubits x ∉ (rotatedSurfaceHomologicalCode L).boundaries := by
  change (M.HZ.mulVec x = 0 ∧ x ∉ Submodule.span (ZMod 2) (Set.range M.HX)) ↔ _
  rw [boundaries_eq_rowspace]
  change _ ↔ (rscBoundary1 L (pull M.qubits x) = 0 ∧ _)
  rw [rscBoundary1_eq_mulVecLin]
  change _ ↔ ((stabZMatrix L).mulVec (pull M.qubits x) = 0 ∧ _)
  rw [kernel_pull_iff M.qubits M.HZ _ M.zFace M.z_surjective M.z_rows]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff M.qubits M.HX _ M.xFace M.x_surjective M.x_rows x)).symm

theorem z_logical_iff (z : Vec n) :
    M.code.IsZLogical z ↔
      pull M.qubits z ∈ (rotatedSurfaceHomologicalCode L).dualCycles ∧
      pull M.qubits z ∉ (rotatedSurfaceHomologicalCode L).dualBoundaries := by
  change (M.HX.mulVec z = 0 ∧ z ∉ Submodule.span (ZMod 2) (Set.range M.HZ)) ↔ _
  rw [dualBoundaries_eq_rowspace]
  change _ ↔ ((rotatedSurfaceHomologicalCode L).dualBoundary (pull M.qubits z) = 0 ∧ _)
  rw [dualBoundary_eq_mulVecLin]
  change _ ↔ ((stabXMatrix L).mulVec (pull M.qubits z) = 0 ∧ _)
  rw [kernel_pull_iff M.qubits M.HX _ M.xFace M.x_surjective M.x_rows]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff M.qubits M.HZ _ M.zFace M.z_surjective M.z_rows z)).symm

theorem chainWeight_eq (x : Vec n) :
    (rotatedSurfaceHomologicalCode L).chainWeight (pull M.qubits x) = hammingNorm x := by
  rw [← pull_weight M.qubits x]
  rfl

omit [Fact (Odd L)] in
theorem middleCol_weight : hammingNorm (middleColChain L) = L := by
  classical
  rw [hammingNorm, Finset.card_filter]
  have he : (fun p : VtxIdx L => if middleColChain L p ≠ 0 then (1 : ℕ) else 0) =
      (fun p => if p.1 = midIdx L then 1 else 0) := by
    funext p
    simp [middleColChain, Fin.ext_iff, midIdx]
  rw [he, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (midIdx L)]
  · simp
  · intro x _ hne
    simp [hne]
  · simp

omit [Fact (Odd L)] in
theorem middleRow_weight : hammingNorm (middleRowChain L) = L := by
  classical
  rw [hammingNorm, Finset.card_filter]
  have he : (fun p : VtxIdx L => if middleRowChain L p ≠ 0 then (1 : ℕ) else 0) =
      (fun p => if p.2 = midIdx L then 1 else 0) := by
    funext p
    simp [middleRowChain, Fin.ext_iff, midIdx]
  rw [he, Fintype.sum_prod_type]
  simp

theorem distX : M.code.DistX L := by
  constructor
  · refine ⟨(pull M.qubits).symm (middleColChain L), ?_, ?_⟩
    · rw [M.x_logical_iff, LinearEquiv.apply_symm_apply]
      exact ⟨middleColChain_mem_cycles L, middleColChain_not_mem_boundaries L⟩
    · have h := pull_weight M.qubits ((pull M.qubits).symm (middleColChain L))
      rw [LinearEquiv.apply_symm_apply, middleCol_weight] at h
      exact h.symm
  · intro x hx
    obtain ⟨hc, hb⟩ := (M.x_logical_iff x).mp hx
    simpa only [M.chainWeight_eq] using chainWeight_ge_L_of_nontrivial L hc hb

theorem distZ : M.code.DistZ L := by
  constructor
  · refine ⟨(pull M.qubits).symm (middleRowChain L), ?_, ?_⟩
    · rw [M.z_logical_iff, LinearEquiv.apply_symm_apply]
      exact ⟨middleRowChain_mem_dualCycles L, middleRowChain_not_mem_dualBoundaries L⟩
    · have h := pull_weight M.qubits ((pull M.qubits).symm (middleRowChain L))
      rw [LinearEquiv.apply_symm_apply, middleRow_weight] at h
      exact h.symm
  · intro z hz
    obtain ⟨hc, hb⟩ := (M.z_logical_iff z).mp hz
    simpa only [M.chainWeight_eq] using dual_chainWeight_ge_L_of_nontrivial L hc hb

theorem parameters :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 1) ∧
      M.code.DistX L ∧ M.code.DistZ L := ⟨M.encoded_qubits, M.distX, M.distZ⟩

end RotatedSurfaceMatch
end QldpcVerification
