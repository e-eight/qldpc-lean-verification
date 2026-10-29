import QldpcVerification.Input.Surface225Match
import QldpcVerification.Input.MatrixSpec
import QEC.Stabilizer.Codes.RotatedSurface.Distance

/-!
The submitted [[225,1,15]] check supports, matched to QECLean's surface code.
The qubit rotation and both complete row maps are checked by the kernel.
The distance bounds then use QECLean's parametric homological proofs.
-/

namespace QldpcVerification.Surface225

open QldpcVerification.Input

open Matrix Quantum.Stabilizer.Lattice.RotatedSurface
open Quantum.StabilizerGroup.RotatedSurfaceCodeN
open Quantum.Stabilizer.Homological.HomologicalCode

local instance : Fact (Odd 15) := ⟨by decide⟩
local instance : Fact (3 ≤ 15) := ⟨by decide⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem canonical_comm (xf : XFaceIdx 15) (zf : ZFaceIdx 15) :
    stabXMatrix 15 xf ⬝ᵥ stabZMatrix 15 zf = 0 := by
  have hs : rscBoundary2 15 (Pi.single xf 1) = stabXMatrix 15 xf := by
    ext v
    exact boundary2_singleFace_apply 15 xf v
  have h := congrFun (rscBoundary_comp_zero_apply 15 (Pi.single xf 1)) zf
  rw [hs, rscBoundary1_eq_mulVecLin] at h
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

def code : CSSCode 225 112 112 where
  HX := hx
  HZ := hz
  comm := by
    ext i j
    change hx i ⬝ᵥ hz j = 0
    rw [← pull_dot qubitEquiv, hx_pull, hz_pull]
    exact canonical_comm _ _

theorem boundaries_eq_rowspace :
    (rotatedSurfaceHomologicalCode 15).boundaries =
      Submodule.span (ZMod 2) (Set.range (stabXMatrix 15)) := by
  change LinearMap.range (rscBoundary2 15) = _
  rw [rscBoundary2_eq_transpose_mulVecLin, Matrix.range_mulVecLin]
  rfl

theorem dualBoundaries_eq_rowspace :
    (rotatedSurfaceHomologicalCode 15).dualBoundaries =
      Submodule.span (ZMod 2) (Set.range (stabZMatrix 15)) := by
  change LinearMap.range (rotatedSurfaceHomologicalCode 15).cutMap = _
  rw [cutMap_eq_rscZCutMap, rscZCutMap_eq_transpose_mulVecLin]
  erw [Matrix.range_mulVecLin]
  rfl

theorem rankX : Module.finrank (ZMod 2) code.xStab = 112 := by
  have hm : Submodule.map (pull qubitEquiv).toLinearMap code.xStab =
      (rotatedSurfaceHomologicalCode 15).boundaries := by
    rw [boundaries_eq_rowspace]
    exact rowspace_pull qubitEquiv hx (stabXMatrix 15) xFace xFace_surjective hx_pull
  rw [← (pull qubitEquiv).finrank_map_eq code.xStab, hm]
  change Module.finrank (ZMod 2) (LinearMap.range (rscBoundary2 15)) = 112
  rw [rsc_rank_boundary2]
  decide +kernel

theorem rankZ : Module.finrank (ZMod 2) code.zStab = 112 := by
  have hm : Submodule.map (pull qubitEquiv).toLinearMap code.zStab =
      (rotatedSurfaceHomologicalCode 15).dualBoundaries := by
    rw [dualBoundaries_eq_rowspace]
    exact rowspace_pull qubitEquiv hz (stabZMatrix 15) zFace zFace_surjective hz_pull
  rw [← (pull qubitEquiv).finrank_map_eq code.zStab, hm]
  change Module.finrank (ZMod 2) (LinearMap.range
    (rotatedSurfaceHomologicalCode 15).cutMap) = 112
  rw [cutMap_eq_rscZCutMap]
  erw [rsc_rank_zCutMap]
  decide +kernel

/-- The CSS rank formula gives exactly one encoded qubit. -/
theorem encoded_qubits :
    225 - Module.finrank (ZMod 2) code.xStab - Module.finrank (ZMod 2) code.zStab = 1 := by
  rw [rankX, rankZ]

/-- Matrix logical operators coincide with QECLean's nontrivial homology classes. -/
theorem x_logical_iff (x : Vec 225) :
    code.IsXLogical x ↔
      pull qubitEquiv x ∈ (rotatedSurfaceHomologicalCode 15).cycles ∧
      pull qubitEquiv x ∉ (rotatedSurfaceHomologicalCode 15).boundaries := by
  change (hz.mulVec x = 0 ∧ x ∉ Submodule.span (ZMod 2) (Set.range hx)) ↔ _
  rw [boundaries_eq_rowspace]
  change _ ↔ (rscBoundary1 15 (pull qubitEquiv x) = 0 ∧ _)
  rw [rscBoundary1_eq_mulVecLin]
  change _ ↔ ((stabZMatrix 15).mulVec (pull qubitEquiv x) = 0 ∧ _)
  rw [kernel_pull_iff qubitEquiv hz (stabZMatrix 15) zFace zFace_surjective hz_pull]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff qubitEquiv hx (stabXMatrix 15) xFace xFace_surjective hx_pull x)).symm

theorem z_logical_iff (z : Vec 225) :
    code.IsZLogical z ↔
      pull qubitEquiv z ∈ (rotatedSurfaceHomologicalCode 15).dualCycles ∧
      pull qubitEquiv z ∉ (rotatedSurfaceHomologicalCode 15).dualBoundaries := by
  change (hx.mulVec z = 0 ∧ z ∉ Submodule.span (ZMod 2) (Set.range hz)) ↔ _
  rw [dualBoundaries_eq_rowspace]
  change _ ↔ ((rotatedSurfaceHomologicalCode 15).dualBoundary (pull qubitEquiv z) = 0 ∧ _)
  rw [dualBoundary_eq_mulVecLin]
  change _ ↔ ((stabXMatrix 15).mulVec (pull qubitEquiv z) = 0 ∧ _)
  rw [kernel_pull_iff qubitEquiv hx (stabXMatrix 15) xFace xFace_surjective hx_pull]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff qubitEquiv hz (stabZMatrix 15) zFace zFace_surjective hz_pull z)).symm

theorem chainWeight_eq (x : Vec 225) :
    (rotatedSurfaceHomologicalCode 15).chainWeight (pull qubitEquiv x) = hammingNorm x := by
  rw [← pull_weight qubitEquiv x]
  rfl

theorem distX : code.DistX 15 := by
  constructor
  · refine ⟨(pull qubitEquiv).symm (middleColChain 15), ?_, ?_⟩
    · rw [x_logical_iff, LinearEquiv.apply_symm_apply]
      exact ⟨middleColChain_mem_cycles 15, middleColChain_not_mem_boundaries 15⟩
    · decide +kernel
  · intro x hx
    obtain ⟨hc, hb⟩ := (x_logical_iff x).mp hx
    simpa only [chainWeight_eq] using chainWeight_ge_L_of_nontrivial 15 hc hb

theorem distZ : code.DistZ 15 := by
  constructor
  · refine ⟨(pull qubitEquiv).symm (middleRowChain 15), ?_, ?_⟩
    · rw [z_logical_iff, LinearEquiv.apply_symm_apply]
      exact ⟨middleRowChain_mem_dualCycles 15, middleRowChain_not_mem_dualBoundaries 15⟩
    · decide +kernel
  · intro z hz
    obtain ⟨hc, hb⟩ := (z_logical_iff z).mp hz
    simpa only [chainWeight_eq] using dual_chainWeight_ge_L_of_nontrivial 15 hc hb

/-- The submitted matrices have both CSS distances exactly 15. -/
theorem distance : code.DistX 15 ∧ code.DistZ 15 := ⟨distX, distZ⟩

theorem parameters :
    (225 - Module.finrank (ZMod 2) code.xStab - Module.finrank (ZMod 2) code.zStab = 1) ∧
      code.DistX 15 ∧ code.DistZ 15 := ⟨encoded_qubits, distance⟩

end QldpcVerification.Surface225
