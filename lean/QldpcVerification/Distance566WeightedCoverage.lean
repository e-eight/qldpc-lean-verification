import QldpcVerification.Distance566
import QldpcVerification.Input.Distance566WeightedChecks

/-! Independent detector bases for the literal target, with separately paired
witnesses. Neither detector basis is replaced by a dense dualized basis. -/

namespace QldpcVerification.Distance566Weighted

open Matrix Module Input Input.Sparse Quantum.Stabilizer.Homological
open Removal566.Stage12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def xDetector (i : Fin 18) : Vec 566 := vec 566 (Data.xMasks.get i)
def zDetector (i : Fin 18) : Vec 566 := vec 566 (Data.zMasks.get i)

/-- A Z witness paired with an X detector; not necessarily a Z detector. -/
def xPaired (i : Fin 18) : Vec 566 := vec 566 (Data.xPairedMasks.get i)
/-- An X witness paired with a Z detector; not necessarily an X detector. -/
def zPaired (i : Fin 18) : Vec 566 := vec 566 (Data.zPairedMasks.get i)

theorem xDetector_cycle (i : Fin 18) : code.HZ.mulVec (xDetector i) = 0 :=
  kernel_of_check hz _ (Checks.xKernel i)

theorem zDetector_cycle (i : Fin 18) : code.HX.mulVec (zDetector i) = 0 :=
  kernel_of_check hx _ (Checks.zKernel i)

theorem xPaired_cycle (i : Fin 18) : code.HX.mulVec (xPaired i) = 0 :=
  kernel_of_check hx _ (Checks.xPairedKernel i)

theorem zPaired_cycle (i : Fin 18) : code.HZ.mulVec (zPaired i) = 0 :=
  kernel_of_check hz _ (Checks.zPairedKernel i)

theorem x_paired (i j : Fin 18) : xPaired i ⬝ᵥ xDetector j = if i = j then 1 else 0 := by
  have h := pairing_of_check Data.xSupports Data.xPairedMasks Checks.xPaired i j
  have hv := vec_eq_indicator (Data.xMasks.get j) (Data.xSupports.get j) (Checks.xVector j)
  simpa only [xPaired, xDetector, hv, Fin.ext_iff] using h

theorem z_paired (i j : Fin 18) : zPaired i ⬝ᵥ zDetector j = if i = j then 1 else 0 := by
  have h := pairing_of_check Data.zSupports Data.zPairedMasks Checks.zPaired i j
  have hv := vec_eq_indicator (Data.zMasks.get j) (Data.zSupports.get j) (Checks.zVector j)
  simpa only [zPaired, zDetector, hv, Fin.ext_iff] using h

def xCoverage : CoverageCertificate code.homological.cycles code.homological.boundaries 18 where
  boundary_le := code.homological.boundaries_le_cycles
  detectors := zDetector
  witnesses := zPaired
  witness_mem := zPaired_cycle
  boundary_zero := by
    intro b hb j
    apply Homological.boundary_pairs_zero code.homological hb
    change code.homological.dualBoundary (zDetector j) = 0
    rw [code.dualBoundary_eq]
    exact zDetector_cycle j
  paired := z_paired
  dimension_bound := code.dimension_bound (by rw [rankX, rankZ])

def zCoverage : CoverageCertificate code.homological.dualCycles code.homological.dualBoundaries 18 where
  boundary_le := Homological.dual_boundaries_le_dual_cycles _
  detectors := xDetector
  witnesses := xPaired
  witness_mem := by
    intro i
    change code.homological.dualBoundary (xPaired i) = 0
    rw [code.dualBoundary_eq]
    exact xPaired_cycle i
  boundary_zero := fun _ hb j => Homological.dual_boundary_pairs_zero _ hb (xDetector_cycle j)
  paired := x_paired
  dimension_bound := code.dual_dimension_bound (by rw [rankX, rankZ])

theorem detects_X {v : Vec 566} (h : code.IsXLogical v) :
    ∃ j, v ⬝ᵥ zDetector j = 1 :=
  xCoverage.detects h.1 (by simpa only [code.boundaries_eq] using h.2)

theorem detects_Z {v : Vec 566} (h : code.IsZLogical v) :
    ∃ j, v ⬝ᵥ xDetector j = 1 := by
  have hh := (code.z_logical_iff v).mp h
  exact zCoverage.detects hh.1 hh.2

end QldpcVerification.Distance566Weighted
