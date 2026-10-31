import QldpcVerification.Boundary566Stage12
import QldpcVerification.Input.LogicalWitness
import QldpcVerification.Input.Distance566Checks

/-! Complete logical coordinates and an upper witness for the literal 566 matrices.
This module supplies no lower bound of twenty. -/

namespace QldpcVerification.Distance566

open Matrix Module Input Input.Sparse Quantum.Stabilizer.Homological
open Removal566.Stage12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def x (i : Fin 18) : Vec 566 := vec 566 (Data.xMasks.get i)
def z (i : Fin 18) : Vec 566 := indicator (Data.zSupports.get i)

theorem x_cycle (i : Fin 18) : code.HZ.mulVec (x i) = 0 :=
  kernel_of_check hz _ (Checks.xKernel i)

theorem z_cycle (i : Fin 18) : code.HX.mulVec (z i) = 0 := by
  have hv := vec_eq_indicator (Data.zMasks.get i) (Data.zSupports.get i) (Checks.zVector i)
  rw [z, ← hv]
  exact kernel_of_check hx _ (Checks.zKernel i)

theorem paired (i j : Fin 18) : x i ⬝ᵥ z j = if i = j then 1 else 0 := by
  have h := pairing_of_check Data.zSupports Data.xMasks Checks.paired i j
  simpa only [x, z, Fin.ext_iff] using h

def xCoverage : CoverageCertificate code.homological.cycles code.homological.boundaries 18 where
  boundary_le := code.homological.boundaries_le_cycles
  detectors := z
  witnesses := x
  witness_mem := x_cycle
  boundary_zero := by
    intro b hb j
    apply Homological.boundary_pairs_zero code.homological hb
    change code.homological.dualBoundary (z j) = 0
    rw [code.dualBoundary_eq]
    exact z_cycle j
  paired := paired
  dimension_bound := code.dimension_bound (by rw [rankX, rankZ])

def zCoverage : CoverageCertificate code.homological.dualCycles code.homological.dualBoundaries 18 where
  boundary_le := Homological.dual_boundaries_le_dual_cycles _
  detectors := x
  witnesses := z
  witness_mem := by
    intro i
    change code.homological.dualBoundary (z i) = 0
    rw [code.dualBoundary_eq]
    exact z_cycle i
  boundary_zero := fun _ hb j => Homological.dual_boundary_pairs_zero _ hb (x_cycle j)
  paired := by
    intro i j
    exact (dotProduct_comm _ _).trans (by
      simpa only [eq_comm] using (Distance566.paired j i))
  dimension_bound := code.dual_dimension_bound (by rw [rankX, rankZ])

/-- Every nontrivial X class is detected by one of the eighteen paired Z cycles. -/
theorem detects_X {v : Vec 566} (h : code.IsXLogical v) : ∃ j, v ⬝ᵥ z j = 1 :=
  xCoverage.detects h.1 (by simpa only [code.boundaries_eq] using h.2)

/-- Every nontrivial Z class is detected by one of the eighteen paired X cycles. -/
theorem detects_Z {v : Vec 566} (h : code.IsZLogical v) : ∃ j, v ⬝ᵥ x j = 1 := by
  have hh := (code.z_logical_iff v).mp h
  exact zCoverage.detects hh.1 hh.2

/-- The first X coordinate is the stored submitted weight-twenty witness. -/
theorem stored_X_logical : code.IsXLogical (x 0) :=
  code.x_logical_of_pair (x 0) (z 0) (x_cycle 0) (z_cycle 0) (by simpa using paired 0 0)

theorem stored_X_weight : hammingNorm (x 0) = 20 := by
  rw [x, weight_eq]
  exact Checks.xWeight

/-- An upper bound only; the final lower-distance obligations remain separate. -/
theorem X_upper_witness : ∃ v, code.IsXLogical v ∧ hammingNorm v = 20 :=
  ⟨x 0, stored_X_logical, stored_X_weight⟩

end QldpcVerification.Distance566
