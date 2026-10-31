import QldpcVerification.Distance566WeightedCoverage
import QldpcVerification.Input.Distance566WeightedPacking

/-! Additive natural-weight packing bounds for the literal final matrices. -/

namespace QldpcVerification.Distance566Weighted

open Matrix Input Input.Sparse Quantum.Stabilizer.Homological WeightedPackingCertificates
open Removal566.Stage12 PackingData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem x_family_class (a : Fin 18) (i : Fin (xFamily a).length) :
    vec 566 ((xFamily a).get i).1 - xDetector a ∈ code.homological.boundaries := by
  rw [code.boundaries_eq]
  exact packedClassCheck_map_sound hx RowData.xMask RowData.x_check
    (Data.xMasks.get a) (xReps.get a) (xClass a) i

theorem z_family_class (a : Fin 18) (i : Fin (zFamily a).length) :
    vec 566 ((zFamily a).get i).1 - zDetector a ∈ code.homological.dualBoundaries := by
  rw [code.dualBoundaries_eq]
  exact packedClassCheck_map_sound hz RowData.zMask RowData.z_check
    (Data.zMasks.get a) (zReps.get a) (zClass a) i

/-- Z detector families modulo HZ bound every nontrivial X logical. -/
theorem lower_X (v : Vec 566) (h : code.IsXLogical v) : 6 ≤ hammingNorm v := by
  obtain ⟨a, ha⟩ := detects_X h
  have hc : v ∈ code.homological.cycles := h.1
  apply Homological.chain_weight_ge_of_overlap code.homological v
    (fun i : Fin (zFamily a).length => vec 566 ((zFamily a).get i).1)
    (fun i => ((zFamily a).get i).2) (zCaps.get a) 6
  · intro i
    exact (Homological.pairing_eq_of_dual_boundary _ hc (z_family_class a i)).trans ha
  · exact cap_of_check (zFamily a) _ (zCap a)
  · rw [← sum_map_eq]
    exact zThreshold a

/-- X detector families modulo HX bound every nontrivial Z logical. -/
theorem lower_Z (v : Vec 566) (h : code.IsZLogical v) : 6 ≤ hammingNorm v := by
  obtain ⟨a, ha⟩ := detects_Z h
  have hc : v ∈ code.homological.dualCycles := ((code.z_logical_iff v).mp h).1
  apply Homological.chain_weight_ge_of_overlap code.homological v
    (fun i : Fin (xFamily a).length => vec 566 ((xFamily a).get i).1)
    (fun i => ((xFamily a).get i).2) (xCaps.get a) 6
  · intro i
    exact (Homological.pairing_eq_of_boundary _ hc (x_family_class a i)).trans ha
  · exact cap_of_check (xFamily a) _ (xCap a)
  · rw [← sum_map_eq]
    exact xThreshold a

theorem partial_bounds :
    (∀ v, code.IsXLogical v → 6 ≤ hammingNorm v) ∧
    (∀ v, code.IsZLogical v → 6 ≤ hammingNorm v) :=
  ⟨lower_X, lower_Z⟩

end QldpcVerification.Distance566Weighted
