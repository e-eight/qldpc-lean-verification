import QldpcVerification.Distance566
import QldpcVerification.Input.Distance566PackingChecks

/-! Kernel-checked partial packing bounds for the literal final matrices. -/

namespace QldpcVerification.Distance566

open Matrix Input Input.Sparse Quantum.Stabilizer.Homological Distance566Certificates
open Removal566.Stage12 PackingData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem z_mask_eq (a : Fin 18) : vec 566 (Data.zMasks.get a) = z a :=
  vec_eq_indicator _ _ (Checks.zVector a)

theorem x_family_class (a : Fin 18) (i : Fin (xFamily a).length) :
    vec 566 ((xFamily a).get i).1 - x a ∈ code.homological.boundaries := by
  rw [code.boundaries_eq]
  exact classCheck_map_sound hx (Data.xMasks.get a) (xReps.get a) (PackingChecks.xClass a) i

theorem z_family_class (a : Fin 18) (i : Fin (zFamily a).length) :
    vec 566 ((zFamily a).get i).1 - z a ∈ code.homological.dualBoundaries := by
  rw [code.dualBoundaries_eq, ← z_mask_eq]
  exact classCheck_map_sound hz (Data.zMasks.get a) (zReps.get a) (PackingChecks.zClass a) i

/-- Every nontrivial X logical has at least the certified partial packing weight. -/
theorem lower_X (v : Vec 566) (h : code.IsXLogical v) : bound ≤ hammingNorm v := by
  obtain ⟨a, ha⟩ := detects_X h
  have hc : v ∈ code.homological.cycles := h.1
  apply Homological.chain_weight_ge_of_overlap code.homological v
    (fun i : Fin (zFamily a).length => vec 566 ((zFamily a).get i).1)
    (fun i => ((zFamily a).get i).2) (zCaps.get a) bound
  · intro i
    exact (Homological.pairing_eq_of_dual_boundary _ hc (z_family_class a i)).trans ha
  · exact cap_of_check (zFamily a) _ (PackingChecks.zCap a)
  · rw [← sum_map_eq]
    exact PackingChecks.zThreshold a

/-- Every nontrivial Z logical has at least the certified partial packing weight. -/
theorem lower_Z (v : Vec 566) (h : code.IsZLogical v) : bound ≤ hammingNorm v := by
  obtain ⟨a, ha⟩ := detects_Z h
  have hc : v ∈ code.homological.dualCycles := ((code.z_logical_iff v).mp h).1
  apply Homological.chain_weight_ge_of_overlap code.homological v
    (fun i : Fin (xFamily a).length => vec 566 ((xFamily a).get i).1)
    (fun i => ((xFamily a).get i).2) (xCaps.get a) bound
  · intro i
    exact (Homological.pairing_eq_of_boundary _ hc (x_family_class a i)).trans ha
  · exact cap_of_check (xFamily a) _ (PackingChecks.xCap a)
  · rw [← sum_map_eq]
    exact PackingChecks.xThreshold a

theorem partial_bounds :
    (∀ v, code.IsXLogical v → 3 ≤ hammingNorm v) ∧
    (∀ v, code.IsZLogical v → 3 ≤ hammingNorm v) :=
  ⟨lower_X, lower_Z⟩

end QldpcVerification.Distance566
