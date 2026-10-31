import QldpcVerification.SectorPacking
import QldpcVerification.Input.Distance566SectorZPacking

/-!
An unconditional Z-logical lower bound for the literal submitted 566 matrices.
Fifteen individual detector families cover the nonzero prefix coordinates.
Seven mixed-class certificates cover every remaining nonzero three-bit suffix.
Logical coordinates do not change the physical Hamming weight.
-/

namespace QldpcVerification.Distance566SectorZ

open Matrix Input Input.Sparse Quantum.Stabilizer.Homological
open WeightedPackingCertificates SectorPackingCertificates
open Removal566.Stage12 PackingData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The seven nonzero suffixes, in the numerical certificate's bit order. -/
def residualTail (a : Fin 7) : Fin 3 → ZMod 2 :=
  fun j => if bit (a.val + 1) j then 1 else 0

theorem residualTail_ne_zero (a : Fin 7) : residualTail a ≠ 0 := by
  have h : ∀ a : Fin 7, residualTail a ≠ 0 := by decide +kernel
  exact h a

/-- All nonzero suffixes are covered, including sums of basis suffixes. -/
theorem residualTail_exhaustive (tail : Fin 3 → ZMod 2) (h : tail ≠ 0) :
    ∃ a : Fin 7, tail = residualTail a := by
  have hall : ∀ tail : Fin 3 → ZMod 2, tail ≠ 0 →
      ∃ a : Fin 7, tail = residualTail a := by decide +kernel
  exact hall tail h

/-- This is only the finite logical-coordinate encoding, not a physical map. -/
theorem shifted_pattern (a : Fin 7) (i : Fin 18) :
    (if bit ((a.val + 1) * 2 ^ 15) i then (1 : ZMod 2) else 0) =
      SectorPacking.residualCoordinates (r := 15) (residualTail a) i := by
  have h : ∀ a : Fin 7, ∀ i : Fin 18,
      (if bit ((a.val + 1) * 2 ^ 15) i then (1 : ZMod 2) else 0) =
        SectorPacking.residualCoordinates (r := 15) (residualTail a) i := by
    decide +kernel
  exact h a i

def reference (a : Fin 7) : Vec 566 := vec 566 (Data.referenceMasks.get a)
def base (a : Fin Data.numBases) : Vec 566 := vec 566 (Data.baseMask a)

theorem reference_cycle (a : Fin 7) : reference a ∈ code.homological.dualCycles := by
  change code.homological.dualBoundary (reference a) = 0
  rw [code.dualBoundary_eq]
  exact kernel_of_check hx _ (Checks.refKernel a)

theorem base_cycle (a : Fin Data.numBases) : base a ∈ code.homological.cycles :=
  kernel_of_check hz _ (Checks.baseKernel a)

theorem base_vector (a : Fin Data.numBases) : base a = indicator (Data.baseSupport a) :=
  vec_eq_indicator _ _ (Checks.baseVector a)

/-- Each checked physical reference has zero prefix and its specified suffix. -/
theorem reference_coordinates (a : Fin 7) :
    Distance566Weighted.zCoverage.coordinates ⟨reference a, reference_cycle a⟩ =
      SectorPacking.residualCoordinates (r := 15) (residualTail a) := by
  ext i
  change reference a ⬝ᵥ Distance566Weighted.xDetector i = _
  have hv := vec_eq_indicator (Distance566Weighted.Data.xMasks.get i)
    (Distance566Weighted.Data.xSupports.get i) (Distance566Weighted.Checks.xVector i)
  change reference a ⬝ᵥ vec 566 (Distance566Weighted.Data.xMasks.get i) = _
  rw [hv]
  have hp := pattern_of_check Distance566Weighted.Data.xSupports
    (Data.referenceMasks.get a) ((a.val + 1) * 2 ^ 15) (Checks.refPattern a) i
  exact hp.trans (shifted_pattern a i)

theorem good_family_class (a : Fin 15) (i : Fin (goodFamily a).length) :
    vec 566 ((goodFamily a).get i).1 -
      Distance566Weighted.xDetector (Fin.castAdd 3 a) ∈ code.homological.boundaries := by
  rw [code.boundaries_eq]
  exact packedClassCheck_map_sound hx Distance566Weighted.RowData.xMask
    Distance566Weighted.RowData.x_check
    (Distance566Weighted.Data.xMasks.get (Fin.castAdd 3 a))
    (goodReps.get a) (goodClass a) i

/-- A hit among the first fifteen coordinates gives the required bound. -/
theorem good_lower_bound (v : Vec 566) (hv : v ∈ code.homological.dualCycles)
    (a : Fin 15) (hpair : v ⬝ᵥ Distance566Weighted.xDetector (Fin.castAdd 3 a) = 1) :
    7 ≤ hammingNorm v := by
  apply Homological.chain_weight_ge_of_overlap code.homological v
    (fun i : Fin (goodFamily a).length => vec 566 ((goodFamily a).get i).1)
    (fun i => ((goodFamily a).get i).2) (goodCaps.get a) 7
  · intro i
    exact (Homological.pairing_eq_of_boundary _ hv (good_family_class a i)).trans hpair
  · exact cap_of_check (goodFamily a) _ (goodCap a)
  · rw [← sum_map_eq]
    exact goodThreshold a

/-- Each mixed representative has its own checked original-row difference. -/
theorem residual_family_class (a : Fin 7) (i : Fin (residualFamily a).length) :
    vec 566 ((residualFamily a).get i).1 -
      base (entryAt (residualReps.get a) i).1 ∈ code.homological.boundaries := by
  rw [code.boundaries_eq]
  exact mixedClassCheck_map_sound hx Distance566Weighted.RowData.xMask
    Distance566Weighted.RowData.x_check Data.baseMask (residualReps.get a)
    (residualClass a) i

/-- Cycle membership follows from one base-cycle check and a row-space difference. -/
theorem residual_family_cycle (a : Fin 7) (i : Fin (residualFamily a).length) :
    vec 566 ((residualFamily a).get i).1 ∈ code.homological.cycles := by
  let r : Vec 566 := vec 566 ((residualFamily a).get i).1
  let b : Vec 566 := base (entryAt (residualReps.get a) i).1
  have hd : r - b ∈ code.homological.cycles :=
    @HomologicalCode.boundaries_le_cycles code.homological (r - b)
      (residual_family_class a i)
  have hb : b ∈ code.homological.cycles := base_cycle (entryAt (residualReps.get a) i).1
  have hs : (r - b) + b ∈ code.homological.cycles :=
    Submodule.add_mem _ (x := r - b) (y := b) hd hb
  have he : (r - b) + b = r := sub_add_cancel _ _
  exact Eq.mp (congrArg (fun v : Vec 566 => v ∈ code.homological.cycles) he) hs

/-- Base pairings transfer using the reference's explicit opposite-cycle proof. -/
theorem reference_pairs_one (a : Fin 7) (i : Fin (residualFamily a).length) :
    reference a ⬝ᵥ vec 566 ((residualFamily a).get i).1 = 1 := by
  have hp := mixedPairCheck_sound Data.baseSupport (Data.referenceMasks.get a)
    (residualReps.get a) (residualPair a) i
  have hb : reference a ⬝ᵥ base (entryAt (residualReps.get a) i).1 = 1 := by
    rw [base_vector]
    exact hp
  exact (Homological.pairing_eq_of_boundary _ (reference_cycle a)
    (residual_family_class a i)).trans hb

theorem residual_boundary_zero (a : Fin 7) (i : Fin (residualFamily a).length)
    (b : Vec 566) (hb : b ∈ code.homological.dualBoundaries) :
    b ⬝ᵥ vec 566 ((residualFamily a).get i).1 = 0 :=
  Homological.dual_boundary_pairs_zero _ hb (residual_family_cycle a i)

/-- A mixed-class packing certifies the entire physical coordinate sector. -/
def residualCertificate (a : Fin 7) :
    SectorPacking.Certificate Distance566Weighted.zCoverage
      (SectorPacking.residualCoordinates (r := 15) (residualTail a)) 7 where
  size := (residualFamily a).length
  reference := ⟨reference a, reference_cycle a⟩
  reference_coordinates := reference_coordinates a
  representatives := fun i => vec 566 ((residualFamily a).get i).1
  weights := fun i => ((residualFamily a).get i).2
  cap := residualCaps.get a
  boundary_zero := fun i b hb => residual_boundary_zero a i b hb
  pairs_one := reference_pairs_one a
  capacity := cap_of_check (residualFamily a) _ (residualCap a)
  threshold := by
    rw [← sum_map_eq]
    exact residualThreshold a

theorem residual_lower_bound (a : Fin 7) (v : Vec 566)
    (hv : v ∈ code.homological.dualCycles)
    (hc : Distance566Weighted.zCoverage.coordinates ⟨v, hv⟩ =
      SectorPacking.residualCoordinates (r := 15) (residualTail a)) :
    7 ≤ hammingNorm v :=
  (residualCertificate a).lower_bound hv hc

/-- Every nontrivial dual cycle is covered by a good prefix hit or one of seven tails. -/
theorem lower_Z_cycle : ∀ v : Vec 566, v ∈ code.homological.dualCycles →
    v ∉ code.homological.dualBoundaries → 7 ≤ hammingNorm v := by
  apply SectorPacking.weight_ge_of_prefix_sectors (r := 15) (s := 3)
    Distance566Weighted.zCoverage 7
  · intro v hv _ a ha
    exact good_lower_bound v hv a ha
  · intro tail htail
    obtain ⟨a, rfl⟩ := residualTail_exhaustive tail htail
    exact residualCertificate a

/-- Unconditional Z-logical lower bound; this does not assert an exact distance. -/
theorem lower_Z (v : Vec 566) (h : code.IsZLogical v) : 7 ≤ hammingNorm v := by
  obtain ⟨hv, hb⟩ := (code.z_logical_iff v).mp h
  exact lower_Z_cycle v hv hb

end QldpcVerification.Distance566SectorZ
