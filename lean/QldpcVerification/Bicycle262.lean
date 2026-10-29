import QldpcVerification.Input.Homological
import QldpcVerification.Input.Bicycle262Checks

/-! The submitted [[262,2,15]] code, with finite coverage and weighted packing certificates. -/

namespace QldpcVerification.Bicycle262

open Matrix Module Input Input.Sparse
open Quantum.Stabilizer.Homological
open Bicycle262Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def code : CSSCode nq hx.length hz.length where
  HX := matrix hx
  HZ := matrix hz
  comm := comm_of_check hx hz Bicycle262Checks.comm

theorem rankX_lower : tx.length ≤ finrank (ZMod 2) code.xStab :=
  rank_of_check hx tx px cx (by decide) (by decide)
    Bicycle262Checks.xColumns Bicycle262Checks.xPivots

theorem rankZ_lower : tz.length ≤ finrank (ZMod 2) code.zStab :=
  rank_of_check hz tz pz cz (by decide) (by decide)
    Bicycle262Checks.zColumns Bicycle262Checks.zPivots

theorem rank_sum_bound : nq ≤ finrank (ZMod 2) code.xStab + finrank (ZMod 2) code.zStab + 2 := by
  have hx := rankX_lower
  have hz := rankZ_lower
  have hn : nq = tx.length + tz.length + 2 := by decide +kernel
  omega

def xDetector (i : Fin 2) : Vec nq := indicator (xBase.get i)
def zDetector (i : Fin 2) : Vec nq := indicator (zBase.get i)

theorem x_mask_eq (i : Fin 2) : vec nq (xBaseMasks.get i) = xDetector i :=
  vec_eq_indicator _ _ (Bicycle262Checks.xBaseVectors i)

theorem z_mask_eq (i : Fin 2) : vec nq (zBaseMasks.get i) = zDetector i :=
  vec_eq_indicator _ _ (Bicycle262Checks.zBaseVectors i)

theorem x_detector_cycle (i : Fin 2) : xDetector i ∈ code.homological.cycles := by
  change (matrix hz).mulVec (xDetector i) = 0
  rw [← x_mask_eq]
  exact kernel_of_check hz _ (Bicycle262Checks.xBaseKernel i)

theorem z_detector_cycle (i : Fin 2) : zDetector i ∈ code.homological.dualCycles := by
  change code.homological.dualBoundary (zDetector i) = 0
  rw [code.dualBoundary_eq, ← z_mask_eq]
  exact kernel_of_check hx _ (Bicycle262Checks.zBaseKernel i)

/-- The two selected Z classes detect every nontrivial X logical. -/
def xCoverage : CoverageCertificate code.homological.cycles code.homological.boundaries 2 where
  boundary_le := code.homological.boundaries_le_cycles
  detectors := zDetector
  witnesses := fun i => vec nq (xDual.get i)
  witness_mem := fun i => kernel_of_check hz _ (Bicycle262Checks.xDualKernel i)
  boundary_zero := fun _ hb j => Homological.boundary_pairs_zero _ hb (z_detector_cycle j)
  paired := fun i j => by
    simpa only [Fin.ext_iff] using
      pairing_of_check zBase xDual Bicycle262Checks.xPairing i j
  dimension_bound := code.dimension_bound rank_sum_bound

/-- The selected X classes detect every nontrivial Z logical. -/
def zCoverage : CoverageCertificate code.homological.dualCycles code.homological.dualBoundaries 2 where
  boundary_le := Homological.dual_boundaries_le_dual_cycles _
  detectors := xDetector
  witnesses := fun i => vec nq (zDual.get i)
  witness_mem := fun i => by
    change code.homological.dualBoundary (vec nq (zDual.get i)) = 0
    rw [code.dualBoundary_eq]
    exact kernel_of_check hx _ (Bicycle262Checks.zDualKernel i)
  boundary_zero := fun _ hb j => Homological.dual_boundary_pairs_zero _ hb (x_detector_cycle j)
  paired := fun i j => by
    simpa only [Fin.ext_iff] using
      pairing_of_check xBase zDual Bicycle262Checks.zPairing i j
  dimension_bound := code.dual_dimension_bound rank_sum_bound

theorem encoded_qubits :
    nq - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2 := by
  have hd := xCoverage.dimension_eq
  rw [code.boundaries_eq] at hd
  change finrank (ZMod 2) (LinearMap.ker code.HZ.mulVecLin) =
    finrank (ZMod 2) code.xStab + 2 at hd
  have hr := Input.CSSCode.rank_nullity code.HZ
  change finrank (ZMod 2) (LinearMap.ker code.HZ.mulVecLin) +
    finrank (ZMod 2) code.zStab = nq at hr
  omega

theorem z_family_class (a : Fin 2) (family : List (ℕ × ℕ))
    (h : familyCheck hx xBase (zBaseMasks.get a) family = true) (i : Fin family.length) :
    vec nq (family.get i).1 - zDetector a ∈ code.homological.dualBoundaries := by
  have hc : vec nq (family.get i).1 ∈ code.homological.dualCycles := by
    change code.homological.dualBoundary _ = 0
    rw [code.dualBoundary_eq]
    exact family_kernel hx xBase _ family h i
  apply (zCoverage.difference_mem_iff hc (z_detector_cycle a)).mpr
  intro j
  have hp := family_pair hx xBase _ family h i j
  erw [z_mask_eq a] at hp
  exact (dotProduct_comm _ _).trans (hp.trans (dotProduct_comm _ _))

theorem x_family_class (a : Fin 2) (family : List (ℕ × ℕ))
    (h : familyCheck hz zBase (xBaseMasks.get a) family = true) (i : Fin family.length) :
    vec nq (family.get i).1 - xDetector a ∈ code.homological.boundaries := by
  have hc : vec nq (family.get i).1 ∈ code.homological.cycles :=
    family_kernel hz zBase _ family h i
  apply (xCoverage.difference_mem_iff hc (x_detector_cycle a)).mpr
  intro j
  have hp := family_pair hz zBase _ family h i j
  erw [x_mask_eq a] at hp
  exact (dotProduct_comm _ _).trans (hp.trans (dotProduct_comm _ _))

theorem x_ge_family (a : Fin 2) (family : List (ℕ × ℕ)) (cap : ℕ)
    (hclass : familyCheck hx xBase (zBaseMasks.get a) family = true)
    (hcap : capCheck nq family cap = true)
    (ht : (target - 1) * cap < (family.map Prod.snd).sum)
    (x : Vec nq) (hc : x ∈ code.homological.cycles) (hp : x ⬝ᵥ zDetector a = 1) :
    target ≤ hammingNorm x := by
  have hh := Homological.chain_weight_ge_of_overlap code.homological x
    (fun i : Fin family.length => vec nq (family.get i).1)
    (fun i => (family.get i).2) cap target
    (fun i => (Homological.pairing_eq_of_dual_boundary _ hc
      (z_family_class a family hclass i)).trans hp)
    (cap_of_check family cap hcap)
    (by rw [← sum_map_eq]; exact ht)
  exact hh

theorem z_ge_family (a : Fin 2) (family : List (ℕ × ℕ)) (cap : ℕ)
    (hclass : familyCheck hz zBase (xBaseMasks.get a) family = true)
    (hcap : capCheck nq family cap = true)
    (ht : (target - 1) * cap < (family.map Prod.snd).sum)
    (z : Vec nq) (hc : z ∈ code.homological.dualCycles) (hp : z ⬝ᵥ xDetector a = 1) :
    target ≤ hammingNorm z := by
  have hh := Homological.chain_weight_ge_of_overlap code.homological z
    (fun i : Fin family.length => vec nq (family.get i).1)
    (fun i => (family.get i).2) cap target
    (fun i => (Homological.pairing_eq_of_boundary _ hc
      (x_family_class a family hclass i)).trans hp)
    (cap_of_check family cap hcap)
    (by rw [← sum_map_eq]; exact ht)
  exact hh

theorem x_lower (x : Vec nq) (hx : code.IsXLogical x) : target ≤ hammingNorm x := by
  obtain ⟨hc, hb⟩ := (code.x_logical_iff x).mp hx
  obtain ⟨a, ha⟩ := xCoverage.detects hc hb
  fin_cases a
  · exact x_ge_family 0 zFamily0 cap0 Bicycle262Checks.zClass0
      Bicycle262Checks.zCap0 Bicycle262Checks.threshold0 x hc ha
  · exact x_ge_family 1 zFamily1 cap1 Bicycle262Checks.zClass1
      Bicycle262Checks.zCap1 Bicycle262Checks.threshold1 x hc ha

theorem z_lower (z : Vec nq) (hz : code.IsZLogical z) : target ≤ hammingNorm z := by
  obtain ⟨hc, hb⟩ := (code.z_logical_iff z).mp hz
  obtain ⟨a, ha⟩ := zCoverage.detects hc hb
  fin_cases a
  · exact z_ge_family 0 xFamily0 cap0 Bicycle262Checks.xClass0
      Bicycle262Checks.xCap0 (by decide +kernel) z hc ha
  · exact z_ge_family 1 xFamily1 cap1 Bicycle262Checks.xClass1
      Bicycle262Checks.xCap1 (by decide +kernel) z hc ha

theorem distX : code.DistX target := by
  refine ⟨⟨vec nq wx, ?_, ?_⟩, x_lower⟩
  · rw [code.x_logical_iff]
    refine ⟨kernel_of_check hz wx Bicycle262Checks.wxKernel, ?_⟩
    intro hb
    obtain ⟨j, hj⟩ := Bicycle262Checks.wxPair
    have hh := xCoverage.boundary_zero _ hb j
    change vec nq wx ⬝ᵥ indicator (zBase.get j) = 0 at hh
    rw [dotProduct_comm, indicator_dot] at hh
    erw [hj] at hh
    exact one_ne_zero hh
  · rw [weight_eq]
    exact Bicycle262Checks.wxWeight

theorem distZ : code.DistZ target := by
  refine ⟨⟨vec nq wz, ?_, ?_⟩, z_lower⟩
  · rw [code.z_logical_iff]
    refine ⟨?_, ?_⟩
    · change code.homological.dualBoundary (vec nq wz) = 0
      rw [code.dualBoundary_eq]
      exact kernel_of_check hx wz Bicycle262Checks.wzKernel
    · intro hb
      obtain ⟨j, hj⟩ := Bicycle262Checks.wzPair
      have hh := zCoverage.boundary_zero _ hb j
      change vec nq wz ⬝ᵥ indicator (xBase.get j) = 0 at hh
      rw [dotProduct_comm, indicator_dot] at hh
      erw [hj] at hh
      exact one_ne_zero hh
  · rw [weight_eq]
    exact Bicycle262Checks.wzWeight

theorem parameters :
    (nq - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 15 ∧ code.DistZ 15 := ⟨encoded_qubits, distX, distZ⟩

end QldpcVerification.Bicycle262
