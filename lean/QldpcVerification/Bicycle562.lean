import QldpcVerification.Input.Homological
import QldpcVerification.Input.Bicycle562Checks
import QldpcVerification.Input.Bicycle562Geometry
import QldpcVerification.Lattice.Arithmetic562

/-! The submitted [[562,2,23]] matrices, proved by the cyclic lattice bridge. -/

namespace QldpcVerification.Bicycle562

open Matrix Module Input Input.Sparse Lattice Bicycle562Data
open Quantum.Stabilizer.Homological

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def code : CSSCode nq hx.length hz.length where
  HX := matrix hx
  HZ := matrix hz
  comm := Bicycle562Geometry.commutation

theorem hx_incidence (i : Fin 281) (q : Fin 562) :
    code.HX i q = incidence Bicycle562Geometry.xSource Bicycle562Geometry.xTarget q i := by
  change indicator (hx.get i) q = _
  rw [Bicycle562Geometry.x_match i]
  exact Bicycle562Geometry.x_indicator i q

theorem hz_incidence (i : Fin 281) (q : Fin 562) :
    code.HZ i q = incidence Bicycle562Geometry.zSource Bicycle562Geometry.zTarget q i := by
  change indicator (hz.get i) q = _
  rw [Bicycle562Geometry.z_match i]
  exact Bicycle562Geometry.z_indicator i q

theorem rankX_lower : 280 ≤ finrank (ZMod 2) code.xStab := by
  change 280 ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range code.HX))
  exact incidence_rank_lower Bicycle562Geometry.xSource Bicycle562Geometry.xTarget
    (0 : ZMod 281) code.HX hx_incidence Bicycle562Geometry.x_connected

theorem rankZ_lower : 280 ≤ finrank (ZMod 2) code.zStab := by
  change 280 ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range code.HZ))
  exact incidence_rank_lower Bicycle562Geometry.zSource Bicycle562Geometry.zTarget
    (0 : ZMod 281) code.HZ hz_incidence Bicycle562Geometry.z_connected

theorem rank_sum_bound : nq ≤ finrank (ZMod 2) code.xStab + finrank (ZMod 2) code.zStab + 2 := by
  have hx := rankX_lower
  have hz := rankZ_lower
  change 562 ≤ _
  omega

def blockDetector (i : Fin 2) : Vec nq := vec nq (blockMasks.get i)

theorem block_vec_eq (i : Fin 2) : blockDetector i = indicator (blocks.get i) :=
  Bicycle562Geometry.blocks_vector i

theorem block_x_cycle (i : Fin 2) : blockDetector i ∈ code.homological.cycles :=
  kernel_of_check hz _ (Bicycle562Checks.xBlocksKernel i)

theorem block_z_cycle (i : Fin 2) : blockDetector i ∈ code.homological.dualCycles := by
  change code.homological.dualBoundary (blockDetector i) = 0
  rw [code.dualBoundary_eq]
  exact kernel_of_check hx _ (Bicycle562Checks.zBlocksKernel i)

theorem block_paired (i j : Fin 2) :
    blockDetector i ⬝ᵥ blockDetector j = if i = j then 1 else 0 :=
  Bicycle562Geometry.blocks_paired i j

def xCoverage : CoverageCertificate code.homological.cycles code.homological.boundaries 2 where
  boundary_le := code.homological.boundaries_le_cycles
  detectors := blockDetector
  witnesses := blockDetector
  witness_mem := block_x_cycle
  boundary_zero := fun _ hb j => Homological.boundary_pairs_zero _ hb (block_z_cycle j)
  paired := block_paired
  dimension_bound := code.dimension_bound rank_sum_bound

def zCoverage : CoverageCertificate code.homological.dualCycles code.homological.dualBoundaries 2 where
  boundary_le := Homological.dual_boundaries_le_dual_cycles _
  detectors := blockDetector
  witnesses := blockDetector
  witness_mem := block_z_cycle
  boundary_zero := fun _ hb j => Homological.dual_boundary_pairs_zero _ hb (block_x_cycle j)
  paired := block_paired
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

theorem rankX : finrank (ZMod 2) code.xStab = 280 := by
  have hx : 280 ≤ finrank (ZMod 2) code.xStab := rankX_lower
  have hz : 280 ≤ finrank (ZMod 2) code.zStab := rankZ_lower
  have he : 562 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2 := encoded_qubits
  omega

theorem rankZ : finrank (ZMod 2) code.zStab = 280 := by
  have hx : 280 ≤ finrank (ZMod 2) code.xStab := rankX_lower
  have hz : 280 ≤ finrank (ZMod 2) code.zStab := rankZ_lower
  have he : 562 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2 := encoded_qubits
  omega

theorem detector_label0 (q : Fin 562) :
    blockDetector 0 q = (axisLabel Bicycle562Geometry.horizontal q).1 :=
  congrArg Prod.fst (Bicycle562Geometry.block_labels q)

theorem detector_label1 (q : Fin 562) :
    blockDetector 1 q = (axisLabel Bicycle562Geometry.horizontal q).2 :=
  congrArg Prod.snd (Bicycle562Geometry.block_labels q)

theorem swapped_lattice_bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (he : (145 : ZMod 281) * (u : ZMod 281) + 7 * (v : ZMod 281) = 0) :
    23 ≤ u.natAbs + v.natAbs := by
  have he' : (7 : ZMod 281) * (v : ZMod 281) + 145 * (u : ZMod 281) = 0 :=
    (add_comm _ _).trans he
  calc
    23 ≤ v.natAbs + u.natAbs := Arithmetic562.norm_ge_23_of_cast he' hn.symm
    _ = u.natAbs + v.natAbs := Nat.add_comm _ _

theorem x_lattice_cycle (x : Vec nq) (hx : code.IsXLogical x) :
    IsCycle Bicycle562Geometry.zSource Bicycle562Geometry.zTarget (binarySupport x) :=
  cycle_of_kernel (V := ZMod 281) Bicycle562Geometry.zSource Bicycle562Geometry.zTarget
    code.HZ hz_incidence x hx.1

theorem z_lattice_cycle (z : Vec nq) (hz : code.IsZLogical z) :
    IsCycle Bicycle562Geometry.xSource Bicycle562Geometry.xTarget (binarySupport z) :=
  cycle_of_kernel (V := ZMod 281) Bicycle562Geometry.xSource Bicycle562Geometry.xTarget
    code.HX hx_incidence z hz.1

theorem x_lattice_labels (x : Vec nq) (hx : code.IsXLogical x) :
    ∑ e ∈ binarySupport x, axisLabel Bicycle562Geometry.horizontal e ≠ 0 := by
  obtain ⟨hc, hb⟩ := (code.x_logical_iff x).mp hx
  exact label_sum_ne_zero_of_pairing Bicycle562Geometry.horizontal x blockDetector detector_label0 detector_label1
    (xCoverage.detects hc hb)

theorem z_lattice_labels (z : Vec nq) (hz : code.IsZLogical z) :
    ∑ e ∈ binarySupport z, axisLabel Bicycle562Geometry.horizontal e ≠ 0 := by
  obtain ⟨hc, hb⟩ := (code.z_logical_iff z).mp hz
  exact label_sum_ne_zero_of_pairing Bicycle562Geometry.horizontal z blockDetector detector_label0 detector_label1
    (zCoverage.detects hc hb)

theorem x_lower (x : Vec nq) (hx : code.IsXLogical x) : 23 ≤ hammingNorm x :=
  weight_ge_of_lattice_bound Bicycle562Geometry.horizontal (145 : ZMod 281) 7
    Bicycle562Geometry.zSource Bicycle562Geometry.zTarget Bicycle562Geometry.z_step 23
    swapped_lattice_bound x (x_lattice_cycle x hx) (x_lattice_labels x hx)

theorem z_lower (z : Vec nq) (hz : code.IsZLogical z) : 23 ≤ hammingNorm z :=
  weight_ge_of_lattice_bound Bicycle562Geometry.horizontal (7 : ZMod 281) 145
    Bicycle562Geometry.xSource Bicycle562Geometry.xTarget Bicycle562Geometry.x_step 23
    (fun _ _ hn he => Arithmetic562.norm_ge_23_of_cast he hn) z
    (z_lattice_cycle z hz) (z_lattice_labels z hz)

theorem distX : code.DistX 23 := by
  refine ⟨⟨vec nq wx, ?_, ?_⟩, x_lower⟩
  · rw [code.x_logical_iff]
    refine ⟨kernel_of_check hz wx Bicycle562Checks.wxKernel, ?_⟩
    intro hb
    obtain ⟨j, hj⟩ := Bicycle562Checks.wxPair
    have hh := xCoverage.boundary_zero _ hb j
    change vec nq wx ⬝ᵥ blockDetector j = 0 at hh
    rw [block_vec_eq, dotProduct_comm] at hh
    have hp := indicator_dot (blocks.get j) wx
    rw [hj] at hp
    exact one_ne_zero (hp.symm.trans hh)
  · rw [weight_eq]
    exact Bicycle562Checks.wxWeight

theorem distZ : code.DistZ 23 := by
  refine ⟨⟨vec nq wz, ?_, ?_⟩, z_lower⟩
  · rw [code.z_logical_iff]
    refine ⟨?_, ?_⟩
    · change code.homological.dualBoundary (vec nq wz) = 0
      rw [code.dualBoundary_eq]
      exact kernel_of_check hx wz Bicycle562Checks.wzKernel
    · intro hb
      obtain ⟨j, hj⟩ := Bicycle562Checks.wzPair
      have hh := zCoverage.boundary_zero _ hb j
      change vec nq wz ⬝ᵥ blockDetector j = 0 at hh
      rw [block_vec_eq, dotProduct_comm] at hh
      have hp := indicator_dot (blocks.get j) wz
      rw [hj] at hp
      exact one_ne_zero (hp.symm.trans hh)
  · rw [weight_eq]
    exact Bicycle562Checks.wzWeight

theorem parameters :
    (nq - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 23 ∧ code.DistZ 23 := ⟨encoded_qubits, distX, distZ⟩

end QldpcVerification.Bicycle562
