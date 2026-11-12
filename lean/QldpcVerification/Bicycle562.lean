import QldpcVerification.Bicycle562Family
import QldpcVerification.Input.Homological
import QldpcVerification.Input.Bicycle562Checks
import QldpcVerification.Input.Bicycle562Geometry
import QldpcVerification.Input.Bicycle562Winding
import QldpcVerification.Lattice.Arithmetic562

/-! The submitted [[562,2,23]] matrices, with exact parameters from the analytic
shortest-relation family theorem. Earlier geometry helpers remain available. -/

namespace QldpcVerification.Bicycle562

open Matrix Module Input Input.Sparse Lattice Bicycle562Data
open Quantum.Stabilizer.Homological

set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def code : CSSCode nq hx.length hz.length := Bicycle562Family.code

/-- The historical public code is the recognized family code on the same literal rows. -/
theorem family_code_eq : code = Bicycle562Family.code := rfl

theorem HX_eq_original : code.HX = matrix hx := rfl
theorem HZ_eq_original : code.HZ = matrix hz := rfl

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

theorem rankX_lower : 280 ≤ finrank (ZMod 2) code.xStab :=
  le_of_eq Bicycle562Family.rankX.symm

theorem rankZ_lower : 280 ≤ finrank (ZMod 2) code.zStab :=
  le_of_eq Bicycle562Family.rankZ.symm

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
    nq - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2 :=
  Bicycle562Family.parameters.1

theorem rankX : finrank (ZMod 2) code.xStab = 280 :=
  Bicycle562Family.rankX

theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  Bicycle562Family.rankZ

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
  Bicycle562Family.parameters.2.1.2 x hx

theorem z_lower (z : Vec nq) (hz : code.IsZLogical z) : 23 ≤ hammingNorm z :=
  Bicycle562Family.parameters.2.2.2 z hz

theorem distX : code.DistX 23 :=
  Bicycle562Family.parameters.2.1

theorem distZ : code.DistZ 23 :=
  Bicycle562Family.parameters.2.2

theorem parameters :
    (nq - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 23 ∧ code.DistZ 23 := ⟨encoded_qubits, distX, distZ⟩

end QldpcVerification.Bicycle562
