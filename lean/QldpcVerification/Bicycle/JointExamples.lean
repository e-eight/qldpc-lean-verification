import QldpcVerification.Bicycle.JointMatch
import QldpcVerification.Input.LogicalWitness
import QldpcVerification.Input.SparseCertificates
import QldpcVerification.Lattice.JointFiniteBound

/-! Exact-distance construction regressions for nonunit steps and the one-vertex edge case. -/

namespace QldpcVerification.BicycleJoint12
open Matrix Module Input Input.Sparse Bicycle.Connected

def matching := canonicalMatch 6 2 3
abbrev code := matching.code

theorem finite_exclusion : ∀ i j : Fin 3,
    let u : ℤ := (i.val : ℤ) - 1
    let v : ℤ := (j.val : ℤ) - 1
    u.natAbs + v.natAbs ≤ 1 → (2 * u + 3 * v) % 6 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem lattice_bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (2 : ZMod 6) * (u : ZMod 6) + 3 * (v : ZMod 6) = 0) :
    2 ≤ u.natAbs + v.natAbs :=
  Lattice.norm_ge_of_joint_finite_exclusion 6 2 3 2 (by decide)
    finite_exclusion u v hn hc

theorem wx_logical : code.IsXLogical (vec 12 9) :=
  code.x_logical_of_pair _ (vec 12 398) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem wz_logical : code.IsZLogical (vec 12 576) :=
  code.z_logical_of_pair _ (vec 12 3632) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem wx_weight : hammingNorm (vec 12 9) = 2 := by rw [weight_eq]; decide +kernel
theorem wz_weight : hammingNorm (vec 12 576) = 2 := by rw [weight_eq]; decide +kernel

theorem ranks : finrank (ZMod 2) code.xStab = 5 ∧ finrank (ZMod 2) code.zStab = 5 :=
  ⟨matching.rankX (by decide), matching.rankZ (by decide)⟩

theorem parameters :
    (12 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 2 ∧ code.DistZ 2 :=
  matching.parameters 2 (by decide) lattice_bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

def naiveLift : Lattice.WindingData (source (m := 6)) (target 2 3) Bicycle.Normalized.horizontal :=
  Lattice.cyclicWindingData source (target 2 3) Bicycle.Normalized.horizontal 2 3
    (by simpa using step 2 3)

def naiveDetector (i : Fin 2) (q : Fin 12) : ZMod 2 :=
  let label := naiveLift.label (Bicycle.Normalized.qubits.symm q)
  if i = 0 then label.1 else label.2

/-- Carry and vertical parity miss this logical; the adapted coordinates are required. -/
theorem naive_coordinates_miss :
    code.IsZLogical (vec 12 597) ∧ ∀ i, vec 12 597 ⬝ᵥ naiveDetector i = 0 := by
  refine ⟨code.z_logical_of_pair _ (vec 12 4095)
    (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_⟩
  decide +kernel

end QldpcVerification.BicycleJoint12

namespace QldpcVerification.BicycleJoint30
open Matrix Module Input Input.Sparse Bicycle.Connected

def matching := canonicalMatch 15 6 10
abbrev code := matching.code

theorem finite_exclusion : ∀ i j : Fin 5,
    let u : ℤ := (i.val : ℤ) - 2
    let v : ℤ := (j.val : ℤ) - 2
    u.natAbs + v.natAbs ≤ 2 → (6 * u + 10 * v) % 15 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem lattice_bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (6 : ZMod 15) * (u : ZMod 15) + 10 * (v : ZMod 15) = 0) :
    3 ≤ u.natAbs + v.natAbs :=
  Lattice.norm_ge_of_joint_finite_exclusion 15 6 10 3 (by decide)
    finite_exclusion u v hn hc

theorem wx_logical : code.IsXLogical (vec 30 1057) :=
  code.x_logical_of_pair _ (vec 30 2753876) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem wz_logical : code.IsZLogical (vec 30 34635776) :=
  code.z_logical_of_pair _ (vec 30 357575168) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem wx_weight : hammingNorm (vec 30 1057) = 3 := by rw [weight_eq]; decide +kernel
theorem wz_weight : hammingNorm (vec 30 34635776) = 3 := by rw [weight_eq]; decide +kernel

theorem ranks : finrank (ZMod 2) code.xStab = 14 ∧ finrank (ZMod 2) code.zStab = 14 :=
  ⟨matching.rankX (by decide), matching.rankZ (by decide)⟩

theorem parameters :
    (30 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 3 ∧ code.DistZ 3 :=
  matching.parameters 3 (by decide) lattice_bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.BicycleJoint30

namespace QldpcVerification.BicycleJointTrivial2
open Matrix Module Input Input.Sparse Bicycle.Connected

def matching := canonicalMatch 1 0 0
abbrev code := matching.code

theorem finite_exclusion : ∀ i j : Fin 1,
    let u : ℤ := (i.val : ℤ) - 0
    let v : ℤ := (j.val : ℤ) - 0
    u.natAbs + v.natAbs ≤ 0 → (0 * u + 0 * v) % 1 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem lattice_bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (0 : ZMod 1) * (u : ZMod 1) + 0 * (v : ZMod 1) = 0) :
    1 ≤ u.natAbs + v.natAbs :=
  Lattice.norm_ge_of_joint_finite_exclusion 1 0 0 1 (by decide)
    finite_exclusion u v hn hc

theorem wx_logical : code.IsXLogical (vec 2 1) :=
  code.x_logical_of_pair _ (vec 2 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem wz_logical : code.IsZLogical (vec 2 1) :=
  code.z_logical_of_pair _ (vec 2 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem wx_weight : hammingNorm (vec 2 1) = 1 := by rw [weight_eq]; decide +kernel
theorem wz_weight : hammingNorm (vec 2 1) = 1 := by rw [weight_eq]; decide +kernel

theorem ranks : finrank (ZMod 2) code.xStab = 0 ∧ finrank (ZMod 2) code.zStab = 0 :=
  ⟨matching.rankX (by decide), matching.rankZ (by decide)⟩

theorem parameters :
    (2 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 1 ∧ code.DistZ 1 :=
  matching.parameters 1 (by decide) lattice_bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.BicycleJointTrivial2
