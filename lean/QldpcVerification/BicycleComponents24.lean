import QldpcVerification.Bicycle.ComponentParameters
import QldpcVerification.Bicycle.GcdComponents
import QldpcVerification.Bicycle.JointExamples

/-! GB(1+x^4,1+x^6,12) is two copies of the verified twelve-qubit component. -/

namespace QldpcVerification.BicycleComponents24

open Matrix Module Input Input.Sparse Bicycle

def matching := Connected.canonicalMatch 12 4 6
abbrev code := matching.code

theorem decomposition (r : Fin 2 × ZMod 6) :
    pull (Decomposition.edges 2 6) (Connected.H 4 6 (Decomposition.vertices 2 6 r)) =
      Components.block (Connected.H 2 3) r ∧
    pull (Decomposition.edges 2 6) (Connected.F 4 6 (Decomposition.vertices 2 6 r)) =
      Components.block (Connected.F 2 3) r :=
  ⟨Decomposition.pull_H 2 6 2 3 r, Decomposition.pull_F 2 6 2 3 r⟩

theorem ranks : finrank (ZMod 2) code.xStab = 10 ∧ finrank (ZMod 2) code.zStab = 10 :=
  ⟨Decomposition.MatrixMatch.rankX (c := 2) (l := 6) (a := 2) (b := 3) matching (by decide),
    Decomposition.MatrixMatch.rankZ (c := 2) (l := 6) (a := 2) (b := 3) matching (by decide)⟩

theorem distanceX_iff (D : ℕ) : code.DistX D ↔ BicycleJoint12.code.DistX D :=
  Decomposition.matrix_distanceX_iff (c := 2) (l := 6) (a := 2) (b := 3) matching BicycleJoint12.matching D

theorem distanceZ_iff (D : ℕ) : code.DistZ D ↔ BicycleJoint12.code.DistZ D :=
  Decomposition.matrix_distanceZ_iff (c := 2) (l := 6) (a := 2) (b := 3) matching BicycleJoint12.matching D

theorem parameters :
    (24 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 4) ∧
      code.DistX 2 ∧ code.DistZ 2 :=
  ⟨Decomposition.MatrixMatch.encoded_qubits (c := 2) (l := 6) (a := 2) (b := 3) matching (by decide),
    (distanceX_iff 2).mpr BicycleJoint12.parameters.2.1,
    (distanceZ_iff 2).mpr BicycleJoint12.parameters.2.2⟩

noncomputable def logicalCoverage :
    CoverageCertificate (Connected.cycles (m := 12) 4 6) (Connected.boundaries 4 6) 4 :=
  Decomposition.gcd_coverage 12 4 6

theorem wz_logical : code.IsZLogical (vec 24 266240) :=
  code.z_logical_of_pair _ (vec 24 5506304)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem logical_detected : ∃ i : Fin 4,
    pull matching.qubits (vec 24 266240) ⬝ᵥ logicalCoverage.detectors i = 1 := by
  obtain ⟨hs, hb⟩ := (matching.z_logical_iff _).mp wz_logical
  exact logicalCoverage.detects hs hb

def blockParity (i : Fin 2) (q : Fin 24) : ZMod 2 :=
  if q.val < 12 then (if i = 0 then 1 else 0) else (if i = 0 then 0 else 1)

theorem raw_parity_misses_logical :
    code.IsZLogical (vec 24 266240) ∧ ∀ i, vec 24 266240 ⬝ᵥ blockParity i = 0 :=
  ⟨wz_logical, by decide +kernel⟩

theorem single_component_recovers :
    (Connected.canonicalMatch 6 2 3).code = BicycleJoint12.code := rfl

theorem zero_step_structure :
    Decomposition.count 4 0 0 = 4 ∧
      finrank (ZMod 2) (Connected.boundaries (m := 4) 0 0) = 0 ∧
      (4 + 4) - finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.range (Connected.H (m := 4) 0 0))) -
        finrank (ZMod 2) (Connected.boundaries (m := 4) 0 0) = 8 :=
  ⟨by decide, (Decomposition.gcd_ranks 4 0 0).2, Decomposition.gcd_encoded_qubits 4 0 0⟩

end QldpcVerification.BicycleComponents24
