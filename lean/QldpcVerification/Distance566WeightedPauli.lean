import QldpcVerification.Distance566WeightedPacking
import QldpcVerification.Distance566Pauli

/-! The stronger lower bound includes mixed Pauli logicals through QECLean. -/

namespace QldpcVerification.Distance566Weighted

open Quantum Quantum.Stabilizer.Homological
open Removal566.Stage12

theorem pauli_lower (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    6 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 6
    (fun v hv hb => lower_X v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => lower_Z v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

/-- Reuse the unchanged, already checked submitted X witness. -/
theorem X_upper_witness : ∃ v, code.IsXLogical v ∧ hammingNorm v = 20 :=
  Distance566.X_upper_witness

theorem pauli_upper_witness :
    ∃ g : NQubitPauliGroupElement code.homological.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g
        code.homological.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = 20 :=
  Distance566.pauli_upper_witness

end QldpcVerification.Distance566Weighted
