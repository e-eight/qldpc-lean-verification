import QldpcVerification.Distance566Packing

/-! Partial Pauli-distance bounds through QECLean's CSS distance bridge. -/

namespace QldpcVerification.Distance566

open Quantum Quantum.Stabilizer.Homological
open Removal566.Stage12

/-- The partial bound applies to mixed Pauli logicals as well as pure X/Z ones. -/
theorem pauli_lower (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    3 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 3
    (fun v hv hb => lower_X v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => lower_Z v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

/-- The stored X witness also gives an actual nontrivial Pauli of weight twenty. -/
theorem pauli_upper_witness :
    ∃ g : NQubitPauliGroupElement code.homological.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g
        code.homological.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = 20 := by
  refine ⟨code.homological.chainXOperator (x 0), ?_, ?_⟩
  · exact (HomologicalCode.chainXOperator_isNontrivialLogical_iff
      (X := code.homological) (x 0)).mpr
      ((code.x_logical_iff _).mp stored_X_logical)
  · rw [HomologicalCode.weight_chainXOperator]
    exact stored_X_weight

end QldpcVerification.Distance566
