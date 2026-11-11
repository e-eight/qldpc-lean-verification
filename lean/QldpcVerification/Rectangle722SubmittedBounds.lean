import QldpcVerification.Rectangle722SubmittedSeventeen
import QldpcVerification.Rectangle722Witness

/-! Analytic lower bounds and explicit upper witness for the pinned submitted722 code. -/
namespace QldpcVerification.Rectangle722Submitted

open Input Quantum Quantum.Stabilizer.Homological

theorem parameters_and_bounds :
    (Module.finrank (ZMod 2) code.xStab = 357 ∧ Module.finrank (ZMod 2) code.zStab = 357) ∧
    (722 - Module.finrank (ZMod 2) code.xStab - Module.finrank (ZMod 2) code.zStab = 8) ∧
    (∀ x : Vec 722, code.IsXLogical x → 17 ≤ hammingNorm x) ∧
    (∀ z : Vec 722, code.IsZLogical z → 17 ≤ hammingNorm z) ∧
    (∃ z : Vec 722, code.IsZLogical z ∧ hammingNorm z = 20) :=
  ⟨⟨rankX, rankZ⟩, encoded_qubits, x_lower_seventeen, z_lower_seventeen,
    Rectangle722Witness.z_upper_witness⟩

theorem pauli_bounds :
    (∀ g : NQubitPauliGroupElement code.homological.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g code.homological.homologicalStabilizerGroup →
      17 ≤ NQubitPauliGroupElement.weight g) ∧
    (∃ g : NQubitPauliGroupElement code.homological.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g code.homological.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = 20) :=
  ⟨pauli_lower_seventeen, Rectangle722Witness.pauli_upper_witness⟩

end QldpcVerification.Rectangle722Submitted
