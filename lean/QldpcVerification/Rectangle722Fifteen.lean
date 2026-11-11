import QldpcVerification.Rectangle722
import QldpcVerification.Planar.Distance722Fifteen

namespace QldpcVerification.Rectangle722

open Input Quantum Quantum.Stabilizer.Homological

theorem x_lower_fifteen (x : Vec 722) (hx : code.IsXLogical x) : 15 ≤ hammingNorm x := by
  obtain ⟨hc, hb⟩ := (x_logical_iff x).mp hx
  have hs : pull qubits x ∉ Planar.CycleSpaces722.xStab := by
    simpa only [Planar.CycleSpaces722.xStab_eq_span] using hb
  simpa only [pull_weight] using Planar.Distance722Fifteen.x_lower (pull qubits x) hc hs

theorem z_lower_fifteen (z : Vec 722) (hz : code.IsZLogical z) : 15 ≤ hammingNorm z := by
  obtain ⟨hc, hb⟩ := (z_logical_iff z).mp hz
  have hs : pull qubits z ∉ Planar.CycleSpaces722.zStab := by
    simpa only [Planar.CycleSpaces722.zStab_eq_span] using hb
  simpa only [pull_weight] using Planar.Distance722Fifteen.z_lower (pull qubits z) hc hs

theorem pauli_lower_fifteen (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    15 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 15
    (fun v hv hb => x_lower_fifteen v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => z_lower_fifteen v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

end QldpcVerification.Rectangle722
