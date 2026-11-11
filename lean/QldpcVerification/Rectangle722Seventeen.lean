import QldpcVerification.Rectangle722
import QldpcVerification.Planar.Distance722Seventeen

namespace QldpcVerification.Rectangle722

open Input Quantum Quantum.Stabilizer.Homological

theorem x_lower_seventeen (x : Vec 722) (hx : code.IsXLogical x) : 17 ≤ hammingNorm x := by
  obtain ⟨hc, hb⟩ := (x_logical_iff x).mp hx
  have hs : pull qubits x ∉ Planar.CycleSpaces722.xStab := by
    simpa only [Planar.CycleSpaces722.xStab_eq_span] using hb
  simpa only [pull_weight] using Planar.Distance722Seventeen.x_lower (pull qubits x) hc hs

theorem z_lower_seventeen (z : Vec 722) (hz : code.IsZLogical z) : 17 ≤ hammingNorm z := by
  obtain ⟨hc, hb⟩ := (z_logical_iff z).mp hz
  have hs : pull qubits z ∉ Planar.CycleSpaces722.zStab := by
    simpa only [Planar.CycleSpaces722.zStab_eq_span] using hb
  simpa only [pull_weight] using Planar.Distance722Seventeen.z_lower (pull qubits z) hc hs

theorem pauli_lower_seventeen (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    17 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 17
    (fun v hv hb => x_lower_seventeen v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => z_lower_seventeen v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

end QldpcVerification.Rectangle722
