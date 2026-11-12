import QldpcVerification.Rectangle722Seventeen

namespace QldpcVerification.Rectangle722

open Input Quantum Quantum.Stabilizer.Homological

theorem x_lower_fifteen (x : Vec 722) (hx : code.IsXLogical x) : 15 ≤ hammingNorm x := by
  exact (by omega : 15 ≤ 17).trans (x_lower_seventeen x hx)

theorem z_lower_fifteen (z : Vec 722) (hz : code.IsZLogical z) : 15 ≤ hammingNorm z := by
  exact (by omega : 15 ≤ 17).trans (z_lower_seventeen z hz)

theorem pauli_lower_fifteen (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    15 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 15
    (fun v hv hb => x_lower_fifteen v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => z_lower_fifteen v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

end QldpcVerification.Rectangle722
