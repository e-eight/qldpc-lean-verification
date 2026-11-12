import QldpcVerification.Rectangle722Seventeen

/-! Both sector and mixed-Pauli lower bounds for the explicit rectangle,
transported to the project's QECLean-backed CSS model. -/
namespace QldpcVerification.Rectangle722

open Input Quantum Quantum.Stabilizer.Homological

theorem x_lower (x : Vec 722) (hx : code.IsXLogical x) : 9 ≤ hammingNorm x := by
  exact (by omega : 9 ≤ 17).trans (x_lower_seventeen x hx)

theorem z_lower (z : Vec 722) (hz : code.IsZLogical z) : 9 ≤ hammingNorm z := by
  exact (by omega : 9 ≤ 17).trans (z_lower_seventeen z hz)

theorem pauli_lower (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    9 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 9
    (fun v hv hb => x_lower v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => z_lower v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

end QldpcVerification.Rectangle722
