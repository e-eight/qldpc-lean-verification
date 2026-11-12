import QldpcVerification.Rectangle722Submitted
import QldpcVerification.Rectangle722Seventeen

/-! The analytic seventeen lower bound transported to the pinned submitted rows. -/
namespace QldpcVerification.Rectangle722Submitted

open Input Quantum Quantum.Stabilizer.Homological

theorem x_lower_seventeen (x : Vec 722) (hx : code.IsXLogical x) : 17 ≤ hammingNorm x := by
  rw [code_eq_family] at hx
  exact Planar.RectangleFamily.x_lower 17 17 x hx

theorem z_lower_seventeen (z : Vec 722) (hz : code.IsZLogical z) : 17 ≤ hammingNorm z := by
  rw [code_eq_family] at hz
  exact Planar.RectangleFamily.z_lower 17 17 z hz

theorem pauli_lower_seventeen (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    17 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 17
    (fun v hv hb => x_lower_seventeen v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => z_lower_seventeen v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

end QldpcVerification.Rectangle722Submitted
