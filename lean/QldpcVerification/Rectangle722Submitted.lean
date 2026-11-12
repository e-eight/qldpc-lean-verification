import QldpcVerification.Input.Rectangle722Recognition
import QldpcVerification.Rectangle722Fifteen

/-!
The pinned submitted check arrays, identified with the `(17,17)` rectangle
family member by the retained sparse row identities and literal model equality.
The JSON name's distance 20 is not used as a hypothesis or asserted as a conclusion.
-/
namespace QldpcVerification.Rectangle722Submitted

open Input Input.Rectangle722Recognition
open Quantum Quantum.Stabilizer.Homological

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

private theorem css_ext {n mX mZ : ℕ} (C D : CSSCode n mX mZ)
    (hx : C.HX = D.HX) (hz : C.HZ = D.HZ) : C = D := by
  cases C
  cases D
  dsimp at hx hz
  cases hx
  cases hz
  rfl

/-- Input order r = 17a+b, anchor (a-2,b). -/
def HX : Matrix (Fin 357) (Fin 722) (ZMod 2) :=
  fun i q => row (rawX (Rectangle722.xRows.symm i)) q

/-- Input order r = 21c+d, anchor (c+2,d). -/
def HZ : Matrix (Fin 357) (Fin 722) (ZMod 2) :=
  fun i q => row (rawZ (Rectangle722.zRows.symm i)) q

theorem HX_eq : HX = Rectangle722.code.HX := by
  funext i q
  unfold HX
  rw [fixedX]
  have h := expectedX_row (Rectangle722.xRows.symm i) (Rectangle722.qubits.symm q)
  simpa only [Equiv.apply_symm_apply] using h

theorem HZ_eq : HZ = Rectangle722.code.HZ := by
  funext i q
  unfold HZ
  rw [fixedZ]
  have h := expectedZ_row (Rectangle722.zRows.symm i) (Rectangle722.qubits.symm q)
  simpa only [Equiv.apply_symm_apply] using h

/-- Commutation is transported from the analytic model, not evaluated densely. -/
def code : CSSCode 722 357 357 where
  HX := HX
  HZ := HZ
  comm := by rw [HX_eq, HZ_eq]; exact Rectangle722.code.comm

theorem code_eq : code = Rectangle722.code := by
  exact css_ext code Rectangle722.code HX_eq HZ_eq

/-- The literal submitted arrays are the canonical nineteen-by-nineteen family member. -/
theorem code_eq_family : code = Planar.RectangleFamily.code 17 17 :=
  code_eq.trans Rectangle722.code_eq_family

theorem rankX : Module.finrank (ZMod 2) code.xStab = 357 := by
  rw [code_eq_family]
  exact Planar.RectangleFamily.rankX 17 17

theorem rankZ : Module.finrank (ZMod 2) code.zStab = 357 := by
  rw [code_eq_family]
  exact Planar.RectangleFamily.rankZ 17 17

theorem encoded_qubits :
    722 - Module.finrank (ZMod 2) code.xStab - Module.finrank (ZMod 2) code.zStab = 8 := by
  rw [code_eq_family]
  exact Planar.RectangleFamily.encoded_qubits 17 17

theorem x_lower_fifteen (x : Vec 722) (hx : code.IsXLogical x) :
    15 ≤ hammingNorm x := by
  rw [code_eq_family] at hx
  exact (by omega : 15 ≤ 17).trans (Planar.RectangleFamily.x_lower 17 17 x hx)

theorem z_lower_fifteen (z : Vec 722) (hz : code.IsZLogical z) :
    15 ≤ hammingNorm z := by
  rw [code_eq_family] at hz
  exact (by omega : 15 ≤ 17).trans (Planar.RectangleFamily.z_lower 17 17 z hz)

theorem pauli_lower_fifteen (g : NQubitPauliGroupElement code.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      code.homological.homologicalStabilizerGroup) :
    15 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers code.homological 15
    (fun v hv hb => x_lower_fifteen v ((code.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => z_lower_fifteen v ((code.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

end QldpcVerification.Rectangle722Submitted
