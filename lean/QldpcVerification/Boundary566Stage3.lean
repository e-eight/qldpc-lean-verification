import QldpcVerification.Boundary566Stage4
import QldpcVerification.Input.Removal566Step3Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage3
def code : CSSCode 575 277 280 :=
  recognize Stage4.hx Stage4.hz Step3.fan Step3.clear Step3.clear_last
    Stage4.code Stage4.hx_eq Stage4.hz_eq hx.get hz.get
    Step3.e Step3.rx Step3.rz Step3.xcheck Step3.zcheck
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : code =
    extension Stage4.code (indicator Step3.fan) (indicator Step3.clear)
      (by exact if_neg Step3.clear_last) Step3.e Step3.rx Step3.rz := by
  exact recognize_eq Stage4.hx Stage4.hz Step3.fan Step3.clear Step3.clear_last
    Stage4.code Stage4.hx_eq Stage4.hz_eq hx.get hz.get
    Step3.e Step3.rx Step3.rz Step3.xcheck Step3.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage4.code.xStab + 1 := by
  exact recognize_rankX Stage4.hx Stage4.hz Step3.fan Step3.clear Step3.clear_last
    Stage4.code Stage4.hx_eq Stage4.hz_eq hx.get hz.get
    Step3.e Step3.rx Step3.rz Step3.xcheck Step3.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage4.code.zStab  := by
  exact recognize_rankZ Stage4.hx Stage4.hz Step3.fan Step3.clear Step3.clear_last
    Stage4.code Stage4.hx_eq Stage4.hz_eq hx.get hz.get
    Step3.e Step3.rx Step3.rz Step3.xcheck Step3.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 277 :=
  step_rankX.trans (congrArg (fun r : ℕ => r + 1) Stage4.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  step_rankZ.trans (Stage4.rankZ)
theorem encoded_dimension : 575 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 575 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage4.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_new_X_lower Stage4.hx Stage4.hz Step3.fan Step3.clear Step3.clear_last
    Stage4.code Stage4.hx_eq Stage4.hz_eq hx.get hz.get
    Step3.e Step3.rx Step3.rz Step3.xcheck Step3.zcheck h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage4.code.IsZLogical z → D - 1 ≤ hammingNorm z := by
  exact recognize_new_Z_lower Stage4.hx Stage4.hz Step3.fan Step3.clear Step3.clear_last
    Stage4.code Stage4.hx_eq Stage4.hz_eq hx.get hz.get
    Step3.e Step3.rx Step3.rz Step3.xcheck Step3.zcheck h
end Stage3

end QldpcVerification.Removal566
