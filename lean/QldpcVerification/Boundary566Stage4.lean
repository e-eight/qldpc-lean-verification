import QldpcVerification.Boundary566Stage5
import QldpcVerification.Input.Removal566Step4Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage4
def code : CSSCode 574 276 280 :=
  recognize Stage5.hx Stage5.hz Step4.fan Step4.clear Step4.clear_last
    Stage5.code Stage5.hx_eq Stage5.hz_eq hx.get hz.get
    Step4.e Step4.rx Step4.rz Step4.xcheck Step4.zcheck
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : code =
    extension Stage5.code (indicator Step4.fan) (indicator Step4.clear)
      (by exact if_neg Step4.clear_last) Step4.e Step4.rx Step4.rz := by
  exact recognize_eq Stage5.hx Stage5.hz Step4.fan Step4.clear Step4.clear_last
    Stage5.code Stage5.hx_eq Stage5.hz_eq hx.get hz.get
    Step4.e Step4.rx Step4.rz Step4.xcheck Step4.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage5.code.xStab + 1 := by
  exact recognize_rankX Stage5.hx Stage5.hz Step4.fan Step4.clear Step4.clear_last
    Stage5.code Stage5.hx_eq Stage5.hz_eq hx.get hz.get
    Step4.e Step4.rx Step4.rz Step4.xcheck Step4.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage5.code.zStab  := by
  exact recognize_rankZ Stage5.hx Stage5.hz Step4.fan Step4.clear Step4.clear_last
    Stage5.code Stage5.hx_eq Stage5.hz_eq hx.get hz.get
    Step4.e Step4.rx Step4.rz Step4.xcheck Step4.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 276 :=
  step_rankX.trans (congrArg (fun r : ℕ => r + 1) Stage5.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  step_rankZ.trans (Stage5.rankZ)
theorem encoded_dimension : 574 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 574 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage5.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_new_X_lower Stage5.hx Stage5.hz Step4.fan Step4.clear Step4.clear_last
    Stage5.code Stage5.hx_eq Stage5.hz_eq hx.get hz.get
    Step4.e Step4.rx Step4.rz Step4.xcheck Step4.zcheck h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage5.code.IsZLogical z → D - 1 ≤ hammingNorm z := by
  exact recognize_new_Z_lower Stage5.hx Stage5.hz Step4.fan Step4.clear Step4.clear_last
    Stage5.code Stage5.hx_eq Stage5.hz_eq hx.get hz.get
    Step4.e Step4.rx Step4.rz Step4.xcheck Step4.zcheck h
end Stage4

end QldpcVerification.Removal566
