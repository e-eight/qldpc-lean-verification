import QldpcVerification.Boundary566Stage3
import QldpcVerification.Input.Removal566Step2Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage2
def code : CSSCode 576 278 280 :=
  recognize Stage3.hx Stage3.hz Step2.fan Step2.clear Step2.clear_last
    Stage3.code Stage3.hx_eq Stage3.hz_eq hx.get hz.get
    Step2.e Step2.rx Step2.rz Step2.xcheck Step2.zcheck
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : code =
    extension Stage3.code (indicator Step2.fan) (indicator Step2.clear)
      (by exact if_neg Step2.clear_last) Step2.e Step2.rx Step2.rz := by
  exact recognize_eq Stage3.hx Stage3.hz Step2.fan Step2.clear Step2.clear_last
    Stage3.code Stage3.hx_eq Stage3.hz_eq hx.get hz.get
    Step2.e Step2.rx Step2.rz Step2.xcheck Step2.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage3.code.xStab + 1 := by
  exact recognize_rankX Stage3.hx Stage3.hz Step2.fan Step2.clear Step2.clear_last
    Stage3.code Stage3.hx_eq Stage3.hz_eq hx.get hz.get
    Step2.e Step2.rx Step2.rz Step2.xcheck Step2.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage3.code.zStab  := by
  exact recognize_rankZ Stage3.hx Stage3.hz Step2.fan Step2.clear Step2.clear_last
    Stage3.code Stage3.hx_eq Stage3.hz_eq hx.get hz.get
    Step2.e Step2.rx Step2.rz Step2.xcheck Step2.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 278 :=
  step_rankX.trans (congrArg (fun r : ℕ => r + 1) Stage3.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  step_rankZ.trans (Stage3.rankZ)
theorem encoded_dimension : 576 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 576 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage3.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_new_X_lower Stage3.hx Stage3.hz Step2.fan Step2.clear Step2.clear_last
    Stage3.code Stage3.hx_eq Stage3.hz_eq hx.get hz.get
    Step2.e Step2.rx Step2.rz Step2.xcheck Step2.zcheck h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage3.code.IsZLogical z → D - 1 ≤ hammingNorm z := by
  exact recognize_new_Z_lower Stage3.hx Stage3.hz Step2.fan Step2.clear Step2.clear_last
    Stage3.code Stage3.hx_eq Stage3.hz_eq hx.get hz.get
    Step2.e Step2.rx Step2.rz Step2.xcheck Step2.zcheck h
end Stage2

end QldpcVerification.Removal566
