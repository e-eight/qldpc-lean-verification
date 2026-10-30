import QldpcVerification.Boundary566Stage6
import QldpcVerification.Input.Removal566Step5Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage5
def code : CSSCode 573 275 280 :=
  recognize Stage6.hx Stage6.hz Step5.fan Step5.clear Step5.clear_last
    Stage6.code Stage6.hx_eq Stage6.hz_eq hx.get hz.get
    Step5.e Step5.rx Step5.rz Step5.xcheck Step5.zcheck
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : code =
    extension Stage6.code (indicator Step5.fan) (indicator Step5.clear)
      (by exact if_neg Step5.clear_last) Step5.e Step5.rx Step5.rz := by
  exact recognize_eq Stage6.hx Stage6.hz Step5.fan Step5.clear Step5.clear_last
    Stage6.code Stage6.hx_eq Stage6.hz_eq hx.get hz.get
    Step5.e Step5.rx Step5.rz Step5.xcheck Step5.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage6.code.xStab + 1 := by
  exact recognize_rankX Stage6.hx Stage6.hz Step5.fan Step5.clear Step5.clear_last
    Stage6.code Stage6.hx_eq Stage6.hz_eq hx.get hz.get
    Step5.e Step5.rx Step5.rz Step5.xcheck Step5.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage6.code.zStab  := by
  exact recognize_rankZ Stage6.hx Stage6.hz Step5.fan Step5.clear Step5.clear_last
    Stage6.code Stage6.hx_eq Stage6.hz_eq hx.get hz.get
    Step5.e Step5.rx Step5.rz Step5.xcheck Step5.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 275 :=
  step_rankX.trans (congrArg (fun r : ℕ => r + 1) Stage6.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  step_rankZ.trans (Stage6.rankZ)
theorem encoded_dimension : 573 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 573 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage6.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_new_X_lower Stage6.hx Stage6.hz Step5.fan Step5.clear Step5.clear_last
    Stage6.code Stage6.hx_eq Stage6.hz_eq hx.get hz.get
    Step5.e Step5.rx Step5.rz Step5.xcheck Step5.zcheck h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage6.code.IsZLogical z → D - 1 ≤ hammingNorm z := by
  exact recognize_new_Z_lower Stage6.hx Stage6.hz Step5.fan Step5.clear Step5.clear_last
    Stage6.code Stage6.hx_eq Stage6.hz_eq hx.get hz.get
    Step5.e Step5.rx Step5.rz Step5.xcheck Step5.zcheck h
end Stage5

end QldpcVerification.Removal566
