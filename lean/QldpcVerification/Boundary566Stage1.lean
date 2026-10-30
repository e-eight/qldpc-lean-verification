import QldpcVerification.Boundary566Stage2
import QldpcVerification.Input.Removal566Step1Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage1
def code : CSSCode 577 279 280 :=
  recognize Stage2.hx Stage2.hz Step1.fan Step1.clear Step1.clear_last
    Stage2.code Stage2.hx_eq Stage2.hz_eq hx.get hz.get
    Step1.e Step1.rx Step1.rz Step1.xcheck Step1.zcheck
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : code =
    extension Stage2.code (indicator Step1.fan) (indicator Step1.clear)
      (by exact if_neg Step1.clear_last) Step1.e Step1.rx Step1.rz := by
  exact recognize_eq Stage2.hx Stage2.hz Step1.fan Step1.clear Step1.clear_last
    Stage2.code Stage2.hx_eq Stage2.hz_eq hx.get hz.get
    Step1.e Step1.rx Step1.rz Step1.xcheck Step1.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage2.code.xStab + 1 := by
  exact recognize_rankX Stage2.hx Stage2.hz Step1.fan Step1.clear Step1.clear_last
    Stage2.code Stage2.hx_eq Stage2.hz_eq hx.get hz.get
    Step1.e Step1.rx Step1.rz Step1.xcheck Step1.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage2.code.zStab  := by
  exact recognize_rankZ Stage2.hx Stage2.hz Step1.fan Step1.clear Step1.clear_last
    Stage2.code Stage2.hx_eq Stage2.hz_eq hx.get hz.get
    Step1.e Step1.rx Step1.rz Step1.xcheck Step1.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 279 :=
  step_rankX.trans (congrArg (fun r : ℕ => r + 1) Stage2.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  step_rankZ.trans (Stage2.rankZ)
theorem encoded_dimension : 577 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 577 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage2.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_new_X_lower Stage2.hx Stage2.hz Step1.fan Step1.clear Step1.clear_last
    Stage2.code Stage2.hx_eq Stage2.hz_eq hx.get hz.get
    Step1.e Step1.rx Step1.rz Step1.xcheck Step1.zcheck h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage2.code.IsZLogical z → D - 1 ≤ hammingNorm z := by
  exact recognize_new_Z_lower Stage2.hx Stage2.hz Step1.fan Step1.clear Step1.clear_last
    Stage2.code Stage2.hx_eq Stage2.hz_eq hx.get hz.get
    Step1.e Step1.rx Step1.rz Step1.xcheck Step1.zcheck h
end Stage1

end QldpcVerification.Removal566
