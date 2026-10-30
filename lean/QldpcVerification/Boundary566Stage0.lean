import QldpcVerification.Boundary566Stage1
import QldpcVerification.Input.Removal566Step0Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage0
def code : CSSCode 578 280 280 :=
  recognize Stage1.hx Stage1.hz Step0.fan Step0.clear Step0.clear_last
    Stage1.code Stage1.hx_eq Stage1.hz_eq hx.get hz.get
    Step0.e Step0.rx Step0.rz Step0.xcheck Step0.zcheck
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : code =
    extension Stage1.code (indicator Step0.fan) (indicator Step0.clear)
      (by exact if_neg Step0.clear_last) Step0.e Step0.rx Step0.rz := by
  exact recognize_eq Stage1.hx Stage1.hz Step0.fan Step0.clear Step0.clear_last
    Stage1.code Stage1.hx_eq Stage1.hz_eq hx.get hz.get
    Step0.e Step0.rx Step0.rz Step0.xcheck Step0.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage1.code.xStab + 1 := by
  exact recognize_rankX Stage1.hx Stage1.hz Step0.fan Step0.clear Step0.clear_last
    Stage1.code Stage1.hx_eq Stage1.hz_eq hx.get hz.get
    Step0.e Step0.rx Step0.rz Step0.xcheck Step0.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage1.code.zStab  := by
  exact recognize_rankZ Stage1.hx Stage1.hz Step0.fan Step0.clear Step0.clear_last
    Stage1.code Stage1.hx_eq Stage1.hz_eq hx.get hz.get
    Step0.e Step0.rx Step0.rz Step0.xcheck Step0.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 280 :=
  step_rankX.trans (congrArg (fun r : ℕ => r + 1) Stage1.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  step_rankZ.trans (Stage1.rankZ)
theorem encoded_dimension : 578 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 578 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage1.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_new_X_lower Stage1.hx Stage1.hz Step0.fan Step0.clear Step0.clear_last
    Stage1.code Stage1.hx_eq Stage1.hz_eq hx.get hz.get
    Step0.e Step0.rx Step0.rz Step0.xcheck Step0.zcheck h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage1.code.IsZLogical z → D - 1 ≤ hammingNorm z := by
  exact recognize_new_Z_lower Stage1.hx Stage1.hz Step0.fan Step0.clear Step0.clear_last
    Stage1.code Stage1.hx_eq Stage1.hz_eq hx.get hz.get
    Step0.e Step0.rx Step0.rz Step0.xcheck Step0.zcheck h
end Stage0

end QldpcVerification.Removal566
