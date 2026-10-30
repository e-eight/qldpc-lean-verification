import QldpcVerification.Boundary566Stage11
import QldpcVerification.Input.Removal566Step10Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage10
def code : CSSCode 568 274 276 :=
  dual (recognize Stage11.hz Stage11.hx Step10.fan Step10.clear Step10.clear_last
    (dual Stage11.code) Stage11.hz_eq Stage11.hx_eq hz.get hx.get
    Step10.e Step10.rx Step10.rz Step10.xcheck Step10.zcheck)
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : dual code =
    extension (dual Stage11.code) (indicator Step10.fan) (indicator Step10.clear)
      (by exact if_neg Step10.clear_last) Step10.e Step10.rx Step10.rz := by
  exact recognize_eq Stage11.hz Stage11.hx Step10.fan Step10.clear Step10.clear_last
    (dual Stage11.code) Stage11.hz_eq Stage11.hx_eq hz.get hx.get
    Step10.e Step10.rx Step10.rz Step10.xcheck Step10.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage11.code.xStab  := by
  exact recognize_rankZ Stage11.hz Stage11.hx Step10.fan Step10.clear Step10.clear_last
    (dual Stage11.code) Stage11.hz_eq Stage11.hx_eq hz.get hx.get
    Step10.e Step10.rx Step10.rz Step10.xcheck Step10.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage11.code.zStab + 1 := by
  exact recognize_rankX Stage11.hz Stage11.hx Step10.fan Step10.clear Step10.clear_last
    (dual Stage11.code) Stage11.hz_eq Stage11.hx_eq hz.get hx.get
    Step10.e Step10.rx Step10.rz Step10.xcheck Step10.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 274 :=
  step_rankX.trans (Stage11.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 276 :=
  step_rankZ.trans (congrArg (fun r : ℕ => r + 1) Stage11.rankZ)
theorem encoded_dimension : 568 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 568 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage11.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_zero_new_Z_lower Stage11.hz Stage11.hx Step10.fan Step10.clear Step10.clear_last
    (dual Stage11.code) Stage11.hz_eq Stage11.hx_eq hz.get hx.get
    Step10.e Step10.rx Step10.rz Step10.xcheck Step10.zcheck (by exact indicator_empty) h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage11.code.IsZLogical z → D ≤ hammingNorm z := by
  exact recognize_new_X_lower Stage11.hz Stage11.hx Step10.fan Step10.clear Step10.clear_last
    (dual Stage11.code) Stage11.hz_eq Stage11.hx_eq hz.get hx.get
    Step10.e Step10.rx Step10.rz Step10.xcheck Step10.zcheck h
end Stage10

end QldpcVerification.Removal566
