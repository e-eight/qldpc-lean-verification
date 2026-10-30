import QldpcVerification.Boundary566Stage10
import QldpcVerification.Input.Removal566Step9Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage9
def code : CSSCode 569 274 277 :=
  dual (recognize Stage10.hz Stage10.hx Step9.fan Step9.clear Step9.clear_last
    (dual Stage10.code) Stage10.hz_eq Stage10.hx_eq hz.get hx.get
    Step9.e Step9.rx Step9.rz Step9.xcheck Step9.zcheck)
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : dual code =
    extension (dual Stage10.code) (indicator Step9.fan) (indicator Step9.clear)
      (by exact if_neg Step9.clear_last) Step9.e Step9.rx Step9.rz := by
  exact recognize_eq Stage10.hz Stage10.hx Step9.fan Step9.clear Step9.clear_last
    (dual Stage10.code) Stage10.hz_eq Stage10.hx_eq hz.get hx.get
    Step9.e Step9.rx Step9.rz Step9.xcheck Step9.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage10.code.xStab  := by
  exact recognize_rankZ Stage10.hz Stage10.hx Step9.fan Step9.clear Step9.clear_last
    (dual Stage10.code) Stage10.hz_eq Stage10.hx_eq hz.get hx.get
    Step9.e Step9.rx Step9.rz Step9.xcheck Step9.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage10.code.zStab + 1 := by
  exact recognize_rankX Stage10.hz Stage10.hx Step9.fan Step9.clear Step9.clear_last
    (dual Stage10.code) Stage10.hz_eq Stage10.hx_eq hz.get hx.get
    Step9.e Step9.rx Step9.rz Step9.xcheck Step9.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 274 :=
  step_rankX.trans (Stage10.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 277 :=
  step_rankZ.trans (congrArg (fun r : ℕ => r + 1) Stage10.rankZ)
theorem encoded_dimension : 569 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 569 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage10.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_zero_new_Z_lower Stage10.hz Stage10.hx Step9.fan Step9.clear Step9.clear_last
    (dual Stage10.code) Stage10.hz_eq Stage10.hx_eq hz.get hx.get
    Step9.e Step9.rx Step9.rz Step9.xcheck Step9.zcheck (by exact indicator_empty) h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage10.code.IsZLogical z → D ≤ hammingNorm z := by
  exact recognize_new_X_lower Stage10.hz Stage10.hx Step9.fan Step9.clear Step9.clear_last
    (dual Stage10.code) Stage10.hz_eq Stage10.hx_eq hz.get hx.get
    Step9.e Step9.rx Step9.rz Step9.xcheck Step9.zcheck h
end Stage9

end QldpcVerification.Removal566
