import QldpcVerification.Boundary566Stage9
import QldpcVerification.Input.Removal566Step8Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage8
def code : CSSCode 570 274 278 :=
  dual (recognize Stage9.hz Stage9.hx Step8.fan Step8.clear Step8.clear_last
    (dual Stage9.code) Stage9.hz_eq Stage9.hx_eq hz.get hx.get
    Step8.e Step8.rx Step8.rz Step8.xcheck Step8.zcheck)
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : dual code =
    extension (dual Stage9.code) (indicator Step8.fan) (indicator Step8.clear)
      (by exact if_neg Step8.clear_last) Step8.e Step8.rx Step8.rz := by
  exact recognize_eq Stage9.hz Stage9.hx Step8.fan Step8.clear Step8.clear_last
    (dual Stage9.code) Stage9.hz_eq Stage9.hx_eq hz.get hx.get
    Step8.e Step8.rx Step8.rz Step8.xcheck Step8.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage9.code.xStab  := by
  exact recognize_rankZ Stage9.hz Stage9.hx Step8.fan Step8.clear Step8.clear_last
    (dual Stage9.code) Stage9.hz_eq Stage9.hx_eq hz.get hx.get
    Step8.e Step8.rx Step8.rz Step8.xcheck Step8.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage9.code.zStab + 1 := by
  exact recognize_rankX Stage9.hz Stage9.hx Step8.fan Step8.clear Step8.clear_last
    (dual Stage9.code) Stage9.hz_eq Stage9.hx_eq hz.get hx.get
    Step8.e Step8.rx Step8.rz Step8.xcheck Step8.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 274 :=
  step_rankX.trans (Stage9.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 278 :=
  step_rankZ.trans (congrArg (fun r : ℕ => r + 1) Stage9.rankZ)
theorem encoded_dimension : 570 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 570 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage9.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_zero_new_Z_lower Stage9.hz Stage9.hx Step8.fan Step8.clear Step8.clear_last
    (dual Stage9.code) Stage9.hz_eq Stage9.hx_eq hz.get hx.get
    Step8.e Step8.rx Step8.rz Step8.xcheck Step8.zcheck (by exact indicator_empty) h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage9.code.IsZLogical z → D ≤ hammingNorm z := by
  exact recognize_new_X_lower Stage9.hz Stage9.hx Step8.fan Step8.clear Step8.clear_last
    (dual Stage9.code) Stage9.hz_eq Stage9.hx_eq hz.get hx.get
    Step8.e Step8.rx Step8.rz Step8.xcheck Step8.zcheck h
end Stage8

end QldpcVerification.Removal566
