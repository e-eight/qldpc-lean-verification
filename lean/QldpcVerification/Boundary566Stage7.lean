import QldpcVerification.Boundary566Stage8
import QldpcVerification.Input.Removal566Step7Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage7
def code : CSSCode 571 274 279 :=
  dual (recognize Stage8.hz Stage8.hx Step7.fan Step7.clear Step7.clear_last
    (dual Stage8.code) Stage8.hz_eq Stage8.hx_eq hz.get hx.get
    Step7.e Step7.rx Step7.rz Step7.xcheck Step7.zcheck)
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : dual code =
    extension (dual Stage8.code) (indicator Step7.fan) (indicator Step7.clear)
      (by exact if_neg Step7.clear_last) Step7.e Step7.rx Step7.rz := by
  exact recognize_eq Stage8.hz Stage8.hx Step7.fan Step7.clear Step7.clear_last
    (dual Stage8.code) Stage8.hz_eq Stage8.hx_eq hz.get hx.get
    Step7.e Step7.rx Step7.rz Step7.xcheck Step7.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage8.code.xStab  := by
  exact recognize_rankZ Stage8.hz Stage8.hx Step7.fan Step7.clear Step7.clear_last
    (dual Stage8.code) Stage8.hz_eq Stage8.hx_eq hz.get hx.get
    Step7.e Step7.rx Step7.rz Step7.xcheck Step7.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage8.code.zStab + 1 := by
  exact recognize_rankX Stage8.hz Stage8.hx Step7.fan Step7.clear Step7.clear_last
    (dual Stage8.code) Stage8.hz_eq Stage8.hx_eq hz.get hx.get
    Step7.e Step7.rx Step7.rz Step7.xcheck Step7.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 274 :=
  step_rankX.trans (Stage8.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 279 :=
  step_rankZ.trans (congrArg (fun r : ℕ => r + 1) Stage8.rankZ)
theorem encoded_dimension : 571 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 571 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage8.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_zero_new_Z_lower Stage8.hz Stage8.hx Step7.fan Step7.clear Step7.clear_last
    (dual Stage8.code) Stage8.hz_eq Stage8.hx_eq hz.get hx.get
    Step7.e Step7.rx Step7.rz Step7.xcheck Step7.zcheck (by exact indicator_empty) h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage8.code.IsZLogical z → D ≤ hammingNorm z := by
  exact recognize_new_X_lower Stage8.hz Stage8.hx Step7.fan Step7.clear Step7.clear_last
    (dual Stage8.code) Stage8.hz_eq Stage8.hx_eq hz.get hx.get
    Step7.e Step7.rx Step7.rz Step7.xcheck Step7.zcheck h
end Stage7

end QldpcVerification.Removal566
