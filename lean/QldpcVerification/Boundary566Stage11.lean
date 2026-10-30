import QldpcVerification.Boundary566Stage12
import QldpcVerification.Input.Removal566Step11Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage11
def code : CSSCode 567 274 275 :=
  dual (recognize Stage12.hz Stage12.hx Step11.fan Step11.clear Step11.clear_last
    (dual Stage12.code) Stage12.hz_eq Stage12.hx_eq hz.get hx.get
    Step11.e Step11.rx Step11.rz Step11.xcheck Step11.zcheck)
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : dual code =
    extension (dual Stage12.code) (indicator Step11.fan) (indicator Step11.clear)
      (by exact if_neg Step11.clear_last) Step11.e Step11.rx Step11.rz := by
  exact recognize_eq Stage12.hz Stage12.hx Step11.fan Step11.clear Step11.clear_last
    (dual Stage12.code) Stage12.hz_eq Stage12.hx_eq hz.get hx.get
    Step11.e Step11.rx Step11.rz Step11.xcheck Step11.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage12.code.xStab  := by
  exact recognize_rankZ Stage12.hz Stage12.hx Step11.fan Step11.clear Step11.clear_last
    (dual Stage12.code) Stage12.hz_eq Stage12.hx_eq hz.get hx.get
    Step11.e Step11.rx Step11.rz Step11.xcheck Step11.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage12.code.zStab + 1 := by
  exact recognize_rankX Stage12.hz Stage12.hx Step11.fan Step11.clear Step11.clear_last
    (dual Stage12.code) Stage12.hz_eq Stage12.hx_eq hz.get hx.get
    Step11.e Step11.rx Step11.rz Step11.xcheck Step11.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 274 :=
  step_rankX.trans (Stage12.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 275 :=
  step_rankZ.trans (congrArg (fun r : ℕ => r + 1) Stage12.rankZ)
theorem encoded_dimension : 567 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 567 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage12.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_zero_new_Z_lower Stage12.hz Stage12.hx Step11.fan Step11.clear Step11.clear_last
    (dual Stage12.code) Stage12.hz_eq Stage12.hx_eq hz.get hx.get
    Step11.e Step11.rx Step11.rz Step11.xcheck Step11.zcheck (by exact indicator_empty) h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage12.code.IsZLogical z → D ≤ hammingNorm z := by
  exact recognize_new_X_lower Stage12.hz Stage12.hx Step11.fan Step11.clear Step11.clear_last
    (dual Stage12.code) Stage12.hz_eq Stage12.hx_eq hz.get hx.get
    Step11.e Step11.rx Step11.rz Step11.xcheck Step11.zcheck h
end Stage11

end QldpcVerification.Removal566
