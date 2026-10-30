import QldpcVerification.Boundary566Stage7
import QldpcVerification.Input.Removal566Step6Checks

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage6
def code : CSSCode 572 274 280 :=
  dual (recognize Stage7.hz Stage7.hx Step6.fan Step6.clear Step6.clear_last
    (dual Stage7.code) Stage7.hz_eq Stage7.hx_eq hz.get hx.get
    Step6.e Step6.rx Step6.rz Step6.xcheck Step6.zcheck)
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem step_eq : dual code =
    extension (dual Stage7.code) (indicator Step6.fan) (indicator Step6.clear)
      (by exact if_neg Step6.clear_last) Step6.e Step6.rx Step6.rz := by
  exact recognize_eq Stage7.hz Stage7.hx Step6.fan Step6.clear Step6.clear_last
    (dual Stage7.code) Stage7.hz_eq Stage7.hx_eq hz.get hx.get
    Step6.e Step6.rx Step6.rz Step6.xcheck Step6.zcheck
theorem step_rankX : finrank (ZMod 2) code.xStab =
    finrank (ZMod 2) Stage7.code.xStab  := by
  exact recognize_rankZ Stage7.hz Stage7.hx Step6.fan Step6.clear Step6.clear_last
    (dual Stage7.code) Stage7.hz_eq Stage7.hx_eq hz.get hx.get
    Step6.e Step6.rx Step6.rz Step6.xcheck Step6.zcheck
theorem step_rankZ : finrank (ZMod 2) code.zStab =
    finrank (ZMod 2) Stage7.code.zStab + 1 := by
  exact recognize_rankX Stage7.hz Stage7.hx Step6.fan Step6.clear Step6.clear_last
    (dual Stage7.code) Stage7.hz_eq Stage7.hx_eq hz.get hx.get
    Step6.e Step6.rx Step6.rz Step6.xcheck Step6.zcheck
theorem rankX : finrank (ZMod 2) code.xStab = 274 :=
  step_rankX.trans (Stage7.rankX)
theorem rankZ : finrank (ZMod 2) code.zStab = 280 :=
  step_rankZ.trans (congrArg (fun r : ℕ => r + 1) Stage7.rankZ)
theorem encoded_dimension : 572 - finrank (ZMod 2) code.xStab -
    finrank (ZMod 2) code.zStab = 18 :=
  congrArg₂ (fun x z : ℕ => 572 - x - z) rankX rankZ
theorem lowerX {D : ℕ}
    (h : ∀ y, code.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, Stage7.code.IsXLogical x → D ≤ hammingNorm x := by
  exact recognize_zero_new_Z_lower Stage7.hz Stage7.hx Step6.fan Step6.clear Step6.clear_last
    (dual Stage7.code) Stage7.hz_eq Stage7.hx_eq hz.get hx.get
    Step6.e Step6.rx Step6.rz Step6.xcheck Step6.zcheck (by exact indicator_empty) h
theorem lowerZ {D : ℕ}
    (h : ∀ y, code.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, Stage7.code.IsZLogical z → D ≤ hammingNorm z := by
  exact recognize_new_X_lower Stage7.hz Stage7.hx Step6.fan Step6.clear Step6.clear_last
    (dual Stage7.code) Stage7.hz_eq Stage7.hx_eq hz.get hx.get
    Step6.e Step6.rx Step6.rz Step6.xcheck Step6.zcheck h
end Stage6

end QldpcVerification.Removal566
