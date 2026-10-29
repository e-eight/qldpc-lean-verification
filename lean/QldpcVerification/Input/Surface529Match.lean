import QldpcVerification.RotatedSurface
import QldpcVerification.Input.Surface529Labels
import QldpcVerification.Input.Surface529Support
import QldpcVerification.Input.Surface529Lookup

/-! Generated recognition certificate. All finite facts are checked by the kernel. -/
namespace QldpcVerification.Surface529

open Matrix Quantum.Stabilizer.Lattice.RotatedSurface

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qubitEquiv : VtxIdx 23 ≃ Fin 529 :=
  (Equiv.prodCongr
    (show Fin 23 ≃ Fin 23 from
      { toFun := Fin.rev, invFun := Fin.rev,
        left_inv := Fin.rev_rev, right_inv := Fin.rev_rev })
    (Equiv.refl (Fin 23))).trans finProdFinEquiv

def xFace (i : Fin 264) : XFaceIdx 23 := xFaces.get i
def zFace (i : Fin 264) : ZFaceIdx 23 := zFaces.get i

def xPreimage : XFaceIdx 23 → Fin 264
  | .interior c => ⟨xInteriorRows.getD (c.val.2.val * (23 - 1) + c.val.1.val) 0 % 264,
      Nat.mod_lt _ (by decide)⟩
  | .topBdy k => ⟨xFirstRows.getD k.val 0 % 264, Nat.mod_lt _ (by decide)⟩
  | .bottomBdy k => ⟨xSecondRows.getD k.val 0 % 264, Nat.mod_lt _ (by decide)⟩

def zPreimage : ZFaceIdx 23 → Fin 264
  | .interior c => ⟨zInteriorRows.getD (c.val.2.val * (23 - 1) + c.val.1.val) 0 % 264,
      Nat.mod_lt _ (by decide)⟩
  | .leftBdy k => ⟨zFirstRows.getD k.val 0 % 264, Nat.mod_lt _ (by decide)⟩
  | .rightBdy k => ⟨zSecondRows.getD k.val 0 % 264, Nat.mod_lt _ (by decide)⟩

theorem x_right_inverse : ∀ f, xFace (xPreimage f) = f := by decide +kernel
theorem z_right_inverse : ∀ f, zFace (zPreimage f) = f := by decide +kernel

theorem x_surjective : Function.Surjective xFace := fun f => ⟨_, x_right_inverse f⟩

theorem z_surjective : Function.Surjective zFace :=
  fun f => ⟨_, z_right_inverse f⟩

theorem x_support_match : ∀ i : Fin 264,
    Input.Surface529.hxSupport.get i = (xSupport (xFace i)).image qubitEquiv := by
  decide +kernel

theorem z_support_match : ∀ i : Fin 264,
    Input.Surface529.hzSupport.get i = (zSupport (zFace i)).image qubitEquiv := by
  decide +kernel

def certificate : RotatedSurfaceMatch 23 529 264 264 where
  HX := fun i q => if q ∈ Input.Surface529.hxSupport.get i then 1 else 0
  HZ := fun i q => if q ∈ Input.Surface529.hzSupport.get i then 1 else 0
  qubits := qubitEquiv
  xFace := xFace
  zFace := zFace
  x_surjective := x_surjective
  z_surjective := z_surjective
  x_rows := by
    intro i
    funext v
    change (if qubitEquiv v ∈ Input.Surface529.hxSupport.get i then (1 : ZMod 2) else 0) =
      if v ∈ xSupport (xFace i) then 1 else 0
    rw [x_support_match i]
    simp
  z_rows := by
    intro i
    funext v
    change (if qubitEquiv v ∈ Input.Surface529.hzSupport.get i then (1 : ZMod 2) else 0) =
      if v ∈ zSupport (zFace i) then 1 else 0
    rw [z_support_match i]
    simp

end QldpcVerification.Surface529
