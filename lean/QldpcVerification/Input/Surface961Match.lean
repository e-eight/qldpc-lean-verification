import QldpcVerification.RotatedSurface
import QldpcVerification.Input.Surface961Labels
import QldpcVerification.Input.Surface961Support
import QldpcVerification.Input.Surface961Lookup

/-! Generated recognition certificate. All finite facts are checked by the kernel. -/
namespace QldpcVerification.Surface961

open Matrix Quantum.Stabilizer.Lattice.RotatedSurface

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def qubitEquiv : VtxIdx 31 ≃ Fin 961 :=
  (Equiv.prodCongr
    (show Fin 31 ≃ Fin 31 from
      { toFun := Fin.rev, invFun := Fin.rev,
        left_inv := Fin.rev_rev, right_inv := Fin.rev_rev })
    (Equiv.refl (Fin 31))).trans finProdFinEquiv

def xFace (i : Fin 480) : XFaceIdx 31 := xFaces.get i
def zFace (i : Fin 480) : ZFaceIdx 31 := zFaces.get i

def xPreimage : XFaceIdx 31 → Fin 480
  | .interior c => ⟨xInteriorRows.getD (c.val.2.val * (31 - 1) + c.val.1.val) 0 % 480,
      Nat.mod_lt _ (by decide)⟩
  | .topBdy k => ⟨xFirstRows.getD k.val 0 % 480, Nat.mod_lt _ (by decide)⟩
  | .bottomBdy k => ⟨xSecondRows.getD k.val 0 % 480, Nat.mod_lt _ (by decide)⟩

def zPreimage : ZFaceIdx 31 → Fin 480
  | .interior c => ⟨zInteriorRows.getD (c.val.2.val * (31 - 1) + c.val.1.val) 0 % 480,
      Nat.mod_lt _ (by decide)⟩
  | .leftBdy k => ⟨zFirstRows.getD k.val 0 % 480, Nat.mod_lt _ (by decide)⟩
  | .rightBdy k => ⟨zSecondRows.getD k.val 0 % 480, Nat.mod_lt _ (by decide)⟩

theorem x_right_inverse : ∀ f, xFace (xPreimage f) = f := by decide +kernel
theorem z_right_inverse : ∀ f, zFace (zPreimage f) = f := by decide +kernel

theorem x_surjective : Function.Surjective xFace := fun f => ⟨_, x_right_inverse f⟩

theorem z_surjective : Function.Surjective zFace :=
  fun f => ⟨_, z_right_inverse f⟩

theorem x_support_match : ∀ i : Fin 480,
    Input.Surface961.hxSupport.get i = (xSupport (xFace i)).image qubitEquiv := by
  decide +kernel

theorem z_support_match : ∀ i : Fin 480,
    Input.Surface961.hzSupport.get i = (zSupport (zFace i)).image qubitEquiv := by
  decide +kernel

def certificate : RotatedSurfaceMatch 31 961 480 480 where
  HX := fun i q => if q ∈ Input.Surface961.hxSupport.get i then 1 else 0
  HZ := fun i q => if q ∈ Input.Surface961.hzSupport.get i then 1 else 0
  qubits := qubitEquiv
  xFace := xFace
  zFace := zFace
  x_surjective := x_surjective
  z_surjective := z_surjective
  x_rows := by
    intro i
    funext v
    change (if qubitEquiv v ∈ Input.Surface961.hxSupport.get i then (1 : ZMod 2) else 0) =
      if v ∈ xSupport (xFace i) then 1 else 0
    rw [x_support_match i]
    simp
  z_rows := by
    intro i
    funext v
    change (if qubitEquiv v ∈ Input.Surface961.hzSupport.get i then (1 : ZMod 2) else 0) =
      if v ∈ zSupport (zFace i) then 1 else 0
    rw [z_support_match i]
    simp

end QldpcVerification.Surface961
