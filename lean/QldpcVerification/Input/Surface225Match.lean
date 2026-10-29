import QldpcVerification.Transport
import QldpcVerification.Input.Surface225Labels
import QldpcVerification.Input.Surface225Support

/-! Kernel-checked matching of the complete submitted supports to QECLean faces. -/
namespace QldpcVerification.Surface225
open Matrix Quantum.Stabilizer.Lattice.RotatedSurface
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def xRows : Matrix (XFaceIdx 15) (VtxIdx 15) (ZMod 2) :=
  fun f v => if v ∈ xSupport f then 1 else 0

def zRows : Matrix (ZFaceIdx 15) (VtxIdx 15) (ZMod 2) :=
  fun f v => if v ∈ zSupport f then 1 else 0

/-- Canonical vertex (x,y) maps to submitted index (14-x)*15+y. -/
def qubitEquiv : VtxIdx 15 ≃ Fin 225 :=
  (Equiv.prodCongr
    (show Fin 15 ≃ Fin 15 from
      { toFun := Fin.rev, invFun := Fin.rev,
        left_inv := Fin.rev_rev, right_inv := Fin.rev_rev })
    (Equiv.refl (Fin 15))).trans finProdFinEquiv

def xFace (i : Fin 112) : XFaceIdx 15 := xFaces.get i
def zFace (i : Fin 112) : ZFaceIdx 15 := zFaces.get i

theorem xFace_surjective : Function.Surjective xFace := by decide +kernel
theorem zFace_surjective : Function.Surjective zFace := by decide +kernel

/-- Every submitted row equals its labelled canonical support after rotation. -/
theorem x_support_match : ∀ i : Fin 112,
    QldpcVerification.Input.Surface225.hxSupport.get i = (xSupport (xFace i)).image qubitEquiv := by
  decide +kernel

theorem z_support_match : ∀ i : Fin 112,
    QldpcVerification.Input.Surface225.hzSupport.get i = (zSupport (zFace i)).image qubitEquiv := by
  decide +kernel

/-- Matrices from the original JSON supports, in their original row order. -/
def hx : Matrix (Fin 112) (Fin 225) (ZMod 2) :=
  fun i q => if q ∈ QldpcVerification.Input.Surface225.hxSupport.get i then 1 else 0

def hz : Matrix (Fin 112) (Fin 225) (ZMod 2) :=
  fun i q => if q ∈ QldpcVerification.Input.Surface225.hzSupport.get i then 1 else 0

theorem hx_pull (i : Fin 112) : pull qubitEquiv (hx i) = xRows (xFace i) := by
  funext v
  change (if qubitEquiv v ∈ QldpcVerification.Input.Surface225.hxSupport.get i then (1 : ZMod 2) else 0) =
    if v ∈ xSupport (xFace i) then 1 else 0
  rw [x_support_match i]
  simp

theorem hz_pull (i : Fin 112) : pull qubitEquiv (hz i) = zRows (zFace i) := by
  funext v
  change (if qubitEquiv v ∈ QldpcVerification.Input.Surface225.hzSupport.get i then (1 : ZMod 2) else 0) =
    if v ∈ zSupport (zFace i) then 1 else 0
  rw [z_support_match i]
  simp

end QldpcVerification.Surface225
