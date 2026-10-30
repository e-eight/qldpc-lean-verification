import QldpcVerification.Input.BicycleRecognition
import QldpcVerification.Input.LogicalWitness
import QldpcVerification.Input.Bicycle100Data

namespace QldpcVerification.Bicycle100Model
open Matrix Module Input Input.Sparse Input.BicycleRecognition Bicycle Bicycle100Data
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def unitStep : (ZMod 50)ˣ where
  val := 1
  inv := 1
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def baseQubits : Normalized.Edge 50 ≃ Fin 100 := Normalized.qubits
def rowVertex : Fin 50 ≃ ZMod 50 := (ZMod.finEquiv 50).toEquiv
def xp (i : Fin 50) := hPoints unitStep 1 9 9 (rowVertex i)
def zp (i : Fin 50) := fPoints unitStep 1 9 9 (rowVertex i)

theorem x_supports : ∀ i : Fin 50, hx.get i = ((xp i).map baseQubits).toFinset := by
  decide +kernel
theorem z_supports : ∀ i : Fin 50, hz.get i = ((zp i).map baseQubits).toFinset := by
  decide +kernel
theorem x_distinct : ∀ i : Fin 50, ((xp i).map baseQubits).Nodup := by decide +kernel
theorem z_distinct : ∀ i : Fin 50, ((zp i).map baseQubits).Nodup := by decide +kernel

def matching : Bicycle.Match 50 9 100 50 50 :=
  matchBinomial unitStep 1 9 (matrix hx) (matrix hz) baseQubits
    rowVertex rowVertex rowVertex.surjective rowVertex.surjective
    (fun i => (row_of_points baseQubits (hx.get i) (xp i) (x_supports i) (x_distinct i)).trans
      (hPoints_sum unitStep 1 9 9 (rowVertex i)))
    (fun i => (row_of_points baseQubits (hz.get i) (zp i) (z_supports i) (z_distinct i)).trans
      (fPoints_sum unitStep 1 9 9 (rowVertex i)))

abbrev code := matching.code

theorem wx_kernel : kernelCheck hz wx = true := by decide +kernel
theorem wz_kernel : kernelCheck hx wz = true := by decide +kernel
theorem detx_kernel : kernelCheck hx detx = true := by decide +kernel
theorem detz_kernel : kernelCheck hz detz = true := by decide +kernel
theorem wx_pair : vec nq wx ⬝ᵥ vec nq detx = 1 := by decide +kernel
theorem wz_pair : vec nq wz ⬝ᵥ vec nq detz = 1 := by decide +kernel

theorem wx_logical : code.IsXLogical (vec nq wx) :=
  code.x_logical_of_pair _ _ (kernel_of_check hz wx wx_kernel)
    (kernel_of_check hx detx detx_kernel) wx_pair
theorem wz_logical : code.IsZLogical (vec nq wz) :=
  code.z_logical_of_pair _ _ (kernel_of_check hx wz wz_kernel)
    (kernel_of_check hz detz detz_kernel) wz_pair
theorem wx_weight : hammingNorm (vec nq wx) = 10 := by
  rw [weight_eq]
  decide +kernel
theorem wz_weight : hammingNorm (vec nq wz) = 10 := by
  rw [weight_eq]
  decide +kernel

end QldpcVerification.Bicycle100Model
