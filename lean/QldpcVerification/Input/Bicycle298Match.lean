import QldpcVerification.Input.BicycleRecognition
import QldpcVerification.Input.LogicalWitness
import QldpcVerification.Input.Bicycle298Data

namespace QldpcVerification.Bicycle298Model
open Matrix Module Input Input.Sparse Input.BicycleRecognition Bicycle Bicycle298Data
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def unitStep : (ZMod 149)ˣ where
  val := 148
  inv := 148
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def baseQubits : Normalized.Edge 149 ≃ Fin 298 := Normalized.qubits
def rowVertex : Fin 149 ≃ ZMod 149 := (ZMod.finEquiv 149).toEquiv
def xp (i : Fin 149) := hPoints unitStep 148 115 34 (rowVertex i)
def zp (i : Fin 149) := fPoints unitStep 148 115 34 (rowVertex i)

theorem x_supports : ∀ i : Fin 149, hx.get i = ((xp i).map baseQubits).toFinset := by
  decide +kernel
theorem z_supports : ∀ i : Fin 149, hz.get i = ((zp i).map baseQubits).toFinset := by
  decide +kernel
theorem x_distinct : ∀ i : Fin 149, ((xp i).map baseQubits).Nodup := by decide +kernel
theorem z_distinct : ∀ i : Fin 149, ((zp i).map baseQubits).Nodup := by decide +kernel

def matching : Bicycle.Match 149 34 298 149 149 :=
  matchBinomial unitStep 148 115 (matrix hx) (matrix hz) baseQubits
    rowVertex rowVertex rowVertex.surjective rowVertex.surjective
    (fun i => (row_of_points baseQubits (hx.get i) (xp i) (x_supports i) (x_distinct i)).trans
      (hPoints_sum unitStep 148 115 34 (rowVertex i)))
    (fun i => (row_of_points baseQubits (hz.get i) (zp i) (z_supports i) (z_distinct i)).trans
      (fPoints_sum unitStep 148 115 34 (rowVertex i)))

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
theorem wx_weight : hammingNorm (vec nq wx) = 17 := by
  rw [weight_eq]
  decide +kernel
theorem wz_weight : hammingNorm (vec nq wz) = 17 := by
  rw [weight_eq]
  decide +kernel

end QldpcVerification.Bicycle298Model
