import QldpcVerification.Input.BicycleRecognition
import QldpcVerification.Input.LogicalWitness
import QldpcVerification.Input.BicycleEven16FamilyData

namespace QldpcVerification.BicycleEven16FamilyModel
open Matrix Module Input Input.Sparse Input.BicycleRecognition Bicycle BicycleEven16FamilyData
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

def unitStep : (ZMod 8)ˣ where
  val := 7
  inv := 7
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def baseQubits : Normalized.Edge 8 ≃ Fin 16 := Normalized.qubits
def rowVertex : Fin 8 ≃ ZMod 8 := (ZMod.finEquiv 8).toEquiv
def xp (i : Fin 8) := hPoints unitStep 7 5 3 (rowVertex i)
def zp (i : Fin 8) := fPoints unitStep 7 5 3 (rowVertex i)

theorem x_supports : ∀ i : Fin 8, hx.get i = ((xp i).map baseQubits).toFinset := by
  decide +kernel
theorem z_supports : ∀ i : Fin 8, hz.get i = ((zp i).map baseQubits).toFinset := by
  decide +kernel
theorem x_distinct : ∀ i : Fin 8, ((xp i).map baseQubits).Nodup := by decide +kernel
theorem z_distinct : ∀ i : Fin 8, ((zp i).map baseQubits).Nodup := by decide +kernel

def matching : Bicycle.Match 8 3 16 8 8 :=
  matchBinomial unitStep 7 5 (matrix hx) (matrix hz) baseQubits
    rowVertex rowVertex rowVertex.surjective rowVertex.surjective
    (fun i => (row_of_points baseQubits (hx.get i) (xp i) (x_supports i) (x_distinct i)).trans
      (hPoints_sum unitStep 7 5 3 (rowVertex i)))
    (fun i => (row_of_points baseQubits (hz.get i) (zp i) (z_supports i) (z_distinct i)).trans
      (fPoints_sum unitStep 7 5 3 (rowVertex i)))

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
theorem wx_weight : hammingNorm (vec nq wx) = 4 := by
  rw [weight_eq]
  decide +kernel
theorem wz_weight : hammingNorm (vec nq wz) = 4 := by
  rw [weight_eq]
  decide +kernel

end QldpcVerification.BicycleEven16FamilyModel
