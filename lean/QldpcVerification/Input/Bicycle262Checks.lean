import QldpcVerification.Input.SparseCertificates
import QldpcVerification.Input.Bicycle262Data

namespace QldpcVerification.Bicycle262Checks
open QldpcVerification.Input.Sparse
open QldpcVerification.Bicycle262Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem comm : commCheck hx hz = true := by decide +kernel

theorem xColumns : columnCheck hx px cx = true := by decide +kernel

theorem xPivots : pivotCheck tx cx = true := by decide +kernel

theorem xBaseVectors : ∀ i : Fin 2, vectorCheck (xBaseMasks.get i) (xBase.get i) = true := by decide +kernel

theorem xBaseKernel : ∀ i : Fin 2, kernelCheck hz (xBaseMasks.get i) = true := by decide +kernel

theorem xDualKernel : ∀ i : Fin 2, kernelCheck hz (xDual.get i) = true := by decide +kernel

theorem xPairing : pairingCheck zBase xDual = true := by decide +kernel

theorem xClass0 : familyCheck hz zBase (xBaseMasks.get ⟨0, by decide⟩) xFamily0 = true := by decide +kernel

theorem xCap0 : capCheck nq xFamily0 cap0 = true := by decide +kernel

theorem xClass1 : familyCheck hz zBase (xBaseMasks.get ⟨1, by decide⟩) xFamily1 = true := by decide +kernel

theorem xCap1 : capCheck nq xFamily1 cap1 = true := by decide +kernel

theorem wxKernel : kernelCheck hz wx = true := by decide +kernel

theorem wxWeight : (∑ q : Fin nq, if bit wx q then 1 else 0) = target := by decide +kernel

theorem wxPair : ∃ j : Fin 2, parity (zBase.get j) wx = true := by decide +kernel

theorem zColumns : columnCheck hz pz cz = true := by decide +kernel

theorem zPivots : pivotCheck tz cz = true := by decide +kernel

theorem zBaseVectors : ∀ i : Fin 2, vectorCheck (zBaseMasks.get i) (zBase.get i) = true := by decide +kernel

theorem zBaseKernel : ∀ i : Fin 2, kernelCheck hx (zBaseMasks.get i) = true := by decide +kernel

theorem zDualKernel : ∀ i : Fin 2, kernelCheck hx (zDual.get i) = true := by decide +kernel

theorem zPairing : pairingCheck xBase zDual = true := by decide +kernel

theorem zClass0 : familyCheck hx xBase (zBaseMasks.get ⟨0, by decide⟩) zFamily0 = true := by decide +kernel

theorem zCap0 : capCheck nq zFamily0 cap0 = true := by decide +kernel

theorem zClass1 : familyCheck hx xBase (zBaseMasks.get ⟨1, by decide⟩) zFamily1 = true := by decide +kernel

theorem zCap1 : capCheck nq zFamily1 cap1 = true := by decide +kernel

theorem wzKernel : kernelCheck hx wz = true := by decide +kernel

theorem wzWeight : (∑ q : Fin nq, if bit wz q then 1 else 0) = target := by decide +kernel

theorem wzPair : ∃ j : Fin 2, parity (xBase.get j) wz = true := by decide +kernel

theorem threshold0 : (target - 1) * cap0 < (zFamily0.map Prod.snd).sum := by decide +kernel

theorem threshold1 : (target - 1) * cap1 < (zFamily1.map Prod.snd).sum := by decide +kernel

end QldpcVerification.Bicycle262Checks
