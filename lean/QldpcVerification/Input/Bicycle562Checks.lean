import QldpcVerification.Input.SparseCertificates
import QldpcVerification.Input.Bicycle562Data

namespace QldpcVerification.Bicycle562Checks
open Input.Sparse Bicycle562Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xBlocksKernel : ∀ i : Fin 2, kernelCheck hz (blockMasks.get i) = true := by decide +kernel

theorem wxKernel : kernelCheck hz wx = true := by decide +kernel

theorem wxWeight : (∑ q : Fin nq, if bit wx q then 1 else 0) = 23 := by decide +kernel

theorem wxPair : ∃ j : Fin 2, parity (blocks.get j) wx = true := by decide +kernel

theorem zBlocksKernel : ∀ i : Fin 2, kernelCheck hx (blockMasks.get i) = true := by decide +kernel

theorem wzKernel : kernelCheck hx wz = true := by decide +kernel

theorem wzWeight : (∑ q : Fin nq, if bit wz q then 1 else 0) = 23 := by decide +kernel

theorem wzPair : ∃ j : Fin 2, parity (blocks.get j) wz = true := by decide +kernel

end QldpcVerification.Bicycle562Checks
