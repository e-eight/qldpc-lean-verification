import QldpcVerification.Input.Distance566Checks0
import QldpcVerification.Input.Distance566Checks1
import QldpcVerification.Input.Distance566Checks2

namespace QldpcVerification.Distance566.Checks
open Input.Sparse Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xKernel : ∀ i : Fin 18, kernelCheck Removal566.Stage12.hz (xMasks.get i) = true := by
  intro i
  fin_cases i
  · exact xKernel0
  · exact xKernel1
  · exact xKernel2
  · exact xKernel3
  · exact xKernel4
  · exact xKernel5
  · exact xKernel6
  · exact xKernel7
  · exact xKernel8
  · exact xKernel9
  · exact xKernel10
  · exact xKernel11
  · exact xKernel12
  · exact xKernel13
  · exact xKernel14
  · exact xKernel15
  · exact xKernel16
  · exact xKernel17

theorem zKernel : ∀ i : Fin 18, kernelCheck Removal566.Stage12.hx (zMasks.get i) = true := by
  intro i
  fin_cases i
  · exact zKernel0
  · exact zKernel1
  · exact zKernel2
  · exact zKernel3
  · exact zKernel4
  · exact zKernel5
  · exact zKernel6
  · exact zKernel7
  · exact zKernel8
  · exact zKernel9
  · exact zKernel10
  · exact zKernel11
  · exact zKernel12
  · exact zKernel13
  · exact zKernel14
  · exact zKernel15
  · exact zKernel16
  · exact zKernel17

theorem zVector : ∀ i : Fin 18, vectorCheck (zMasks.get i) (zSupports.get i) = true := by
  intro i
  fin_cases i
  · exact zVector0
  · exact zVector1
  · exact zVector2
  · exact zVector3
  · exact zVector4
  · exact zVector5
  · exact zVector6
  · exact zVector7
  · exact zVector8
  · exact zVector9
  · exact zVector10
  · exact zVector11
  · exact zVector12
  · exact zVector13
  · exact zVector14
  · exact zVector15
  · exact zVector16
  · exact zVector17

theorem paired : pairingCheck zSupports xMasks = true := by decide +kernel

theorem xWeight : (∑ q : Fin 566, if bit (xMasks.get ⟨0, by decide⟩) q then 1 else 0) = 20 := by decide +kernel

end QldpcVerification.Distance566.Checks
