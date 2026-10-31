import QldpcVerification.Input.Distance566Data
import QldpcVerification.Input.Removal566Data

namespace QldpcVerification.Distance566.Checks
open Input.Sparse Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xKernel0 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨0, by decide⟩) = true := by decide +kernel

theorem zKernel0 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨0, by decide⟩) = true := by decide +kernel

theorem zVector0 : vectorCheck (zMasks.get ⟨0, by decide⟩) (zSupports.get ⟨0, by decide⟩) = true := by decide +kernel

theorem xKernel1 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨1, by decide⟩) = true := by decide +kernel

theorem zKernel1 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨1, by decide⟩) = true := by decide +kernel

theorem zVector1 : vectorCheck (zMasks.get ⟨1, by decide⟩) (zSupports.get ⟨1, by decide⟩) = true := by decide +kernel

theorem xKernel2 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨2, by decide⟩) = true := by decide +kernel

theorem zKernel2 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨2, by decide⟩) = true := by decide +kernel

theorem zVector2 : vectorCheck (zMasks.get ⟨2, by decide⟩) (zSupports.get ⟨2, by decide⟩) = true := by decide +kernel

theorem xKernel3 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨3, by decide⟩) = true := by decide +kernel

theorem zKernel3 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨3, by decide⟩) = true := by decide +kernel

theorem zVector3 : vectorCheck (zMasks.get ⟨3, by decide⟩) (zSupports.get ⟨3, by decide⟩) = true := by decide +kernel

theorem xKernel4 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨4, by decide⟩) = true := by decide +kernel

theorem zKernel4 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨4, by decide⟩) = true := by decide +kernel

theorem zVector4 : vectorCheck (zMasks.get ⟨4, by decide⟩) (zSupports.get ⟨4, by decide⟩) = true := by decide +kernel

theorem xKernel5 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨5, by decide⟩) = true := by decide +kernel

theorem zKernel5 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨5, by decide⟩) = true := by decide +kernel

theorem zVector5 : vectorCheck (zMasks.get ⟨5, by decide⟩) (zSupports.get ⟨5, by decide⟩) = true := by decide +kernel

end QldpcVerification.Distance566.Checks
