import QldpcVerification.Input.Distance566Data
import QldpcVerification.Input.Removal566Data

namespace QldpcVerification.Distance566.Checks
open Input.Sparse Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xKernel12 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨12, by decide⟩) = true := by decide +kernel

theorem zKernel12 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨12, by decide⟩) = true := by decide +kernel

theorem zVector12 : vectorCheck (zMasks.get ⟨12, by decide⟩) (zSupports.get ⟨12, by decide⟩) = true := by decide +kernel

theorem xKernel13 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨13, by decide⟩) = true := by decide +kernel

theorem zKernel13 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨13, by decide⟩) = true := by decide +kernel

theorem zVector13 : vectorCheck (zMasks.get ⟨13, by decide⟩) (zSupports.get ⟨13, by decide⟩) = true := by decide +kernel

theorem xKernel14 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨14, by decide⟩) = true := by decide +kernel

theorem zKernel14 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨14, by decide⟩) = true := by decide +kernel

theorem zVector14 : vectorCheck (zMasks.get ⟨14, by decide⟩) (zSupports.get ⟨14, by decide⟩) = true := by decide +kernel

theorem xKernel15 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨15, by decide⟩) = true := by decide +kernel

theorem zKernel15 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨15, by decide⟩) = true := by decide +kernel

theorem zVector15 : vectorCheck (zMasks.get ⟨15, by decide⟩) (zSupports.get ⟨15, by decide⟩) = true := by decide +kernel

theorem xKernel16 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨16, by decide⟩) = true := by decide +kernel

theorem zKernel16 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨16, by decide⟩) = true := by decide +kernel

theorem zVector16 : vectorCheck (zMasks.get ⟨16, by decide⟩) (zSupports.get ⟨16, by decide⟩) = true := by decide +kernel

theorem xKernel17 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨17, by decide⟩) = true := by decide +kernel

theorem zKernel17 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨17, by decide⟩) = true := by decide +kernel

theorem zVector17 : vectorCheck (zMasks.get ⟨17, by decide⟩) (zSupports.get ⟨17, by decide⟩) = true := by decide +kernel

end QldpcVerification.Distance566.Checks
