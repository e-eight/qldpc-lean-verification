import QldpcVerification.Input.Distance566Data
import QldpcVerification.Input.Removal566Data

namespace QldpcVerification.Distance566.Checks
open Input.Sparse Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xKernel6 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨6, by decide⟩) = true := by decide +kernel

theorem zKernel6 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨6, by decide⟩) = true := by decide +kernel

theorem zVector6 : vectorCheck (zMasks.get ⟨6, by decide⟩) (zSupports.get ⟨6, by decide⟩) = true := by decide +kernel

theorem xKernel7 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨7, by decide⟩) = true := by decide +kernel

theorem zKernel7 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨7, by decide⟩) = true := by decide +kernel

theorem zVector7 : vectorCheck (zMasks.get ⟨7, by decide⟩) (zSupports.get ⟨7, by decide⟩) = true := by decide +kernel

theorem xKernel8 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨8, by decide⟩) = true := by decide +kernel

theorem zKernel8 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨8, by decide⟩) = true := by decide +kernel

theorem zVector8 : vectorCheck (zMasks.get ⟨8, by decide⟩) (zSupports.get ⟨8, by decide⟩) = true := by decide +kernel

theorem xKernel9 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨9, by decide⟩) = true := by decide +kernel

theorem zKernel9 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨9, by decide⟩) = true := by decide +kernel

theorem zVector9 : vectorCheck (zMasks.get ⟨9, by decide⟩) (zSupports.get ⟨9, by decide⟩) = true := by decide +kernel

theorem xKernel10 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨10, by decide⟩) = true := by decide +kernel

theorem zKernel10 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨10, by decide⟩) = true := by decide +kernel

theorem zVector10 : vectorCheck (zMasks.get ⟨10, by decide⟩) (zSupports.get ⟨10, by decide⟩) = true := by decide +kernel

theorem xKernel11 : kernelCheck Removal566.Stage12.hz (xMasks.get ⟨11, by decide⟩) = true := by decide +kernel

theorem zKernel11 : kernelCheck Removal566.Stage12.hx (zMasks.get ⟨11, by decide⟩) = true := by decide +kernel

theorem zVector11 : vectorCheck (zMasks.get ⟨11, by decide⟩) (zSupports.get ⟨11, by decide⟩) = true := by decide +kernel

end QldpcVerification.Distance566.Checks
