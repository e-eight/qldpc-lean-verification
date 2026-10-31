import QldpcVerification.Input.Distance566PackingData
import QldpcVerification.Input.Distance566Data

namespace QldpcVerification.Distance566.PackingChecks
open Input.Sparse Distance566Certificates PackingData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xClass12 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨12, by decide⟩) (xReps.get ⟨12, by decide⟩) = true := by decide +kernel

theorem xCap12 : capCheck 566 (xFamily ⟨12, by decide⟩) (xCaps.get ⟨12, by decide⟩) = true := by decide +kernel

theorem xThreshold12 : (bound - 1) * (xCaps.get ⟨12, by decide⟩) < ((xFamily ⟨12, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass12 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨12, by decide⟩) (zReps.get ⟨12, by decide⟩) = true := by decide +kernel

theorem zCap12 : capCheck 566 (zFamily ⟨12, by decide⟩) (zCaps.get ⟨12, by decide⟩) = true := by decide +kernel

theorem zThreshold12 : (bound - 1) * (zCaps.get ⟨12, by decide⟩) < ((zFamily ⟨12, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass13 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨13, by decide⟩) (xReps.get ⟨13, by decide⟩) = true := by decide +kernel

theorem xCap13 : capCheck 566 (xFamily ⟨13, by decide⟩) (xCaps.get ⟨13, by decide⟩) = true := by decide +kernel

theorem xThreshold13 : (bound - 1) * (xCaps.get ⟨13, by decide⟩) < ((xFamily ⟨13, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass13 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨13, by decide⟩) (zReps.get ⟨13, by decide⟩) = true := by decide +kernel

theorem zCap13 : capCheck 566 (zFamily ⟨13, by decide⟩) (zCaps.get ⟨13, by decide⟩) = true := by decide +kernel

theorem zThreshold13 : (bound - 1) * (zCaps.get ⟨13, by decide⟩) < ((zFamily ⟨13, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass14 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨14, by decide⟩) (xReps.get ⟨14, by decide⟩) = true := by decide +kernel

theorem xCap14 : capCheck 566 (xFamily ⟨14, by decide⟩) (xCaps.get ⟨14, by decide⟩) = true := by decide +kernel

theorem xThreshold14 : (bound - 1) * (xCaps.get ⟨14, by decide⟩) < ((xFamily ⟨14, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass14 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨14, by decide⟩) (zReps.get ⟨14, by decide⟩) = true := by decide +kernel

theorem zCap14 : capCheck 566 (zFamily ⟨14, by decide⟩) (zCaps.get ⟨14, by decide⟩) = true := by decide +kernel

theorem zThreshold14 : (bound - 1) * (zCaps.get ⟨14, by decide⟩) < ((zFamily ⟨14, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass15 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨15, by decide⟩) (xReps.get ⟨15, by decide⟩) = true := by decide +kernel

theorem xCap15 : capCheck 566 (xFamily ⟨15, by decide⟩) (xCaps.get ⟨15, by decide⟩) = true := by decide +kernel

theorem xThreshold15 : (bound - 1) * (xCaps.get ⟨15, by decide⟩) < ((xFamily ⟨15, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass15 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨15, by decide⟩) (zReps.get ⟨15, by decide⟩) = true := by decide +kernel

theorem zCap15 : capCheck 566 (zFamily ⟨15, by decide⟩) (zCaps.get ⟨15, by decide⟩) = true := by decide +kernel

theorem zThreshold15 : (bound - 1) * (zCaps.get ⟨15, by decide⟩) < ((zFamily ⟨15, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass16 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨16, by decide⟩) (xReps.get ⟨16, by decide⟩) = true := by decide +kernel

theorem xCap16 : capCheck 566 (xFamily ⟨16, by decide⟩) (xCaps.get ⟨16, by decide⟩) = true := by decide +kernel

theorem xThreshold16 : (bound - 1) * (xCaps.get ⟨16, by decide⟩) < ((xFamily ⟨16, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass16 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨16, by decide⟩) (zReps.get ⟨16, by decide⟩) = true := by decide +kernel

theorem zCap16 : capCheck 566 (zFamily ⟨16, by decide⟩) (zCaps.get ⟨16, by decide⟩) = true := by decide +kernel

theorem zThreshold16 : (bound - 1) * (zCaps.get ⟨16, by decide⟩) < ((zFamily ⟨16, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass17 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨17, by decide⟩) (xReps.get ⟨17, by decide⟩) = true := by decide +kernel

theorem xCap17 : capCheck 566 (xFamily ⟨17, by decide⟩) (xCaps.get ⟨17, by decide⟩) = true := by decide +kernel

theorem xThreshold17 : (bound - 1) * (xCaps.get ⟨17, by decide⟩) < ((xFamily ⟨17, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass17 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨17, by decide⟩) (zReps.get ⟨17, by decide⟩) = true := by decide +kernel

theorem zCap17 : capCheck 566 (zFamily ⟨17, by decide⟩) (zCaps.get ⟨17, by decide⟩) = true := by decide +kernel

theorem zThreshold17 : (bound - 1) * (zCaps.get ⟨17, by decide⟩) < ((zFamily ⟨17, by decide⟩).map Prod.snd).sum := by decide +kernel

end QldpcVerification.Distance566.PackingChecks
