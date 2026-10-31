import QldpcVerification.Input.Distance566PackingData
import QldpcVerification.Input.Distance566Data

namespace QldpcVerification.Distance566.PackingChecks
open Input.Sparse Distance566Certificates PackingData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xClass0 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨0, by decide⟩) (xReps.get ⟨0, by decide⟩) = true := by decide +kernel

theorem xCap0 : capCheck 566 (xFamily ⟨0, by decide⟩) (xCaps.get ⟨0, by decide⟩) = true := by decide +kernel

theorem xThreshold0 : (bound - 1) * (xCaps.get ⟨0, by decide⟩) < ((xFamily ⟨0, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass0 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨0, by decide⟩) (zReps.get ⟨0, by decide⟩) = true := by decide +kernel

theorem zCap0 : capCheck 566 (zFamily ⟨0, by decide⟩) (zCaps.get ⟨0, by decide⟩) = true := by decide +kernel

theorem zThreshold0 : (bound - 1) * (zCaps.get ⟨0, by decide⟩) < ((zFamily ⟨0, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass1 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨1, by decide⟩) (xReps.get ⟨1, by decide⟩) = true := by decide +kernel

theorem xCap1 : capCheck 566 (xFamily ⟨1, by decide⟩) (xCaps.get ⟨1, by decide⟩) = true := by decide +kernel

theorem xThreshold1 : (bound - 1) * (xCaps.get ⟨1, by decide⟩) < ((xFamily ⟨1, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass1 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨1, by decide⟩) (zReps.get ⟨1, by decide⟩) = true := by decide +kernel

theorem zCap1 : capCheck 566 (zFamily ⟨1, by decide⟩) (zCaps.get ⟨1, by decide⟩) = true := by decide +kernel

theorem zThreshold1 : (bound - 1) * (zCaps.get ⟨1, by decide⟩) < ((zFamily ⟨1, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass2 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨2, by decide⟩) (xReps.get ⟨2, by decide⟩) = true := by decide +kernel

theorem xCap2 : capCheck 566 (xFamily ⟨2, by decide⟩) (xCaps.get ⟨2, by decide⟩) = true := by decide +kernel

theorem xThreshold2 : (bound - 1) * (xCaps.get ⟨2, by decide⟩) < ((xFamily ⟨2, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass2 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨2, by decide⟩) (zReps.get ⟨2, by decide⟩) = true := by decide +kernel

theorem zCap2 : capCheck 566 (zFamily ⟨2, by decide⟩) (zCaps.get ⟨2, by decide⟩) = true := by decide +kernel

theorem zThreshold2 : (bound - 1) * (zCaps.get ⟨2, by decide⟩) < ((zFamily ⟨2, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass3 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨3, by decide⟩) (xReps.get ⟨3, by decide⟩) = true := by decide +kernel

theorem xCap3 : capCheck 566 (xFamily ⟨3, by decide⟩) (xCaps.get ⟨3, by decide⟩) = true := by decide +kernel

theorem xThreshold3 : (bound - 1) * (xCaps.get ⟨3, by decide⟩) < ((xFamily ⟨3, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass3 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨3, by decide⟩) (zReps.get ⟨3, by decide⟩) = true := by decide +kernel

theorem zCap3 : capCheck 566 (zFamily ⟨3, by decide⟩) (zCaps.get ⟨3, by decide⟩) = true := by decide +kernel

theorem zThreshold3 : (bound - 1) * (zCaps.get ⟨3, by decide⟩) < ((zFamily ⟨3, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass4 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨4, by decide⟩) (xReps.get ⟨4, by decide⟩) = true := by decide +kernel

theorem xCap4 : capCheck 566 (xFamily ⟨4, by decide⟩) (xCaps.get ⟨4, by decide⟩) = true := by decide +kernel

theorem xThreshold4 : (bound - 1) * (xCaps.get ⟨4, by decide⟩) < ((xFamily ⟨4, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass4 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨4, by decide⟩) (zReps.get ⟨4, by decide⟩) = true := by decide +kernel

theorem zCap4 : capCheck 566 (zFamily ⟨4, by decide⟩) (zCaps.get ⟨4, by decide⟩) = true := by decide +kernel

theorem zThreshold4 : (bound - 1) * (zCaps.get ⟨4, by decide⟩) < ((zFamily ⟨4, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass5 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨5, by decide⟩) (xReps.get ⟨5, by decide⟩) = true := by decide +kernel

theorem xCap5 : capCheck 566 (xFamily ⟨5, by decide⟩) (xCaps.get ⟨5, by decide⟩) = true := by decide +kernel

theorem xThreshold5 : (bound - 1) * (xCaps.get ⟨5, by decide⟩) < ((xFamily ⟨5, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass5 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨5, by decide⟩) (zReps.get ⟨5, by decide⟩) = true := by decide +kernel

theorem zCap5 : capCheck 566 (zFamily ⟨5, by decide⟩) (zCaps.get ⟨5, by decide⟩) = true := by decide +kernel

theorem zThreshold5 : (bound - 1) * (zCaps.get ⟨5, by decide⟩) < ((zFamily ⟨5, by decide⟩).map Prod.snd).sum := by decide +kernel

end QldpcVerification.Distance566.PackingChecks
