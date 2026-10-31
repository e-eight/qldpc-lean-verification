import QldpcVerification.Input.Distance566PackingData
import QldpcVerification.Input.Distance566Data

namespace QldpcVerification.Distance566.PackingChecks
open Input.Sparse Distance566Certificates PackingData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xClass6 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨6, by decide⟩) (xReps.get ⟨6, by decide⟩) = true := by decide +kernel

theorem xCap6 : capCheck 566 (xFamily ⟨6, by decide⟩) (xCaps.get ⟨6, by decide⟩) = true := by decide +kernel

theorem xThreshold6 : (bound - 1) * (xCaps.get ⟨6, by decide⟩) < ((xFamily ⟨6, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass6 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨6, by decide⟩) (zReps.get ⟨6, by decide⟩) = true := by decide +kernel

theorem zCap6 : capCheck 566 (zFamily ⟨6, by decide⟩) (zCaps.get ⟨6, by decide⟩) = true := by decide +kernel

theorem zThreshold6 : (bound - 1) * (zCaps.get ⟨6, by decide⟩) < ((zFamily ⟨6, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass7 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨7, by decide⟩) (xReps.get ⟨7, by decide⟩) = true := by decide +kernel

theorem xCap7 : capCheck 566 (xFamily ⟨7, by decide⟩) (xCaps.get ⟨7, by decide⟩) = true := by decide +kernel

theorem xThreshold7 : (bound - 1) * (xCaps.get ⟨7, by decide⟩) < ((xFamily ⟨7, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass7 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨7, by decide⟩) (zReps.get ⟨7, by decide⟩) = true := by decide +kernel

theorem zCap7 : capCheck 566 (zFamily ⟨7, by decide⟩) (zCaps.get ⟨7, by decide⟩) = true := by decide +kernel

theorem zThreshold7 : (bound - 1) * (zCaps.get ⟨7, by decide⟩) < ((zFamily ⟨7, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass8 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨8, by decide⟩) (xReps.get ⟨8, by decide⟩) = true := by decide +kernel

theorem xCap8 : capCheck 566 (xFamily ⟨8, by decide⟩) (xCaps.get ⟨8, by decide⟩) = true := by decide +kernel

theorem xThreshold8 : (bound - 1) * (xCaps.get ⟨8, by decide⟩) < ((xFamily ⟨8, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass8 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨8, by decide⟩) (zReps.get ⟨8, by decide⟩) = true := by decide +kernel

theorem zCap8 : capCheck 566 (zFamily ⟨8, by decide⟩) (zCaps.get ⟨8, by decide⟩) = true := by decide +kernel

theorem zThreshold8 : (bound - 1) * (zCaps.get ⟨8, by decide⟩) < ((zFamily ⟨8, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass9 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨9, by decide⟩) (xReps.get ⟨9, by decide⟩) = true := by decide +kernel

theorem xCap9 : capCheck 566 (xFamily ⟨9, by decide⟩) (xCaps.get ⟨9, by decide⟩) = true := by decide +kernel

theorem xThreshold9 : (bound - 1) * (xCaps.get ⟨9, by decide⟩) < ((xFamily ⟨9, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass9 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨9, by decide⟩) (zReps.get ⟨9, by decide⟩) = true := by decide +kernel

theorem zCap9 : capCheck 566 (zFamily ⟨9, by decide⟩) (zCaps.get ⟨9, by decide⟩) = true := by decide +kernel

theorem zThreshold9 : (bound - 1) * (zCaps.get ⟨9, by decide⟩) < ((zFamily ⟨9, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass10 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨10, by decide⟩) (xReps.get ⟨10, by decide⟩) = true := by decide +kernel

theorem xCap10 : capCheck 566 (xFamily ⟨10, by decide⟩) (xCaps.get ⟨10, by decide⟩) = true := by decide +kernel

theorem xThreshold10 : (bound - 1) * (xCaps.get ⟨10, by decide⟩) < ((xFamily ⟨10, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass10 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨10, by decide⟩) (zReps.get ⟨10, by decide⟩) = true := by decide +kernel

theorem zCap10 : capCheck 566 (zFamily ⟨10, by decide⟩) (zCaps.get ⟨10, by decide⟩) = true := by decide +kernel

theorem zThreshold10 : (bound - 1) * (zCaps.get ⟨10, by decide⟩) < ((zFamily ⟨10, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem xClass11 : classCheck Removal566.Stage12.hx (Data.xMasks.get ⟨11, by decide⟩) (xReps.get ⟨11, by decide⟩) = true := by decide +kernel

theorem xCap11 : capCheck 566 (xFamily ⟨11, by decide⟩) (xCaps.get ⟨11, by decide⟩) = true := by decide +kernel

theorem xThreshold11 : (bound - 1) * (xCaps.get ⟨11, by decide⟩) < ((xFamily ⟨11, by decide⟩).map Prod.snd).sum := by decide +kernel

theorem zClass11 : classCheck Removal566.Stage12.hz (Data.zMasks.get ⟨11, by decide⟩) (zReps.get ⟨11, by decide⟩) = true := by decide +kernel

theorem zCap11 : capCheck 566 (zFamily ⟨11, by decide⟩) (zCaps.get ⟨11, by decide⟩) = true := by decide +kernel

theorem zThreshold11 : (bound - 1) * (zCaps.get ⟨11, by decide⟩) < ((zFamily ⟨11, by decide⟩).map Prod.snd).sum := by decide +kernel

end QldpcVerification.Distance566.PackingChecks
