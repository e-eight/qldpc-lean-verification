import QldpcVerification.Input.Distance566PackingChecks0
import QldpcVerification.Input.Distance566PackingChecks1
import QldpcVerification.Input.Distance566PackingChecks2

namespace QldpcVerification.Distance566.PackingChecks
open Input.Sparse Distance566Certificates PackingData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem xClass : ∀ a : Fin 18, classCheck Removal566.Stage12.hx (Data.xMasks.get a) (xReps.get a) = true := by
  intro a
  fin_cases a
  · exact xClass0
  · exact xClass1
  · exact xClass2
  · exact xClass3
  · exact xClass4
  · exact xClass5
  · exact xClass6
  · exact xClass7
  · exact xClass8
  · exact xClass9
  · exact xClass10
  · exact xClass11
  · exact xClass12
  · exact xClass13
  · exact xClass14
  · exact xClass15
  · exact xClass16
  · exact xClass17

theorem xCap : ∀ a : Fin 18, capCheck 566 (xFamily a) (xCaps.get a) = true := by
  intro a
  fin_cases a
  · exact xCap0
  · exact xCap1
  · exact xCap2
  · exact xCap3
  · exact xCap4
  · exact xCap5
  · exact xCap6
  · exact xCap7
  · exact xCap8
  · exact xCap9
  · exact xCap10
  · exact xCap11
  · exact xCap12
  · exact xCap13
  · exact xCap14
  · exact xCap15
  · exact xCap16
  · exact xCap17

theorem xThreshold : ∀ a : Fin 18, (bound - 1) * (xCaps.get a) < ((xFamily a).map Prod.snd).sum := by
  intro a
  fin_cases a
  · exact xThreshold0
  · exact xThreshold1
  · exact xThreshold2
  · exact xThreshold3
  · exact xThreshold4
  · exact xThreshold5
  · exact xThreshold6
  · exact xThreshold7
  · exact xThreshold8
  · exact xThreshold9
  · exact xThreshold10
  · exact xThreshold11
  · exact xThreshold12
  · exact xThreshold13
  · exact xThreshold14
  · exact xThreshold15
  · exact xThreshold16
  · exact xThreshold17

theorem zClass : ∀ a : Fin 18, classCheck Removal566.Stage12.hz (Data.zMasks.get a) (zReps.get a) = true := by
  intro a
  fin_cases a
  · exact zClass0
  · exact zClass1
  · exact zClass2
  · exact zClass3
  · exact zClass4
  · exact zClass5
  · exact zClass6
  · exact zClass7
  · exact zClass8
  · exact zClass9
  · exact zClass10
  · exact zClass11
  · exact zClass12
  · exact zClass13
  · exact zClass14
  · exact zClass15
  · exact zClass16
  · exact zClass17

theorem zCap : ∀ a : Fin 18, capCheck 566 (zFamily a) (zCaps.get a) = true := by
  intro a
  fin_cases a
  · exact zCap0
  · exact zCap1
  · exact zCap2
  · exact zCap3
  · exact zCap4
  · exact zCap5
  · exact zCap6
  · exact zCap7
  · exact zCap8
  · exact zCap9
  · exact zCap10
  · exact zCap11
  · exact zCap12
  · exact zCap13
  · exact zCap14
  · exact zCap15
  · exact zCap16
  · exact zCap17

theorem zThreshold : ∀ a : Fin 18, (bound - 1) * (zCaps.get a) < ((zFamily a).map Prod.snd).sum := by
  intro a
  fin_cases a
  · exact zThreshold0
  · exact zThreshold1
  · exact zThreshold2
  · exact zThreshold3
  · exact zThreshold4
  · exact zThreshold5
  · exact zThreshold6
  · exact zThreshold7
  · exact zThreshold8
  · exact zThreshold9
  · exact zThreshold10
  · exact zThreshold11
  · exact zThreshold12
  · exact zThreshold13
  · exact zThreshold14
  · exact zThreshold15
  · exact zThreshold16
  · exact zThreshold17

end QldpcVerification.Distance566.PackingChecks
