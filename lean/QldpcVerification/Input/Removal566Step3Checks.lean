import QldpcVerification.Input.Removal566Stage3Data
import QldpcVerification.Input.Removal566Stage4Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step3
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 574) := {⟨224, by decide⟩, ⟨227, by decide⟩, ⟨260, by decide⟩, ⟨510, by decide⟩, ⟨527, by decide⟩, ⟨543, by decide⟩, ⟨563, by decide⟩}

def clear : Finset (Fin 277) := ∅

theorem clear_last : Fin.last 276 ∉ clear := by decide +kernel

def e := moveLast (⟨272, by decide⟩ : Fin 575)

def rx := moveLast (⟨182, by decide⟩ : Fin 277)

def rz := Equiv.refl (Fin 280)

theorem xcheck : ∀ i, Stage3.hx.get i =
    (normalX Stage4.hx fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage3.hz.get i =
    (normalZ Stage4.hz fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step3
