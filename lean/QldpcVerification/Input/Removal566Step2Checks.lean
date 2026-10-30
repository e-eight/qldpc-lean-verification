import QldpcVerification.Input.Removal566Stage2Data
import QldpcVerification.Input.Removal566Stage3Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step2
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 575) := {⟨223, by decide⟩, ⟨226, by decide⟩, ⟨259, by decide⟩, ⟨510, by decide⟩, ⟨527, by decide⟩, ⟨543, by decide⟩, ⟨563, by decide⟩}

def clear : Finset (Fin 278) := ∅

theorem clear_last : Fin.last 277 ∉ clear := by decide +kernel

def e := moveLast (⟨272, by decide⟩ : Fin 576)

def rx := moveLast (⟨182, by decide⟩ : Fin 278)

def rz := Equiv.refl (Fin 280)

theorem xcheck : ∀ i, Stage2.hx.get i =
    (normalX Stage3.hx fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage2.hz.get i =
    (normalZ Stage3.hz fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step2
