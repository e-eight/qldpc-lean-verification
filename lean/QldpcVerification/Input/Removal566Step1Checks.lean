import QldpcVerification.Input.Removal566Stage1Data
import QldpcVerification.Input.Removal566Stage2Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step1
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 576) := {⟨222, by decide⟩, ⟨225, by decide⟩, ⟨258, by decide⟩, ⟨510, by decide⟩, ⟨527, by decide⟩, ⟨543, by decide⟩, ⟨563, by decide⟩}

def clear : Finset (Fin 279) := ∅

theorem clear_last : Fin.last 278 ∉ clear := by decide +kernel

def e := moveLast (⟨272, by decide⟩ : Fin 577)

def rx := moveLast (⟨182, by decide⟩ : Fin 279)

def rz := Equiv.refl (Fin 280)

theorem xcheck : ∀ i, Stage1.hx.get i =
    (normalX Stage2.hx fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage1.hz.get i =
    (normalZ Stage2.hz fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step1
