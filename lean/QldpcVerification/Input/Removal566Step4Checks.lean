import QldpcVerification.Input.Removal566Stage4Data
import QldpcVerification.Input.Removal566Stage5Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step4
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 573) := {⟨225, by decide⟩, ⟨228, by decide⟩, ⟨261, by decide⟩, ⟨510, by decide⟩, ⟨527, by decide⟩, ⟨543, by decide⟩, ⟨563, by decide⟩}

def clear : Finset (Fin 276) := ∅

theorem clear_last : Fin.last 275 ∉ clear := by decide +kernel

def e := moveLast (⟨272, by decide⟩ : Fin 574)

def rx := moveLast (⟨182, by decide⟩ : Fin 276)

def rz := Equiv.refl (Fin 280)

theorem xcheck : ∀ i, Stage4.hx.get i =
    (normalX Stage5.hx fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage4.hz.get i =
    (normalZ Stage5.hz fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step4
