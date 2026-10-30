import QldpcVerification.Input.Removal566Stage5Data
import QldpcVerification.Input.Removal566Stage6Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step5
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 572) := {⟨226, by decide⟩, ⟨229, by decide⟩, ⟨262, by decide⟩, ⟨510, by decide⟩, ⟨527, by decide⟩, ⟨543, by decide⟩, ⟨563, by decide⟩}

def clear : Finset (Fin 275) := ∅

theorem clear_last : Fin.last 274 ∉ clear := by decide +kernel

def e := moveLast (⟨272, by decide⟩ : Fin 573)

def rx := moveLast (⟨182, by decide⟩ : Fin 275)

def rz := Equiv.refl (Fin 280)

theorem xcheck : ∀ i, Stage5.hx.get i =
    (normalX Stage6.hx fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage5.hz.get i =
    (normalZ Stage6.hz fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step5
