import QldpcVerification.Input.Removal578Data
import QldpcVerification.Input.Removal566Stage1Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step0
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 577) := {⟨221, by decide⟩, ⟨224, by decide⟩, ⟨257, by decide⟩, ⟨510, by decide⟩, ⟨527, by decide⟩, ⟨543, by decide⟩, ⟨563, by decide⟩}

def clear : Finset (Fin 280) := ∅

theorem clear_last : Fin.last 279 ∉ clear := by decide +kernel

def e := moveLast (⟨272, by decide⟩ : Fin 578)

def rx := moveLast (⟨182, by decide⟩ : Fin 280)

def rz := Equiv.refl (Fin 280)

theorem xcheck : ∀ i, Stage0.hx.get i =
    (normalX Stage1.hx fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage0.hz.get i =
    (normalZ Stage1.hz fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step0
