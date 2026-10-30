import QldpcVerification.Input.Removal566Stage9Data
import QldpcVerification.Input.Removal566Stage10Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step9
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 568) := ∅

def clear : Finset (Fin 277) := {⟨185, by decide⟩, ⟨188, by decide⟩, ⟨225, by decide⟩}

theorem clear_last : Fin.last 276 ∉ clear := by decide +kernel

def e := moveLast (⟨558, by decide⟩ : Fin 569)

def rx := moveLast (⟨216, by decide⟩ : Fin 277)

def rz := Equiv.refl (Fin 274)

theorem xcheck : ∀ i, Stage9.hz.get i =
    (normalX Stage10.hz fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage9.hx.get i =
    (normalZ Stage10.hx fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step9
