import QldpcVerification.Input.Removal566Stage7Data
import QldpcVerification.Input.Removal566Stage8Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step7
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 570) := ∅

def clear : Finset (Fin 279) := {⟨183, by decide⟩, ⟨186, by decide⟩, ⟨215, by decide⟩}

theorem clear_last : Fin.last 278 ∉ clear := by decide +kernel

def e := moveLast (⟨558, by decide⟩ : Fin 571)

def rx := moveLast (⟨206, by decide⟩ : Fin 279)

def rz := Equiv.refl (Fin 274)

theorem xcheck : ∀ i, Stage7.hz.get i =
    (normalX Stage8.hz fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage7.hx.get i =
    (normalZ Stage8.hx fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step7
