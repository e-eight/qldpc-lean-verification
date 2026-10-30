import QldpcVerification.Input.Removal566Stage11Data
import QldpcVerification.Input.Removal566Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step11
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 566) := ∅

def clear : Finset (Fin 275) := {⟨187, by decide⟩, ⟨190, by decide⟩, ⟨235, by decide⟩}

theorem clear_last : Fin.last 274 ∉ clear := by decide +kernel

def e := moveLast (⟨558, by decide⟩ : Fin 567)

def rx := moveLast (⟨226, by decide⟩ : Fin 275)

def rz := Equiv.refl (Fin 274)

theorem xcheck : ∀ i, Stage11.hz.get i =
    (normalX Stage12.hz fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage11.hx.get i =
    (normalZ Stage12.hx fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step11
