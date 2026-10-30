import QldpcVerification.Input.Removal566Stage10Data
import QldpcVerification.Input.Removal566Stage11Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step10
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 567) := ∅

def clear : Finset (Fin 276) := {⟨186, by decide⟩, ⟨189, by decide⟩, ⟨230, by decide⟩}

theorem clear_last : Fin.last 275 ∉ clear := by decide +kernel

def e := moveLast (⟨558, by decide⟩ : Fin 568)

def rx := moveLast (⟨221, by decide⟩ : Fin 276)

def rz := Equiv.refl (Fin 274)

theorem xcheck : ∀ i, Stage10.hz.get i =
    (normalX Stage11.hz fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage10.hx.get i =
    (normalZ Stage11.hx fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step10
