import QldpcVerification.Input.Removal566Stage8Data
import QldpcVerification.Input.Removal566Stage9Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step8
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 569) := ∅

def clear : Finset (Fin 278) := {⟨184, by decide⟩, ⟨187, by decide⟩, ⟨220, by decide⟩}

theorem clear_last : Fin.last 277 ∉ clear := by decide +kernel

def e := moveLast (⟨558, by decide⟩ : Fin 570)

def rx := moveLast (⟨211, by decide⟩ : Fin 278)

def rz := Equiv.refl (Fin 274)

theorem xcheck : ∀ i, Stage8.hz.get i =
    (normalX Stage9.hz fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage8.hx.get i =
    (normalZ Stage9.hx fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step8
