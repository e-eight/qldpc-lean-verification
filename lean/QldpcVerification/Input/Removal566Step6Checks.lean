import QldpcVerification.Input.Removal566Stage6Data
import QldpcVerification.Input.Removal566Stage7Data

/-! Generated sparse one-step recognition checks. Evaluated by the Lean kernel. -/
namespace QldpcVerification.Removal566.Step6
open Input Input.Sparse QubitRemovalSequence QubitRemovalTransport
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def fan : Finset (Fin 571) := ∅

def clear : Finset (Fin 280) := {⟨182, by decide⟩, ⟨185, by decide⟩, ⟨210, by decide⟩}

theorem clear_last : Fin.last 279 ∉ clear := by decide +kernel

def e := moveLast (⟨558, by decide⟩ : Fin 572)

def rx := moveLast (⟨201, by decide⟩ : Fin 280)

def rz := Equiv.refl (Fin 274)

theorem xcheck : ∀ i, Stage6.hz.get i =
    (normalX Stage7.hz fan clear (rx i)).map e.symm.toEmbedding := by
  decide +kernel

theorem zcheck : ∀ i, Stage6.hx.get i =
    (normalZ Stage7.hx fan (rz i)).map e.symm.toEmbedding := by
  decide +kernel

end QldpcVerification.Removal566.Step6
